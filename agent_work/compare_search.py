"""2-hole contexts C[#1,#2]; fill with numerals N_a, N_b (a, b in 1..K) and run C[N_a,N_b] J K L.
Outcome = head atom of the stuck front (or 'budget').  Report contexts whose outcome table is NOT of the form
f(min(a, t1), min(b, t2)) with t1, t2 <= 2, i.e. depends on a and b beyond small thresholds (e.g. a < b)."""
import sys, itertools, collections
import hm
H1, H2 = hm.atom("#"), hm.atom("%")
J1, J2, J3 = hm.atom("J"), hm.atom("K"), hm.atom("L")
SS = hm.parse("SS")
NUM = {}
def num(n):
    if n in NUM: return NUM[n]
    t = SS
    for _ in range(n - 1): t = hm.app(SS, t)
    NUM[n] = t; return t
def subst2(t, x, y, memo):
    if t == H1: return x
    if t == H2: return y
    if t <= 0: return t
    r = memo.get(t)
    if r is None:
        r = hm.app(subst2(hm.L[t], x, y, memo), subst2(hm.R[t], x, y, memo)); memo[t] = r
    return r
_c2 = {}
def ctx2(n):
    """contexts with exactly one #1 and one #2, n leaves total (holes count as leaves)"""
    if n in _c2: return _c2[n]
    out = []
    import parity_search as ps
    # build from 1-hole contexts: split
    for k in range(1, n):
        # left has #1 only, right has #2 only, or vice versa; or one side has both
        for l in ctx1(k, H1):
            for r in ctx1(n - k, H2): out.append(hm.app(l, r))
        for l in ctx1(k, H2):
            for r in ctx1(n - k, H1): out.append(hm.app(l, r))
        for l in ctx2(k) if k < n and k >= 2 else []:
            for r in hm.trees(n - k): out.append(hm.app(l, r))
        for r in ctx2(n - k) if n - k >= 2 else []:
            for l in hm.trees(k): out.append(hm.app(l, r))
    _c2[n] = out
    return out
_c1 = {}
def ctx1(n, h):
    key = (n, h)
    if key in _c1: return _c1[key]
    out = []
    if n == 1: out = [h]
    else:
        for k in range(1, n):
            for l in ctx1(k, h):
                for r in hm.trees(n - k): out.append(hm.app(l, r))
            for l in hm.trees(k):
                for r in ctx1(n - k, h): out.append(hm.app(l, r))
    _c1[key] = out
    return out
def outcome(t, budget):
    a, h = hm.spine(t)
    if h != 0: return "?"
    st = list(reversed(a + [J1, J2, J3]))
    status, k = hm.run(st, budget)
    if status == "stuck": return hm.show(hm.head(st[-1]))
    return status
def thresholdable(tab, K):
    for t1 in range(1, 3):
        for t2 in range(1, 3):
            f = {}
            ok = True
            for a in range(1, K + 1):
                for b in range(1, K + 1):
                    key = (min(a, t1 + 1), min(b, t2 + 1))
                    if key in f and f[key] != tab[(a, b)]: ok = False; break
                    f[key] = tab[(a, b)]
                if not ok: break
            if ok: return True
    return False
if __name__ == "__main__":
    smax = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    budget = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
    for n in range(1, K + 1): num(n)
    cnt = collections.Counter(); hits = []
    for s in range(2, smax + 1):
        CS = ctx2(s); M0 = hm.mark()
        for C in CS:
            if hm.head(C) not in (0, H1, H2): continue
            tab = {}
            for a in range(1, K + 1):
                for b in range(1, K + 1):
                    tab[(a, b)] = outcome(subst2(C, num(a), num(b), {}), budget)
            cnt["total"] += 1
            hm.truncate(M0)
            if not thresholdable(tab, K):
                hits.append((hm.show(C), tab))
    print(cnt, "non-threshold:", len(hits))
    for c, tab in hits[:20]:
        print(c)
        for a in range(1, K + 1): print("   ", [tab[(a, b)] for b in range(1, K + 1)])
