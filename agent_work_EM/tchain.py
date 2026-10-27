"""agent_work_EM/tchain.py -- chains of depth-1 return steps (case (a') of Conjecture EM) in the RIGHTMOST view.
In a jump-free walk returning infinitely often to nodes q.S, the return multipliers satisfy q_(r+1) = snd H(q_r) and the
first component x0 = fst H(q_r) has type T1 (x0 = SS), T2 (H(x0) = S S y), T3 (x0 = S(SS)), T4 (x0 has >= 2 args and
H(x0.S) = S (SS) c1) [SA4.return_types_S].  For every closed q <= n leaves we follow this chain while it is typed
and report the longest chains and the ones with the most T3/T4 steps, with the 'kind' of each step:
  A  = q has exactly 2 args;  B0 = q = Q.z, z non-tower, R-step on Q;  B1 = restart z.(SS.z);  C = last arg a tower;
  X  = other (should not occur by the analysis in LOG 10:4x)."""
import sys, time
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, trees, mark, truncate
from collections import Counter
SS = app(0, 0); S_SS = app(0, SS)
def hnf(u, bud=4000):
    a, h = spine(u)
    st = list(reversed(a)); k = 0
    while len(st) > 2:
        x = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
        if k > bud: return None
    return list(reversed(st))
def nargs(t): return len(spine(t)[0])
def is_tower(t):
    while t != 0:
        if L[t] != 0: return False
        t = R[t]
    return True
def Rto(x):
    """y with H(x) = S S y, else None"""
    if nargs(x) < 2: return None
    h = hnf(x)
    if h is None or len(h) != 2 or h[0] != 0: return None
    return h[1]
def ttype(x0):
    if x0 == SS: return "T1"
    if x0 == S_SS: return "T3"
    if Rto(x0) is not None: return "T2"
    if nargs(x0) >= 2:
        h = hnf(app(x0, 0))
        if h is not None and len(h) == 2 and h[0] == SS: return "T4"
    return None
def kind(q):
    a = spine(q)[0]
    if len(a) == 2: return "A"
    z = R[q]; Q = L[q]
    if is_tower(z): return "C"
    hQ = hnf(Q)
    if hQ is None: return "X"
    if hQ[0] == 0: return "B0"
    if hQ[0] == SS and hQ[1] == SS: return "B1"
    return "X"
def chain(q, cap):
    out = []
    seen = set()
    for r in range(cap):
        if nargs(q) < 2: return out, "short"
        h = hnf(q)
        if h is None: return out, "nohnf"
        x0, c0 = h
        t = ttype(x0)
        if t is None: return out, "untyped"
        out.append((t, kind(q)))
        q = c0
        if size(q) > 5000: return out, "big"
    return out, "cap"
if __name__ == "__main__":
    n, cap = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    best = []; tot = Counter(); ends = Counter(); kinds = Counter(); capped = Counter()
    for m in range(2, n + 1):
        for q in trees(m):
            ch, why = chain(q, cap)
            ends[why] += 1
            n34 = sum(1 for t, k in ch if t in ("T3", "T4"))
            for t, k in ch: kinds[(t, k)] += 1
            if why == "cap":
                capped[(n34 > 0, tuple(sorted(Counter(t for t, k in ch[cap // 2:]).items())))] += 1
            best.append((n34, len(ch), show(q), why, "".join(t[1] + k for t, k in ch[:40])))
        best.sort(key=lambda x: (-x[0], -x[1])); best = best[:40]
    print("n", n, "cap", cap, "time", round(time.time() - t0, 1))
    print("chain end reasons:", dict(ends))
    print("(type, kind) counts over all chain steps:", dict(kinds))
    print("capped chains: (has T3/T4, type counts in 2nd half) ->", dict(capped))
    print("most T3/T4 steps (n34, len, q, end, steps as <type digit><kind>):")
    for b in best: print("  ", b)
