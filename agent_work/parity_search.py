"""Search for 1-hole contexts C such that the head run of C[N_n] J1 J2 J3 gets stuck with a J1- vs J2-headed front
depending on the parity of n (n = 1..NMAX).  Also reports any context whose outcome is non-constant and not monotone
(i.e. not 'threshold' behaviour), which would be data-dependent beyond a zero test."""
import sys, itertools, collections
import hm
HOLE = hm.atom("#")
J1, J2, J3 = hm.atom("J"), hm.atom("K"), hm.atom("L")
SS = hm.parse("SS")
def num(n):
    t = SS
    for _ in range(n - 1): t = hm.app(SS, t)
    return t
NUMS = {}
def subst(t, val, memo):
    if t == HOLE: return val
    if t <= 0: return t
    r = memo.get(t)
    if r is None:
        r = hm.app(subst(hm.L[t], val, memo), subst(hm.R[t], val, memo)); memo[t] = r
    return r
# contexts with exactly one hole, n leaves total
_ctx = {}
def contexts(n):
    if n in _ctx: return _ctx[n]
    out = []
    if n == 1: out = [HOLE]
    else:
        for k in range(1, n):
            for l in contexts(k):
                for r in hm.trees(n - k): out.append(hm.app(l, r))
            for l in hm.trees(k):
                for r in contexts(n - k): out.append(hm.app(l, r))
    _ctx[n] = out
    return out
def outcome(t, budget):
    args, h = hm.spine(t)
    if h != 0: return ("h", hm.show(h))
    st = list(reversed(args + [J1, J2, J3]))
    status, k = hm.run(st, budget)
    if status == "stuck":
        f = st[-1]
        return ("x", hm.show(hm.head(f)), len(st))
    return (status,)
if __name__ == "__main__":
    smax = int(sys.argv[1]); NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    budget = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    found = collections.Counter(); interesting = []
    for s in range(2, smax + 1):
        for C in contexts(s):
            outs = []
            for n in range(1, NMAX + 1):
                o = outcome(subst(C, num(n), {}), budget)
                outs.append(o[:2])
            heads = [o[1] if o[0] == "x" else o[0] for o in outs]
            key = tuple(heads)
            found[key] += 1
            # interesting: non-constant and not of the form a..a b..b (threshold)
            changes = sum(1 for i in range(1, len(heads)) if heads[i] != heads[i - 1])
            if changes >= 2:
                interesting.append((hm.show(C), heads))
    print("distinct outcome patterns:", len(found))
    for k, v in found.most_common(40): print(v, k)
    print("INTERESTING (>=2 changes):", len(interesting))
    for c, h in interesting[:50]: print(c, h)
