"""Multiset test: in each walk step the popped top multiplier q1 is replaced by the pushed multipliers q_0..q_{k-1}
(chain), by nothing (pop), or by the right-spine multipliers of p0 (jump, all subterms of q1).  If every pushed
multiplier were smaller than q1, the multiset of multiplier sizes would decrease (Dershowitz-Manna) and the walk would
be finite.  Count violations in component walks, and in reload/Omega walks."""
import sys
from dm import *
from classes import cls, COMPONENT
from stackview import hnf
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def walk_viol(t, maxn=80):
    u = t; viol = []; steps = 0
    for j in range(maxn):
        if u == 0: return viol, "leaf", steps
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        H = hnf(u)
        if H is None: return viol, "bot", steps
        c = H[0]; pushed = []; x = c
        while x != v and x != 0:
            pushed.append(L[x]); x = R[x]
        if x != v: return viol, "?", steps
        steps += 1
        big = [p for p in pushed if size(p) >= size(q1)]
        if big: viol.append((size(q1), [size(p) for p in pushed], cls(u)))
        u = c
    return viol, "long", steps
if __name__ == "__main__":
    tot = Counter(); ex = []
    for n in range(3, int(sys.argv[1]) + 1):
        for t in trees(n):
            if cls(t) not in COMPONENT: continue
            viol, end, st = walk_viol(t)
            tot[(len(viol) > 0, end)] += 1
            if viol and len(ex) < 12: ex.append((show(t), viol[:3]))
    print(tot); print(ex)
    for s in ["S(S(SS))(S(SS))(SS)S", "S(S(SS))(S(SS))(S(S(SS))(S(SS)))"]:
        viol, end, st = walk_viol(parse(s), 40); print(s, end, st, "violations:", len(viol), viol[:4])
