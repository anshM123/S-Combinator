"""Large pushes (a pushed multiplier at least as large as the popped one) in component walks, counting only steps whose
child has an hnf (M35 class != 33).  Reports the distribution of the number of large pushes per walk and the class
signatures (node class, q1 class, v class, chain length) of large pushes."""
import sys
from dm import *
from classes import cls, COMPONENT, MFl
from stackview import hnf
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def large_pushes(t, maxn=100):
    u = t; lp = []
    for j in range(maxn):
        if u == 0: return lp, "leaf"
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        H = hnf(u)
        if H is None: return lp, "bot"
        c = H[0]; pushed = []; x = c
        while x != v and x != 0:
            pushed.append(L[x]); x = R[x]
        if MFl[cls(c)[1]] == 1 and any(size(p) >= size(q1) for p in pushed):
            lp.append((cls(u), cls(q1), cls(v), len(pushed), size(q1), tuple(size(p) for p in pushed)))
        u = c
    return lp, "long"
if __name__ == "__main__":
    dist = Counter(); sig = Counter(); ex = {}
    for n in range(3, int(sys.argv[1]) + 1):
        for t in trees(n):
            if cls(t) not in COMPONENT: continue
            lp, end = large_pushes(t)
            dist[(len(lp), end)] += 1
            for e in lp:
                key = e[:4]; sig[key] += 1
                if key not in ex: ex[key] = show(t)
    print(sorted(dist.items())); print(len(sig), "signatures")
    for k, v in sig.most_common(25): print(v, k, ex[k])
