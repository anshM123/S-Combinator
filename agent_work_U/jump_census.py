"""How many jumps (node (S p).v -> p) can a leftmost walk make?  All closed terms <= n leaves (walks <= 200 nodes)."""
import sys
from dm import *
from classes import cls, LFl, clear_cache
from stackview import hnf
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def jumps(t, nodes=200):
    u = t; nj = 0
    for j in range(nodes):
        if u == 0: return nj, "S"
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: nj += 1; u = a[0]; continue
        H = hnf(u, bud=20000)
        if H is None: return nj, "bot"
        u = H[0]
    return nj, "long"
dist = Counter(); ex = {}
for n in range(1, int(sys.argv[1]) + 1):
    for t in trees(n):
        m = mark()
        nj, end = jumps(t)
        key = (nj, end); dist[key] += 1
        if key not in ex: ex[key] = show(t)
        truncate(m); clear_cache(m)
print(sorted(dist.items())); print({k: v for k, v in ex.items() if k[0] >= 3})
