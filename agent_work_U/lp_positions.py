"""Where do large pushes occur in component walks?  For every component term <= n leaves: the indices (computed-step
numbers) of size-large pushes, and the gap between consecutive ones; plus whether the node at a large push is in the
component."""
import sys
from dm import *
from classes import cls, COMPONENT, MFl
from chainsrc import chain
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
pos = Counter(); gaps = Counter(); incomp = Counter(); total = 0; maxsteps = Counter()
for n in range(3, int(sys.argv[1]) + 1):
    for t in trees(n):
        if cls(t) not in COMPONENT: continue
        u = t; k = 0; last = None
        for j in range(200):
            if u == 0: break
            q1, v = L[u], R[u]
            if q1 == 0: u = v; continue
            a = spine(q1)[0]
            if len(a) == 1: u = a[0]; continue
            r = chain(q1, v)
            if r is None: break
            c, pushed = r
            if any(size(q) >= size(q1) for (q, s) in pushed) and MFl[cls(c)[1]] == 1:
                pos[k] += 1; incomp[cls(u) in COMPONENT] += 1
                if last is not None: gaps[k - last] += 1
                last = k
            k += 1; u = c
        maxsteps[k] += 0
print("computed-step index of large pushes:", sorted(pos.items()))
print("gaps between consecutive large pushes:", sorted(gaps.items()))
print("node at large push in component:", dict(incomp))
