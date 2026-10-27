"""Which step types keep a leftmost walk INSIDE the component {(14,28),(14,26)}?  For every closed term with n leaves
in the component, walk the leftmost path (<= 300 nodes) and tally the steps whose source AND target are component
nodes: pop / jump / computed with k pushed multipliers (k = |ms child| - |ms bottom|), split into Fibonacci steps
(H(q1) = S S^(k) c0, child = w_k over the bottom) and others (refills)."""
import sys, time
from dm import *
from classes import cls, COMPONENT, clear_cache
from stackview import hnf
from collections import Counter
def Sk(k):
    x = 0
    for _ in range(k): x = app(0, x)
    return x
def msl(u):
    n = 0
    while u != 0: u = R[u]; n += 1
    return n
def walk(t, tally, ex, nodes=300):
    u = t
    for j in range(nodes):
        if u == 0: return "leaf"
        cu = cls(u); inC = cu in COMPONENT
        q1, Z = L[u], R[u]
        if q1 == 0: ty = "pop"; c = Z
        else:
            a = spine(q1)[0]
            if len(a) == 1: ty = "jump"; c = a[0]
            else:
                Hn = hnf(u, bud=max(5000, 20 * size(u)))
                if Hn is None: return "bot"
                c = Hn[0]
                k = msl(c) - msl(Z)
                hq = hnf(q1, bud=50000)
                fib = hq is not None and len(hq) == 2 and hq[0] == Sk(k)
                ty = ("fib%d" % k) if fib else ("ref%d" % k)
        if inC and cls(c) in COMPONENT:
            tally[ty] += 1
            if ty not in ex: ex[ty] = (show(t)[:80], j)
        u = c
        if size(u) > 100000: return "big"
    return "long"
n = int(sys.argv[1]); tally = Counter(); ex = {}; ends = Counter(); ncomp = 0; t0 = time.time()
for t in trees(n):
    m = mark()
    if cls(t) in COMPONENT:
        ncomp += 1
        ends[walk(t, tally, ex)] += 1
    truncate(m); clear_cache(m)
print(n, "leaves: component terms", ncomp, "walk ends", dict(ends), round(time.time() - t0), "s")
print("component->component step types:", sorted(tally.items(), key=lambda x: -x[1]))
for k, v in sorted(ex.items()): print("  ", k, "first example:", v)
