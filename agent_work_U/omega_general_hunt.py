"""Non-canonical Omega steps: start the walk at nodes (S (S(SS)) q').sigma for all small q', sigma (an Omega base with
second component q'); record whether the walk runs long, how many Omega steps with q' /= S(SS) it makes, and the L36
flag.  A long flag-0 walk would be a counterexample; a long walk with infinitely many non-canonical Omega steps would
be a new mechanism."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from stackview import hnf
from collections import Counter
SS = app(0, 0); S_SS = app(0, SS)
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def walk(u, nodes=300):
    noncanon = 0
    for j in range(nodes):
        if u == 0: return "S", noncanon
        q1, Z = L[u], R[u]
        if q1 == 0: u = Z; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        Hn = hnf(u, bud=max(5000, 20 * size(u)))
        if Hn is None: return "bot?", noncanon
        c = Hn[0]
        hq = hnf(q1, bud=20000)
        if hq and len(hq) == 2 and hq[0] == S_SS and hq[1] != S_SS and c == app(Z, app(hq[1], Z)): noncanon += 1
        u = c
        if size(u) > 100000: return "huge", noncanon
    return "long", noncanon
nmax = int(sys.argv[1])
small = [t for n in range(1, nmax + 1) for t in trees(n)]
stat = Counter(); t0 = time.time(); notes = []
for qp in small:
    Y = app(app(0, S_SS), qp)
    for sg in small:
        m = mark()
        u = app(Y, sg); c = cls(u)
        if MFl[c[1]] == 1:
            r, nc = walk(u)
            stat[(r, LFl[c[0]], min(nc, 3))] += 1
            if r in ("long", "huge") and (LFl[c[0]] == 0 or nc >= 3): notes.append((show(u), c, r, nc))
        truncate(m); clear_cache(m)
print(dict(stat), round(time.time() - t0), "s")
for n in notes[:10]: print(n)
