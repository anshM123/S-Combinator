"""Generalized restart shapes: every infinite Scenario-A walk passes through return multipliers of the form
w.(c.w) infinitely often (R-steps alone are finite).  Hunt: t = (w.(c.w)).Z for all closed w, c <= n leaves and small
fuels Z; walk <= 400 nodes; report long walks with their L36 flags (flag 0 + long = candidate counterexample)."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def walk(u, nodes=400):
    for j in range(nodes):
        if u == 0: return "S", j
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        st = list(reversed(spine(u)[0])); k = 0; bud = max(3000, 20 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", j
        u = st[-1]
        if size(u) > 100000: return "huge", j
    return "long", nodes
nmax = int(sys.argv[1])
small = [t for n in range(1, nmax + 1) for t in trees(n)]
Zs = [parse(z) for z in ["S", "SS", "S(SS)", "SSS"]]
stat = Counter(); t0 = time.time()
for w in small:
    for c in small:
        for Z in Zs:
            m = mark()
            t = app(app(w, app(c, w)), Z); cl = cls(t)
            if MFl[cl[1]] == 1:
                r, j = walk(t)
                stat[(r, LFl[cl[0]])] += 1
                if r in ("long", "huge") and LFl[cl[0]] == 0: print("CANDIDATE", show(t), cl, flush=True)
            truncate(m); clear_cache(m)
print(len(small), "terms per slot;", dict(stat), round(time.time() - t0), "s")
