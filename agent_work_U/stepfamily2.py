"""SF evidence on a larger pool: all flag-1 terms among gadget trees of exactly n letters over {S, SS, S(SS), B, M}
whose leftmost walk runs 400 nodes; classify the steps after a burn-in of 100 nodes (TC / Om / other)."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from stackview import hnf
from collections import Counter
SS = app(0, 0); S_SS = app(0, SS)
alpha = [parse(v) for v in ["S", "SS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))"]]
def trees(n):
    if n == 1:
        for a in alpha: yield a
        return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def step_types(t, nodes=400, burn=100):
    u = t; ty = Counter()
    for j in range(nodes):
        if u == 0: return None
        q1, Z = L[u], R[u]
        if q1 == 0:
            if j >= burn: ty["pop"] += 1
            u = Z; continue
        a = spine(q1)[0]
        if len(a) == 1:
            if j >= burn: ty["jump"] += 1
            u = a[0]; continue
        Hn = hnf(u, bud=max(5000, 20 * size(u)))
        if Hn is None: return None
        c = Hn[0]
        if j >= burn:
            hq = hnf(q1, bud=50000)
            if hq and len(hq) == 2 and c == app(hq[1], Z): ty["TC"] += 1
            elif hq and len(hq) == 2 and hq[0] == S_SS and c == app(Z, app(hq[1], Z)):
                ty["Om" if hq[1] == S_SS else "Om-noncanon"] += 1
            else: ty["other"] += 1
        u = c
        if size(u) > 200000: return None
    return ty
n = int(sys.argv[1]); total = Counter(); nw = 0; others = []; t0 = time.time()
for t in trees(n):
    m = mark()
    c = cls(t)
    if LFl[c[0]] == 1:
        ty = step_types(t)
        if ty is not None:
            nw += 1; total.update(ty)
            if (ty["other"] or ty["pop"] or ty["jump"] or ty["Om-noncanon"]) and len(others) < 8: others.append((show(t)[:90], dict(ty)))
    truncate(m); clear_cache(m)
print(n, "letters: long flag-1 walks", nw, "step types after burn-in", dict(total), round(time.time() - t0), "s")
print("walks with other steps:", others)
