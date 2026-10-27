"""Targeted case-(a') probe: T3-counters.  q_k = (SS^k Y0).S(SS) counts down by T3 steps (H(q_k) = S (S(SS)) q_(k-1),
each followed by one pop).  For every closed base Y0 with <= n leaves and k <= 3, walk the leftmost path of q_k . S
and report walks that run NODES nodes (a reload-type T3 mechanism would show up), with their step types after
burn-in and their L36 flag."""
import sys, time
from dm import *
from classes import cls, LFl, clear_cache
from stackview import hnf
from collections import Counter
SS = app(0, 0); S_SS = app(0, SS)
def walk(t, nodes, burn):
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
        Hn = hnf(u, bud=max(20000, 20 * size(u)))
        if Hn is None: return None
        if j >= burn: ty["return" if Hn[0] == Z else "push"] += 1
        u = Hn[0]
        if size(u) > 300000: return None
    return ty
n, nodes, burn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); long_ = []; tot = 0
for leaves in range(1, n + 1):
    for Y0 in trees(leaves):
        for k in range(0, 4):
            m = mark()
            Y = Y0
            for _ in range(k): Y = app(SS, Y)
            t = app(app(Y, S_SS), 0)
            tot += 1
            ty = walk(t, nodes, burn)
            if ty is not None:
                long_.append((show(t)[:100], dict(ty), LFl[cls(t)[0]]))
            truncate(m); clear_cache(m)
print("bases <=", n, "leaves, k <= 3:", tot, "terms;", len(long_), "walks ran", nodes, "nodes;", round(time.time() - t0), "s")
for x in long_[:15]: print("  ", x)
