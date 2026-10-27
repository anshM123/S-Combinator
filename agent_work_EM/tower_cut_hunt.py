"""agent_work_EM/tower_cut_hunt.py -- evidence for (NT): in a deep jump-free walk some strict cut has a non-tower stack.
NT can only fail if the frozen limit stack is all S, i.e. strict cuts sit at nodes (S x S).(tw (d-1)) (LOG 11:4x).
We start walks at such nodes, u = S x S (tw m), for all closed x <= n leaves and m <= M, and at q.(tw m) for all
closed q <= n leaves, and record walks that run NODES nodes and whether their depth grows while the stack stays a tower
(tower-scenario signature: the minimal depth over the second half increases but every node there has a tower stack
below depth min).  usage: python tower_cut_hunt.py n M NODES"""
import sys, time
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf, depth, walk
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, mark, truncate, trees
from classes import cls, LFl, clear_cache
from collections import Counter
def tw(m):
    t = 0
    for _ in range(m): t = app(0, t)
    return t
def is_tower(t):
    while t != 0:
        if L[t] != 0: return False
        t = R[t]
    return True
def run(u, nodes):
    ds = []; stacks_tower = []
    for j in range(nodes):
        if u == 0: return None
        q, v = L[u], R[u]
        ds.append(depth(u)); stacks_tower.append(is_tower(v))
        if q == 0: u = v; continue
        a = spine(q)[0]
        if len(a) == 1: u = a[0]; continue
        H = hnf(u, max(20000, 20 * size(u)))
        if H is None: return None
        u = H[0]
        if size(u) > 200000: return None
    return ds, stacks_tower
n, M, nodes = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); res = Counter(); ex = []
for k in range(1, n + 1):
    for x in trees(k):
        for m in range(1, M + 1):
            for u0 in (app(app(app(0, x), 0), tw(m)), app(x, tw(m))):
                mk = mark()
                r = run(u0, nodes)
                if r is None: res["ends"] += 1
                else:
                    ds, st = r
                    h = nodes // 2
                    deep = min(ds[h:]) > min(ds[h // 2:h]) + 1
                    # strict cuts in the second half: times whose depth is below all later depths
                    cuts = [j for j in range(h, nodes - 1) if ds[j] < min(ds[j + 1:])]
                    tower_cuts = sum(1 for j in cuts if st[j])
                    key = ("deep" if deep else "bounded", "tower-cuts" if cuts and tower_cuts == len(cuts) else "ok")
                    res[key] += 1
                    if key[1] == "tower-cuts" and len(ex) < 8:
                        ex.append((show(u0)[:80], LFl[cls(u0)[0]], len(cuts)))
                truncate(mk); clear_cache(mk)
print("n", n, "M", M, "nodes", nodes, "time", round(time.time() - t0, 1))
print("results:", dict(res))
print("walks whose second-half strict cuts all sit on tower stacks (term, flag, #cuts):", ex)
