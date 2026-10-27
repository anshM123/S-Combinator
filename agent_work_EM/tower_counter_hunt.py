"""agent_work_EM/tower_counter_hunt.py -- (NT') evidence: the only way NT' can fail is a 'unary tower counter' whose
consecutive strict cuts sit at nodes (S x S).(tw m), (S x' S).(tw (m+1)), ... (LOG 11:48, 11:51).  For every closed
x <= n leaves and m in [2, M], run the leftmost walk from (S x S).(tw m) for up to NODES nodes and record whether it
reaches a node (S y S).(tw (m+1)) at depth m+2 (one counter step).  Chains of such steps are followed.
usage: python tower_counter_hunt.py n M NODES"""
import sys, time
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf, depth
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, mark, truncate, trees
from collections import Counter
def tw(m):
    t = 0
    for _ in range(m): t = app(0, t)
    return t
def step(u):
    q, v = L[u], R[u]
    if q == 0: return v
    a = spine(q)[0]
    if len(a) == 1: return a[0]
    H = hnf(u, max(20000, 20 * size(u)))
    return None if H is None else H[0]
def counter_step(x, m, nodes):
    """walk from (S x S).(tw m); return y if a node (S y S).(tw (m+1)) is reached"""
    target_stack = tw(m + 1)
    u = app(app(app(0, x), 0), tw(m))
    for j in range(nodes):
        if u is None or u == 0: return None
        if R[u] == target_stack:
            q = L[u]
            a, h = spine(q)
            if h == 0 and len(a) == 2 and a[1] == 0: return a[0]
        u = step(u)
        if u is not None and size(u) > 100000: return None
    return None
n, M, nodes = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); res = Counter(); ex = []
for k in range(1, n + 1):
    for x in trees(k):
        for m in range(2, M + 1):
            y = counter_step(x, m, nodes)
            if y is None: res["no step"] += 1; continue
            res["one step"] += 1
            chain = [show(x)]; mm = m; yy = y
            for it in range(4):
                chain.append(show(yy)[:40])
                mm += 1
                yy = counter_step(yy, mm, nodes)
                if yy is None: break
            res["chain length %d" % len(chain)] += 1
            if len(ex) < 10: ex.append((m, chain))
print("n", n, "M", M, "nodes", nodes, "time", round(time.time() - t0, 1), dict(res))
print("counter steps found (m, chain of codes):", ex)
