"""agent_work_EM/periodic_hunt.py -- (J) evidence: an infinite leftmost walk with infinitely many jumps would most
simply be eventually PERIODIC (a node repeats, with a jump inside the cycle).  For every closed term with n leaves
(MODE all) or random gadget compositions (MODE rand), run the leftmost walk up to NODES nodes and report any repeated
node (hash-consed term ids), with the number of jumps inside the cycle.
usage: python periodic_hunt.py all n NODES | python periodic_hunt.py rand SEED NODES COUNT"""
import sys, time, random
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf, tree
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, mark, truncate, trees
from classes import cls, LFl, clear_cache
from collections import Counter
def walk(u, nodes):
    seen = {}; seq = []; kinds = []
    for j in range(nodes):
        if u == 0: return ("leaf", j, None)
        if u in seen:
            i = seen[u]
            return ("periodic", j, (i, j, sum(1 for k in kinds[i:j] if k == "jump")))
        seen[u] = j; seq.append(u)
        q, v = L[u], R[u]
        if q == 0: kinds.append("pop"); u = v; continue
        a = spine(q)[0]
        if len(a) == 1: kinds.append("jump"); u = a[0]; continue
        H = hnf(u, max(20000, 20 * size(u)))
        if H is None: return ("bot", j, None)
        kinds.append("step"); u = H[0]
        if size(u) > 100000: return ("big", j, None)
    return ("cap", nodes, None)
mode = sys.argv[1]
t0 = time.time(); res = Counter(); ex = []
if mode == "all":
    n, nodes = int(sys.argv[2]), int(sys.argv[3]); terms = trees(n)
else:
    random.seed(int(sys.argv[2])); nodes = int(sys.argv[3]); terms = None; cnt = int(sys.argv[4])
N = len(terms) if terms is not None else cnt
for i in range(N):
    m = mark()
    t = terms[i] if terms is not None else tree(random.randint(2, 7))
    st, j, info = walk(t, nodes)
    res[st] += 1
    if st == "periodic" and len(ex) < 10: ex.append((show(t)[:80], info, LFl[cls(t)[0]]))
    if terms is None: truncate(m); clear_cache(m)
print(mode, sys.argv[2:], "time", round(time.time() - t0, 1), dict(res))
print("periodic walks (term, (first index, repeat index, jumps in cycle), flag):", ex)
