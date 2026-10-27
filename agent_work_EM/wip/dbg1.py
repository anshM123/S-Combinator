import sys
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from tchain import *
def typed(x): return ttype(x) is not None
shown = 0
for m in range(2, 10):
    for q in trees(m):
        xs = []; qs = [q]
        for r in range(50):
            if nargs(q) < 2: break
            h = hnf(q)
            if h is None: break
            x0, c0 = h
            if not typed(x0): break
            xs.append(x0); q = c0; qs.append(q)
        for k in range(len(xs)):
            if typed(qs[k]) and shown < 6:
                shown += 1
                print("q_k =", show(qs[k]), "type", ttype(qs[k]), "x0 =", show(xs[k]), ttype(xs[k]), "next", show(qs[k+1]), "chain", [show(x) for x in qs[:k+2]])
