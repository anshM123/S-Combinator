"""Random tree calls under the parallel head machine (main agent): same time as the head machine? Also counts how often
a waiting element (position >= 3) contains a redex at its root."""
import sys, random
sys.setrecursionlimit(1000000)
import hc
from parallel_eval import step_fn
def seq(As):
    t = hc.app(As[-1], 0)
    for A in reversed(As[:-1]): t = hc.app(hc.app(0, A), t)
    return hc.app(0, t)
def is_redex(e):
    args, h = hc.spine(e); return h == 0 and len(args) >= 3
def par_time(C, cap=100000):
    X, Y = -1, -2; XY = hc.app(X, Y); lst = [C, X, Y, -3, -4, -5, -6]; waiting_redex = 0
    for n in range(cap):
        if lst[0] == XY: return n, waiting_redex
        a, b, c, rest = lst[0], lst[1], lst[2], lst[3:]
        args, h = hc.spine(a)
        if h != 0: return None, waiting_redex
        waiting_redex += sum(1 for e in rest if e > 0 and is_redex(e))
        lst = args + [c, hc.app(b, c)] + [P(e) for e in rest]
    return None, waiting_redex
P = step_fn()   # one pass is a pure function of the node: one memo for the whole run
random.seed(3); pool = [(hc.app(0, 0), 2)]; same = diff = 0; wr_total = 0
for it in range(200):
    k = random.randint(2, 4); As = [random.choice(pool) for _ in range(k)]
    pred = sum(T for _, T in As) + k
    if pred > 4000: continue
    C = seq([a for a, _ in As]); n, wr = par_time(C); wr_total += wr
    if n == pred: same += 1
    else: diff += 1; print("differs:", n, pred)
    pool.append((C, pred))
    if (same + diff) % 10 == 0: print(f'  {same + diff} tested, {diff} differ', flush=True)
print(f"random tree calls: parallel time == head time in {same} cases, differs in {diff}; waiting root redexes seen: {wr_total}")
