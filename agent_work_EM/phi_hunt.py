"""agent_work_EM/phi_hunt.py -- (NT') evidence via the rightmost-walk description of a 'tower counter' (LOG 11:59):
a counter step at tower height m from code x needs the rightmost walk y_1 = snd H(x.(tw m)), y_(i+1) = snd H(y_i)
(every y_i with >= 2 arguments, snd H(y_i) /= S) to reach a node y_k = S x' S; then x' is the next code (height m+1).
This is a NECESSARY condition (the leftmost walk must also come back to y_1.(tw (m+1))).  For all closed x <= n leaves and
2 <= m <= M we compute Phi_m(x) and follow chains Phi_(m+1)(Phi_m(x)), ...; we report the longest chains.
usage: python phi_hunt.py n M STEPS"""
import sys, time
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, trees, mark, truncate
from collections import Counter
def tw(m):
    t = 0
    for _ in range(m): t = app(0, t)
    return t
def H2(t):
    a = spine(t)[0]
    if len(a) < 2: return None
    h = hnf(t, 20000)
    if h is None or len(h) != 2: return None
    return h
def phi(x, m, steps):
    h = H2(app(x, tw(m)))
    if h is None: return None
    y = h[1]
    for i in range(steps):
        a = spine(y)[0]
        if len(a) < 2: return None
        if len(a) == 2 and a[1] == 0: return a[0]          # y = S x' S
        hy = H2(y)
        if hy is None or hy[1] == 0: return None
        y = hy[1]
        if size(y) > 50000: return None
    return None
n, M, steps = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); res = Counter(); best = []
for k in range(1, n + 1):
    for x in trees(k):
        for m in range(2, M + 1):
            mk = mark()
            chain = [show(x)]; xx = x; mm = m
            while len(chain) < 8:
                nx = phi(xx, mm, steps)
                if nx is None: break
                chain.append(show(nx)[:40]); xx = nx; mm += 1
            res[len(chain) - 1] += 1
            if len(chain) > 1:
                best.append((len(chain) - 1, m, chain[:5])); best.sort(key=lambda b: -b[0]); best = best[:12]
            truncate(mk)
print("n", n, "M", M, "steps", steps, "time", round(time.time() - t0, 1))
print("number of consecutive counter steps (necessary condition) -> count:", dict(sorted(res.items())))
print("longest chains (steps, start height m, codes):", best)
