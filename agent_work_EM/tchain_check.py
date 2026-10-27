"""agent_work_EM/tchain_check.py -- computational cross-check of the case-(a') chain lemma (LOG 10:5x).
For every closed q <= n leaves, follow the typed chain q_0 = q, q_(k+1) = snd H(q_k) (x0_k = fst H(q_k) of type
T1-T4) and check: (a) a chain element followed by >= 2 more typed steps is never itself typed; (b) after the first element with >= 3 args every later
element has >= 3 args (ignoring the last 2 typed steps of a finite chain); (c) for consecutive >= 3-arg elements: x0_(k+1) = x0_k (R-step) or (x0_k = SS and
x0_(k+1) = S(SS)) or x0_(k+1) is T2; (d) every T4 term has the form S a S; (e) x0_k is the last argument of q_(k+1)."""
import sys, time
from tchain import *
def typed(x): return ttype(x) is not None
n, cap = int(sys.argv[1]), int(sys.argv[2])
bad = Counter(); stats = Counter(); t0 = time.time()
for m in range(2, n + 1):
    for q in trees(m):
        xs = []; qs = [q]
        for r in range(cap):
            if nargs(q) < 2: break
            h = hnf(q)
            if h is None: break
            x0, c0 = h
            if not typed(x0): break
            xs.append(x0); q = c0; qs.append(q)
            if size(q) > 5000: break
        K = len(xs)
        for k in range(K):
            if typed(qs[k]) and k + 2 < K: bad["a: chain element typed"] += 1
            if ttype(xs[k]) == "T4":
                a = spine(xs[k])[0]
                if not (len(a) == 2 and a[1] == 0): bad["d: T4 not S a S"] += 1
            if nargs(qs[k]) >= 3 and R[qs[k + 1]] != xs[k]: bad["e: last arg"] += 1
        first3 = next((k for k in range(K) if nargs(qs[k]) >= 3), None)
        if first3 is not None:
            for k in range(first3 + 1, K - 2):
                if nargs(qs[k]) < 3: bad["b: 2-arg after 3-arg"] += 1
            for k in range(first3, K - 3):
                a_, b_ = xs[k], xs[k + 1]
                if b_ == a_: stats["R"] += 1
                elif a_ == SS and b_ == S_SS: stats["SS->S(SS)"] += 1
                elif ttype(b_) == "T2": stats["->T2"] += 1
                else: bad["c: transition"] += 1
print("n", n, "time", round(time.time() - t0, 1), "violations:", dict(bad), "transitions:", dict(stats))
