import sys
from nf_scan import hc, step_fn, reset, hnum
from parallel_eval import size
def ap(*xs):
    t = xs[0]
    for x in xs[1:]: t = hc.app(t, x)
    return t
def trace(t, cap=60):
    P = step_fn(); out = []
    for k in range(cap):
        u = P(t)
        if u == t: return k, out
        t = u; out.append((len(hc.L), size(t) if len(hc.L) < 300000 else -1))
    return None, out
N, M, K = map(int, sys.argv[1:4])
reset(); t = ap(hnum(N), ap(hnum(M), hnum(K), 0), 0)
k, out = trace(t, int(sys.argv[4]) if len(sys.argv) > 4 else 60)
print("n(mkS)S", N, M, K, "nf at", k, "nodes/sizes:", out[:40])
