"""Higher-order recurrence test and ratio-drift fit for parallel sizes (main agent)."""
import sys, math, time
sys.setrecursionlimit(1000000)
from fractions import Fraction
from symb import parse
import hc


memo_size = {}
def size(t):
    if t <= 0: return 1
    s = memo_size.get(t)
    if s is None: s = size(hc.L[t]) + size(hc.R[t]); memo_size[t] = s
    return s
def step(t, memo):
    if t <= 0: return t
    r = memo.get(t)
    if r is not None: return r
    f, z = hc.L[t], hc.R[t]
    if f > 0 and hc.L[f] > 0 and hc.L[hc.L[f]] == 0:
        x, y = hc.R[hc.L[f]], hc.R[f]; r = hc.app(hc.app(x, z), hc.app(y, z))
    else: r = hc.app(step(f, memo), step(z, memo))
    memo[t] = r; return r
src, N, KMAX = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
t = hc.from_tuple(parse(src)); s = [size(t)]; t0 = time.time()
for n in range(N):
    t = step(t, {}); s.append(size(t))
print(f"{src}: {len(s)} sizes in {time.time() - t0:.0f}s; DAG nodes {len(hc.L)}")
from size_recurrence import solve
def fit(s, KMAX):
    for k in range(1, KMAX + 1):
        n0 = len(s) - 2 * k - 8
        if n0 < k: break
        rows = [[Fraction(s[n - i]) for i in range(1, k + 1)] + [Fraction(1)] for n in range(n0, n0 + k + 1)]
        c = solve(rows, [Fraction(s[n]) for n in range(n0, n0 + k + 1)])
        if c is None: continue
        if all(sum(c[i - 1] * s[n - i] for i in range(1, k + 1)) + c[k] == s[n] for n in range(n0, len(s))):
            return k, n0, c
    return None
r = fit(s, KMAX)
print("  recurrence:", "none up to order %d (tested on the tail)" % KMAX if r is None else f"order {r[0]}: {[str(x) for x in r[2]]}")
rat = [s[i + 1] / s[i] for i in range(len(s) - 1)]
for n in (40, 60, 80, 100, 120, 140, 160, 180):
    if n < len(rat): print(f"  n={n}: ratio {rat[n]:.6f}  n*(ratio_n/ratio_(n-1) - 1) = {n * (rat[n] / rat[n - 1] - 1):.4f}")
