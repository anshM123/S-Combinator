"""Shape of the parallel evolution (main agent): per pass, the head spine length and the sizes of the head's arguments."""
import sys
sys.setrecursionlimit(1000000)
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
src, N = sys.argv[1], int(sys.argv[2])
t = hc.from_tuple(parse(src))
for n in range(N + 1):
    args, h = hc.spine(t)
    print(f"pass {n:3d}: size {size(t):>14d}  spine {len(args):3d}  arg sizes {[size(a) for a in args][:10]}")
    t = step(t, {})
