"""Maximal length of FINITE leftmost Böhm-tree paths, by term size (exact head reduction with generous budgets;
paths reaching depth 400 are treated as infinite and excluded)."""
import sys
from symb import trees, hnf, size, show
for n in range(3, int(sys.argv[1]) + 1):
    best = (-1, None); cnt_inf = 0
    for t in trees(n):
        u = t; d = 0; ended = False
        while d < 400:
            r = hnf(u, 4 * size(u) + 200)
            if r[0] != "hnf" or not r[1]: ended = True; break     # no hnf (within budget) or leaf S
            u = r[1][0]; d += 1
            if size(u) > 20000: break
        if ended:
            if d > best[0]: best = (d, show(t))
        else: cnt_inf += 1
    print(f"n={n:2d} max finite leftmost path length {best[0]:3d} (2n={2*n})  at {best[1]}   [infinite/unknown: {cnt_inf}]", flush=True)
