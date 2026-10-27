"""Probe: standalone ReplaceAll runs of call processes A = S C x y (list [C, x, y]) for binary tree-call levels C = P_m and
small normal x, y.  Report the passes at which the front element (first spine argument) equals x.y, and whether the
run reaches a head normal form.  Direct passes (ptools.P)."""
import sys
from ptools import *
def fronts(t, N, target, cap=300000):
    hits = []; hnf_at = None
    for n in range(N):
        a, h = spine(t)
        if h != 0 or len(a) <= 2: hnf_at = n; break
        if a[0] == target: hits.append(n)
        if size(t) > cap: return hits, 'cap@%d' % n
        t = P(t)
    return hits, hnf_at
S = 0
cands = {'S': 0, 'SS': app(0, 0), 'S(SS)': app(0, app(0, 0)), 'SSS': app(0, 0, 0)}
for xn, x in cands.items():
    for yn, y in cands.items():
        row = []
        for m in range(4):
            C = level(2, m)
            hits, end = fronts(app(S, C, x, y), 400, hc.app(x, y))
            row.append((m, hits[:4], end))
        print(f"x={xn:6s} y={yn:6s}", row, flush=True)
