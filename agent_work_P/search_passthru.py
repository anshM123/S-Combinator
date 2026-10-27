"""Search: contexts A_m = S C_m u v w (C_m = binary tree-call level m, u,v,w small S-terms) whose standalone ReplaceAll run
reaches a head normal form of the pass-through shape S S c (spine [S, c]) for m = 0..3, with the hnf time growing in m.
Prints the candidates with their times (parallel and leftmost-outermost)."""
import sys, itertools
from ptools import *
sys.setrecursionlimit(100000)
def terms(n, memo={}):
    if n in memo: return memo[n]
    if n == 1: r = [0]
    else:
        r = []
        for k in range(1, n):
            for a in terms(k):
                for b in terms(n - k): r.append(hc.app(a, b))
    memo[n] = r; return r
small = [t for n in range(1, 4) for t in terms(n)]
def hnf_time(t, cap, mode, maxsize=20000):
    for n in range(cap):
        a, h = spine(t)
        if h != 0 or len(a) <= 2: return n, t
        if size(t) > maxsize: return None, t
        t = P(t) if mode == 'par' else head_step(t)
    return None, t
levels = [level(2, m) for m in range(4)]
found = 0
for u in small:
    for v in small:
        for w in small + [None]:
            res = []
            ok = True
            for m, C in enumerate(levels):
                A = app(0, C, u, v) if w is None else app(0, C, u, v, w)
                n, z = hnf_time(A, 400, 'par')
                if n is None: ok = False; break
                a, h = spine(z)
                if not (h == 0 and len(a) == 2 and a[0] == 0): ok = False; break
                nl, zl = hnf_time(A, 4000, 'lo', 200000)
                res.append((n, nl))
            if ok:
                found += 1
                print('u', show(u), 'v', show(v), 'w', show(w) if w is not None else '-', 'times (par, lo):', res, flush=True)
print('found', found)
