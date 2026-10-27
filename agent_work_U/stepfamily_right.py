"""Rightmost-path step families: for R19 flag-1 terms (proved infinite rightmost path) among gadget trees and
self-applications, classify the rightmost steps after a burn-in: 'tail' (child t'.sigma, same stack), 'reload'
(child sigma.(SS.sigma)), 'short' (node with <= 2 arguments), 'other'."""
import sys
from dm import *
from classes import cls, clear_cache, load, BASE
from stackview import hnf
from collections import Counter
Rr, RF, RT = load(BASE + "model19_rightpath.txt")
RTl = RT.tolist(); RFl = RF.tolist(); sR = Rr.index("S")
_rc = {}
def rc(t):
    if t == 0: return sR
    r = _rc.get(t)
    if r is not None: return r
    st = [t]
    while st:
        x = st[-1]
        if x == 0 or x in _rc: st.pop(); continue
        pend = [y for y in (L[x], R[x]) if y != 0 and y not in _rc]
        if pend: st.extend(pend); continue
        a = sR if L[x] == 0 else _rc[L[x]]; b = sR if R[x] == 0 else _rc[R[x]]
        _rc[x] = RTl[a][b]; st.pop()
    return _rc[t]
SS = app(0, 0)
alpha = [parse(v) for v in ["S", "SS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))"]]
def trees_over(al, n):
    if n == 1:
        for a in al: yield a
        return
    for k in range(1, n):
        for l in trees_over(al, k):
            for r in trees_over(al, n - k): yield app(l, r)
def rsteps(t, nodes=300, burn=60):
    u = t; ty = Counter()
    for j in range(nodes):
        if u == 0: return None
        a = spine(u)[0]
        if len(a) <= 2:
            if j >= burn: ty["short"] += 1
            if not a: return None
            u = a[-1]; continue
        Hn = hnf(u, bud=max(5000, 20 * size(u)))
        if Hn is None: return None
        child = Hn[1]
        if j >= burn:
            t0, sg = L[u], R[u]
            if child == app(L[child], sg) and R[child] == sg: ty["tail"] += 1
            elif child == app(sg, app(SS, sg)): ty["reload"] += 1
            else: ty["other"] += 1
        u = child
        if size(u) > 200000: return None
    return ty
total = Counter(); nw = 0; others = []
pool = [t for n in range(1, 6) for t in trees_over(alpha, n)]
pool += [app(X, X) for n in range(7, 11) for X in trees_over([0], n)]
for t in pool:
    if RFl[rc(t)] != 1: continue
    ty = rsteps(t)
    if ty is None: continue
    nw += 1; total.update(ty)
    if (ty["other"] or ty["short"]) and len(others) < 6: others.append((show(t)[:80], dict(ty)))
print("R19 flag-1 walks:", nw, "rightmost step types after burn-in:", dict(total)); print("with other/short steps:", others)
