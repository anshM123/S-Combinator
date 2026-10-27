"""Step types along long leftmost walks (after a burn-in of 50 nodes): for node q.Z with q having >= 2 arguments and
H(q) = S p q':  'TC' if the child is q'.Z (one push: p = SS, or a refill-final head over Z = S), 'Om' if p = S(SS) and
the child is Z.(q'.Z), 'pop'/'jump' for short nodes, else 'other'.  Collect over all flag-1 long walks found by the
hunts (self-applications X X, S X X with X <= 11 leaves; gadget trees <= 4 letters)."""
import sys
from dm import *
from classes import cls, LFl, clear_cache
from stackview import hnf
from collections import Counter
SS = app(0, 0); S_SS = app(0, SS)
ALPHA = ["S", "SS", "SSS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))", "SS(SS)", "S(SSS)"]
def trees_over(alpha, n):
    if n == 1:
        for a in alpha: yield a
        return
    for k in range(1, n):
        for l in trees_over(alpha, k):
            for r in trees_over(alpha, n - k): yield app(l, r)
def step_types(t, nodes=400, burn=50):
    u = t; ty = Counter()
    for j in range(nodes):
        if u == 0: return None
        q1, Z = L[u], R[u]
        if q1 == 0:
            if j >= burn: ty["pop"] += 1
            u = Z; continue
        a = spine(q1)[0]
        if len(a) == 1:
            if j >= burn: ty["jump"] += 1
            u = a[0]; continue
        Hn = hnf(u, bud=50000)
        if Hn is None: return None
        c = Hn[0]
        if j >= burn:
            hq = hnf(q1, bud=50000)
            if c == app(L[c], Z) and L[c] == (hq[1] if hq and len(hq) == 2 else -1): ty["TC"] += 1
            elif hq and len(hq) == 2 and hq[0] == S_SS and c == app(Z, app(hq[1], Z)): ty["Om"] += 1
            else: ty["other"] += 1
        u = c
    return ty
total = Counter(); nwalks = 0; others = []
cands = []
for n in range(7, 12):
    for X in trees_over([0], n):
        cands += [app(X, X), app(app(0, X), X)]
alpha = [parse(v) for v in ALPHA]
for n in range(1, 5):
    cands += list(trees_over(alpha, n))
for t in cands:
    if LFl[cls(t)[0]] != 1: continue
    ty = step_types(t)
    if ty is None: continue
    nwalks += 1; total.update(ty)
    if ty["other"] and len(others) < 5: others.append((show(t)[:80], dict(ty)))
print("long flag-1 walks:", nwalks, "step types after burn-in:", dict(total)); print("walks with 'other' steps:", others)
