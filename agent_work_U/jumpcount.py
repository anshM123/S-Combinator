"""Count pops / jumps / computed steps and the right-spine depth along long leftmost walks of flag-1 terms (known
infinite walks): reload terms, Omega, and all 'long' self-applications X X etc. with X <= 12 leaves."""
import sys
from dm import *
from classes import cls, LFl
from stackview import hnf
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def profile(t, nodes=400):
    u = t; ev = Counter(); last_jump = -1; depths = []
    for j in range(nodes):
        if u == 0: return ev, last_jump, "leaf", depths
        q1, v = L[u], R[u]
        d = 0; x = u
        while x != 0: x = R[x]; d += 1
        depths.append(d)
        if q1 == 0: ev["pop"] += 1; u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: ev["jump"] += 1; last_jump = j; u = a[0]; continue
        H = hnf(u, bud=50000)
        if H is None: return ev, last_jump, "bot", depths
        ev["chain"] += 1; u = H[0]
    return ev, last_jump, "long", depths
cands = ["S(S(SS))(S(SS))(SS)S", "S(S(SS))(S(SS))(S(S(SS))(S(SS)))", "S(S(S(SS))(S(SS))(S(S(SS))(S(SS))))S"]
for n in range(7, 12):
    for X in trees(n):
        for t in (app(X, X), app(app(0, X), X)):
            if LFl[cls(t)[0]] == 1: cands.append(show(t))
seen = set()
for s in cands:
    if s in seen: continue
    seen.add(s)
    ev, lj, end, depths = profile(parse(s))
    if end == "long":
        print(s[:60], dict(ev), "last jump at node", lj, "depth min/max over 2nd half:", min(depths[200:]), max(depths[200:]))
