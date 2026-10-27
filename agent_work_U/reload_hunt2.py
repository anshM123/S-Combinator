"""Exhaustive: trees over the alphabet {S, SS, B, N1, N2, S(SS)} with <= n leaves; walk; reload reached => flag must be 1."""
import sys
from dm import *
from classes import cls, LFl
from reload_hunt import is_reload, walk, Ns
alpha = [0, app(0, 0), Ns[0], Ns[1], Ns[2], parse("S(SS)")]
def trees(n):
    if n == 1:
        for a in alpha: yield a
        return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
from collections import Counter
stat = Counter(); bad = []; ex = {}
for n in range(1, int(sys.argv[1]) + 1):
    for t in trees(n):
        c = cls(t); w = walk(t, nodes=80, budget=4000)
        key = (w, LFl[c[0]]); stat[key] += 1
        if key not in ex: ex[key] = show(t)
        if (w == "reload" and LFl[c[0]] == 0) or (w == "S" and LFl[c[0]] == 1):
            if len(bad) < 20: bad.append((show(t), c, w))
    print(n, dict(stat), flush=True)
print("examples:", ex); print("INCONSISTENT:", bad)
