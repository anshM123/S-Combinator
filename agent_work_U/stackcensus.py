"""Census of multiplier-stack events in leftmost walks from component terms: transitions between consecutive
'chain' events, class pairs (class q, class v), chain lengths, and the longest runs of tail calls (k = 1)."""
import sys
from dm import *
from classes import cls, COMPONENT
from stackview import events
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
kc = Counter(); qv = Counter(); runs = Counter(); best = []
for n in range(3, int(sys.argv[1]) + 1):
    for t in trees(n):
        if cls(t) not in COMPONENT: continue
        ev = events(show(t), maxn=80)
        run = 0; mx = 0
        for e in ev:
            if isinstance(e, tuple) and e[0] == "chain":
                kc[e[2]] += 1; qv[(e[2], e[4], e[5])] += 1
                if e[2] == 1: run += 1; mx = max(mx, run)
                else: run = 0
            else: run = 0
        runs[mx] += 1
        if mx >= 3: best.append((mx, show(t)))
print("chain lengths:", sorted(kc.items())); print("max tail-call runs:", sorted(runs.items()))
print("k=1 class pairs:", [(k, v) for k, v in qv.most_common() if k[0] == 1][:30])
print("examples:", sorted(best)[-8:])
