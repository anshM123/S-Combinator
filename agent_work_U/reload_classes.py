"""L36 x M35 classes of reload-cycle terms N_i N_k f for many closed fuels f (opaque-fuel argument: these all have
infinite leftmost paths because the fuel is never executed)."""
import sys, itertools
from dm import *
from classes import cls, LFl, MFl
B = parse("S(SS)(SS)")
def N(k):
    t = B
    for _ in range(k): t = app(app(0, 0), t)
    return t
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
from collections import Counter
cnt = Counter(); bad = []
for n in range(1, 9):
    for f in trees(n):
        for i in range(0, 3):
            for k in range(1, 4):
                t = app(app(N(i), N(k)), f)
                c = cls(t)
                cnt[c] += 1
                if LFl[c[0]] == 0 and len(bad) < 10: bad.append((show(t), c))
print(cnt.most_common(20)); print("flag-0 examples:", bad)
