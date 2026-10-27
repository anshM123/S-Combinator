"""Signatures of o-large pushes in component walks: (class u, class q1, class v, source, class of pushed q) and the
signature sequence per walk (does a signature ever recur within one walk?)."""
import sys
from dm import *
from classes import cls, COMPONENT, MFl
from chainsrc import chain
from ordpush import o
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def sigs(t, maxn=200):
    u = t; out = []
    for j in range(maxn):
        if u == 0: return out, "leaf"
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        r = chain(q1, v)
        if r is None: return out, "bot"
        c, pushed = r
        for (q, src) in pushed:
            if o(q) >= o(q1) and MFl[cls(c)[1]] == 1:
                out.append((cls(u), cls(q1), cls(v), src, cls(q), len(spine(q1)[0])))
        u = c
    return out, "long"
sc = Counter(); rec = 0; ex = {}
for n in range(3, int(sys.argv[1]) + 1):
    for t in trees(n):
        if cls(t) not in COMPONENT: continue
        s, end = sigs(t)
        if len(set(s)) < len(s): rec += 1
        for x in s:
            sc[(x, end)] += 1
            if (x, end) not in ex: ex[(x, end)] = show(t)
print("walks with a repeated signature:", rec)
for k, v in sc.most_common(40): print(v, k, ex[k])
