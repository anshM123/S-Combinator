"""Classify fuel-S tail calls q.S -> q'.S (depth-1 nodes, chain of length 1): q = Q.z;  'R' if H(Q) = S S y and q' = y.z
(z unchanged);  'B' if H(Q) = S(SS)(SS) and q' = z.(SS z) (reload);  'syn2' if q has exactly 2 args;  else 'other'
(with details).  Run on reload walks and on all depth-1 tail calls in component walks <= n leaves."""
import sys
from dm import *
from classes import cls, COMPONENT
from chainsrc import chain, H
from collections import Counter
Bt = parse("S(SS)(SS)"); SS = app(0, 0)
def classify(q, q2):
    a = spine(q)[0]
    if len(a) == 2: return "syn2"
    Q, z = L[q], R[q]
    hQ = H(Q) if len(spine(Q)[0]) >= 3 else spine(Q)[0]
    if hQ is None: return "Qbot"
    if len(hQ) == 2 and hQ[0] == 0 and q2 == app(hQ[1], z): return "R"
    if len(hQ) == 2 and hQ[0] == SS and hQ[1] == SS and q2 == app(z, app(SS, z)): return "B"
    return "other"
def tc_steps(t, maxn=300):
    u = t; out = []
    for j in range(maxn):
        if u == 0: return out
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        r = chain(q1, v)
        if r is None: return out
        c, pushed = r
        if v == 0 and len(pushed) == 1:
            out.append(classify(q1, pushed[0][0]))
        u = c
    return out
print("reload:", Counter(tc_steps(parse("S(S(SS))(S(SS))(SS)S"))))
print("reload2:", Counter(tc_steps(parse("SS(SS(S(SS)(SS)))(SS(SS(SS(S(SS)(SS)))))S"))))
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
tot = Counter(); ex = {}
for n in range(3, int(sys.argv[1]) + 1):
    for t in trees(n):
        if cls(t) not in COMPONENT: continue
        for kind in tc_steps(t):
            tot[kind] += 1
            if kind not in ex: ex[kind] = show(t)
print("component depth-1 tail calls:", dict(tot)); print(ex)
