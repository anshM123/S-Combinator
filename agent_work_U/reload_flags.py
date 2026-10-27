"""All reload-cycle nodes N_i N_m S (i < m) have an L36 flag-1 joint class: the class of N_k is eventually periodic, so
finitely many class pairs occur; check them all."""
from dm import *
from classes import cls, LFl, LTl, MTl
SS = app(0, 0); Bt = parse("S(SS)(SS)")
Ns = [Bt]
for k in range(60): Ns.append(app(SS, Ns[-1]))
cl = [cls(n) for n in Ns]
# find preperiod/period of the class sequence (deterministic: [N_(k+1)] = [SS].[N_k])
first = {}
for k, c in enumerate(cl):
    if c in first: pre, per = first[c], k - first[c]; break
    first[c] = k
print("class of N_k: preperiod", pre, "period", per, "classes", cl[:pre + per])
def mulj(a, b): return (LTl[a[0]][b[0]], MTl[a[1]][b[1]])
sJ = cls(0)
bad = []; pairs = set()
K = pre + 2 * per + 2
for i in range(K):
    for m in range(i + 1, K + per + 1):
        ci = cl[i] if i < len(cl) else None
        cm = cl[m]
        c = mulj(mulj(ci, cm), sJ)
        pairs.add((ci, cm))
        if LFl[c[0]] != 1: bad.append((i, m, c))
print("distinct (class N_i, class N_m) pairs checked:", len(pairs), "flag-0 reload nodes:", bad if bad else "NONE")
