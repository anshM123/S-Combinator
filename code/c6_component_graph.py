"""C6 completeness probe (main agent, 2026-10-26): the component graph on joint classes.
If t is productive and [t]_P = ⊥_P, the hnf S h1 h2 of t has [t] = s·[h1]·[h2] (conversion invariance) and some
component in ⊥_P; following such components gives an infinite Böhm-tree path whose nodes all have hnfs, i.e. all
have joint class (⊥_P, m) with m ∈ F_M (Theorem A / Q10). Edge j -> j' (both in (⊥_P, F_M)) when
j = s·j'·y, s·x·j' or s·j' for some realised joint classes x, y. If this graph is acyclic, C6's completeness half
follows at once. Otherwise this lists its strongly connected components."""
import numpy as np, itertools, sys
from verify_model import load
P_reps, P_F, P = load("../data/model39_productivity.txt")
M_reps, M_F, M = load("../data/model35_hn.txt")
sP, sM = P_reps.index("S"), M_reps.index("S")
start = (sP, sM)
seen = {start}; J = [start]; frontier = [start]
while frontier:
    new = []
    for a in list(J):
        for b in list(J):
            for x, y in ((a, b), (b, a)):
                c = (int(P[x[0], y[0]]), int(M[x[1], y[1]]))
                if c not in seen: seen.add(c); J.append(c); new.append(c)
    frontier = new
idx = {c: i for i, c in enumerate(J)}; n = len(J)
mul = lambda a, b: idx[(int(P[J[a][0], J[b][0]]), int(M[J[a][1], J[b][1]]))]
s = idx[start]
bad = [i for i in range(n) if not P_F[J[i][0]] and M_F[J[i][1]]]          # (⊥_P, has hnf)
print("joint classes:", n, "; (⊥_P, F_M) classes:", len(bad))
E = {i: set() for i in bad}
for x in range(n):
    sx = mul(s, x)
    if sx in E and x in E: E[sx].add(x)
    for y in range(n):
        sxy = mul(sx, y)
        if sxy in E:
            if x in E: E[sxy].add(x)
            if y in E: E[sxy].add(y)
# strongly connected components (Tarjan)
index = {}; low = {}; st = []; on = set(); comps = []; cnt = [0]
def strong(v):
    index[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on.add(v)
    for w in E[v]:
        if w not in index: strong(w); low[v] = min(low[v], low[w])
        elif w in on: low[v] = min(low[v], index[w])
    if low[v] == index[v]:
        comp = []
        while True:
            w = st.pop(); on.discard(w); comp.append(w)
            if w == v: break
        comps.append(comp)
sys.setrecursionlimit(10000)
for v in bad:
    if v not in index: strong(v)
cyc = [c for c in comps if len(c) > 1 or c[0] in E[c[0]]]
print("edges:", sum(len(v) for v in E.values()), "; cyclic SCCs:", len(cyc))
for c in cyc: print("   SCC", [J[i] for i in c], "self-loops:", [J[i] for i in c if i in E[i]])

# Lemma (M) probe: products of two productive joint classes that fall into ⊥_P — are they all hnf-free (⊥_M)?
minimal = {}
for x in range(n):
    for y in range(n):
        if P_F[J[x][0]] and P_F[J[y][0]]:
            z = mul(x, y)
            if not P_F[J[z][0]]: minimal.setdefault(z, []).append((x, y))
print("joint classes of minimal ⊥_P products:", sorted(J[z] for z in minimal))
print("all hnf-free (M35 bottom)?", all(not M_F[J[z][1]] for z in minimal))
