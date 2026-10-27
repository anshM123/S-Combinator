"""C6 completeness half at class level (main agent, 2026-10-27): joint magma P39 x M35; nodes = joint classes with P39 class
bottom_P and M35 class in F (have an hnf by Q10); edges to the bottom_P children of S x y / S x in that class. If this graph
had no cycle, every bottom_P path would reach an M35-bottom node (no hnf, Theorem A) within 17 steps. Prints the SCCs."""
import sys
from verify_model import load
Pr, PF, PT = load("../data/model39_productivity.txt")
Mr, MF, MT = load("../data/model35_hn.txt")
mP = lambda a, b: int(PT[a, b]); mM = lambda a, b: int(MT[a, b])
sP, sM = Pr.index("S"), Mr.index("S")
mul = lambda a, b: (mP(a[0], b[0]), mM(a[1], b[1]))
J = {(sP, sM)}; fr = [(sP, sM)]
while fr:
    new = []
    for a in list(J):
        for b in list(J):
            for c in (mul(a, b), mul(b, a)):
                if c not in J: J.add(c); new.append(c)
    fr = new
J = sorted(J); S = (sP, sM)
botP = [k for k in range(len(Pr)) if not PF[k]]
print(len(J), "joint classes; bottom_P =", botP)
nodes = [c for c in J if not PF[c[0]] and MF[c[1]]]
print(len(nodes), "nodes (bottom_P, F_M)")
E = {c: set() for c in nodes}
for x in J:
    sx = mul(S, x)
    if sx in E and not PF[x[0]] and x in E: E[sx].add(x)
    for y in J:
        sxy = mul(sx, y)
        if sxy in E:
            for ch in (x, y):
                if not PF[ch[0]] and ch in E: E[sxy].add(ch)
idx = {}; low = {}; st = []; on = set(); comps = []; cnt = [0]
def sc(v):
    idx[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on.add(v)
    for w in E[v]:
        if w not in idx: sc(w); low[v] = min(low[v], low[w])
        elif w in on: low[v] = min(low[v], idx[w])
    if low[v] == idx[v]:
        comp = []
        while True:
            w = st.pop(); on.discard(w); comp.append(w)
            if w == v: break
        comps.append(comp)
for v in nodes:
    if v not in idx: sc(v)
nontriv = [c for c in comps if len(c) > 1 or c[0] in E[c[0]]]
print("nontrivial SCCs:", len(nontriv))
for c in nontriv: print("  ", sorted(c), [(Mr[b]) for a, b in sorted(c)][:5])
# must-exit check: does every node have an edge to a node that is NOT in its SCC, or a child with M bottom?
