"""Class-level graph of rightmost (and, for comparison, leftmost) Böhm-tree walks over the joint magma P x M35, where P is
the path model (R19 or L36). Edge c -> d when some S x y in class c has child (x for leftmost, y for rightmost) in class d,
or (both sides) S x in class c has child x in class d. Restricted to joint classes with path flag 0 and M35 class in F.
Prints the nontrivial strongly connected components (main agent, 2026-10-27). Usage: python rw_classgraph.py right|left"""
import sys
from verify_model import load
side = sys.argv[1]
P = "../data/model19_rightpath.txt" if side == "right" else "../data/model36_leftpath.txt"
Pr, PF, PT = load(P)
Mr, MF, MT = load("../data/model35_hn.txt")
mP = lambda a, b: int(PT[a, b]); mM = lambda a, b: int(MT[a, b])
sP, sM = Pr.index("S"), Mr.index("S")
J = {(sP, sM)}; fr = [(sP, sM)]
mul = lambda a, b: (mP(a[0], b[0]), mM(a[1], b[1]))
while fr:
    new = []
    for a in list(J):
        for b in list(J):
            for c in (mul(a, b), mul(b, a)):
                if c not in J: J.add(c); new.append(c)
    fr = new
J = sorted(J)
S = (sP, sM)
live = [c for c in J if not PF[c[0]] and MF[c[1]]]
print(len(J), "joint classes;", len(live), "with path flag 0 and M35 class in F")
E = {c: set() for c in live}
for x in J:
    sx = mul(S, x)
    if sx in E and x in E: E[sx].add(x)            # S x: one child x
    for y in J:
        sxy = mul(sx, y)
        if sxy in E:
            child = x if side == "left" else y
            if child in E: E[sxy].add(child)
# Tarjan SCC
idx = {}; low = {}; st = []; on = set(); comps = []; cnt = [0]
sys.setrecursionlimit(10000)
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
for v in live:
    if v not in idx: sc(v)
nontriv = [c for c in comps if len(c) > 1 or c[0] in E[c[0]]]
print("nontrivial SCCs:", len(nontriv))
for c in nontriv:
    print("  ", sorted(c), " reps:", [ (Pr[a], Mr[b]) for a, b in sorted(c)][:4])
