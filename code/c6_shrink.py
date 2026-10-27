"""C6 completeness: at a computed node u (>= 3 arguments) whose P39 class is bottom_P and whose M35 class is in F, is
there always a bottom_P hnf component smaller than u? (main agent, 2026-10-27) Usage: python c6_shrink.py NMAX"""
import sys, collections
sys.setrecursionlimit(100000)
import hc
from li_explore import terms
from lw_anatomy import hnf
from verify_model import load
Pr, PF, PT = load("../data/model39_productivity.txt")
Mr, MF, MT = load("../data/model35_hn.txt")
sP, sM = Pr.index("S"), Mr.index("S")
C = {}
def cls(i):
    if i == 0: return (sP, sM)
    r = C.get(i)
    if r is None:
        a = cls(hc.L[i]); b = cls(hc.R[i]); r = (int(PT[a[0], b[0]]), int(MT[a[1], b[1]])); C[i] = r
    return r
NMAX = int(sys.argv[1])
stat = collections.Counter(); bad = []
for n in range(3, NMAX + 1):
    for t in terms(n):
        c = cls(t)
        if PF[c[0]] or not MF[c[1]]: continue
        if len(hc.spine(t)[0]) <= 2: continue
        L = hnf(t)
        if L is None: stat["cap"] += 1; continue
        kids = [x for x in L if not PF[cls(x)[0]]]
        best = min(hc.size(x) for x in kids)
        if best < n: stat["shrinks"] += 1
        else:
            stat["grows"] += 1
            if len(bad) < 12: bad.append((hc.show(t), [hc.show(x)[:50] for x in kids]))
print(dict(stat))
for b in bad: print("  ", b)
