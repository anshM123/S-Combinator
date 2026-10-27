"""Does the joint class (P39 x M35) of a term determine the joint classes of its hnf components? (terms <= N leaves)"""
import sys, numpy as np
from collections import defaultdict
from verify_model import load
from symb import trees, spine, hnf
P_reps, P_F, P = load("../data/model39_productivity.txt")
M_reps, M_F, M = load("../data/model35_hn.txt")
sP, sM = P_reps.index("S"), M_reps.index("S")
memo = {}
def J(t):
    if t == "S": return (sP, sM)
    if t in memo: return memo[t]
    a, b = J(t[0]), J(t[1])
    r = (int(P[a[0], b[0]]), int(M[a[1], b[1]])); memo[t] = r; return r
N = int(sys.argv[1]) if len(sys.argv) > 1 else 11
trans = defaultdict(set); cnt = 0; nohnf = 0
for n in range(1, N + 1):
    for t in trees(n):
        r = hnf(t, budget=4 * n + 50)
        if r[0] != "hnf": nohnf += 1; continue
        comps = tuple(J(c) for c in r[1])
        trans[J(t)].add(comps); cnt += 1
amb = {j: v for j, v in trans.items() if len(v) > 1}
print("terms with hnf:", cnt, " joint classes seen:", len(trans), " classes whose component-classes are NOT determined:", len(amb))
botamb = {j: v for j, v in amb.items() if not P_F[j[0]]}
print("  among non-productive joint classes:", len(botamb))
for j, v in list(botamb.items())[:3]:
    print("   class", j, "->", len(v), "different component-class tuples, e.g.", list(v)[:3])
