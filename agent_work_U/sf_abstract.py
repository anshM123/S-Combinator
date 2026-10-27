"""Can SF be certified on the class abstraction?  Abstract leftmost computed steps: kappa -> beta via a tail chain of
length k (= number of pushed multipliers) in the main agent's chain graph G (peel/refill edges over joint classes),
from an initial state (a0, b0, beta0) with kappa = s.a0.b0.beta0 to a final state (s, b, beta).  Report the chain
lengths k of abstract steps with both kappa and beta in the component {(14,28), (14,26)}.  If only k in {1, 2} occurred,
SF for the component would follow from finiteness of the abstraction."""
import sys, collections
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/code")
from verify_model import load
P = load("C:/Users/anshm/Downloads/money problems/data/model36_leftpath.txt")
Mm = load("C:/Users/anshm/Downloads/money problems/data/model35_hn.txt")
sP, sM = P[0].index("S"), Mm[0].index("S")
def mul(x, y): return (int(P[2][x[0], y[0]]), int(Mm[2][x[1], y[1]]))
s = (sP, sM)
J = [s]; seen = {s}; i = 0
while i < len(J):
    a = J[i]; i += 1
    for b in J[:i]:
        for c in (mul(a, b), mul(b, a)):
            if c not in seen: seen.add(c); J.append(c)
hnfc = lambda k: Mm[1][k[1]] == 1
one = collections.defaultdict(list); two = collections.defaultdict(list)
for x in J:
    one[mul(s, x)].append(x)
    for y in J: two[mul(mul(s, x), y)].append((x, y))
COMP = {(14, 28), (14, 26)}
states = [(a, b, be) for a in J for b in J for be in J if hnfc(mul(mul(mul(s, a), b), be))]
succ = collections.defaultdict(set)
for (a, b, be) in states:
    if a == s: continue
    for x in one.get(a, []):                        # peel: a = s.x
        succ[(a, b, be)].add((x, be, mul(b, be)))
    if a in two:                                    # refill: a has >= 2 args; H(p v) = S a2 b2 with s.a2.b2 = a.beta
        for (a2, b2) in two.get(mul(a, be), []):
            if b2 == s: continue
            succ[(a, b, be)].add((a2, b2, mul(b, be)))
# BFS over chain lengths from all initial states whose node class is in the component
lengths = collections.Counter()
init = [st for st in states if mul(mul(mul(s, st[0]), st[1]), st[2]) in COMP]
for st0 in init:
    kap = mul(mul(mul(s, st0[0]), st0[1]), st0[2])
    frontier = {st0}; seenk = set()
    for k in range(0, 15):
        nxt = set()
        for st in frontier:
            if st[0] == s and st[2] in COMP: lengths[k] += 1
            for t in succ.get(st, ()):
                if (t, k + 1) not in seenk: seenk.add((t, k + 1)); nxt.add(t)
        frontier = nxt
        if not frontier: break
print("abstract component->component computed steps by chain length k:", sorted(lengths.items()))
