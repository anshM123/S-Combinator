"""Do computed leftmost-path edges of the main agent's class abstraction (code/leftpathcert.py logic, re-implemented
read-only) ever go from a flag-0 node class (with hnf) to a flag-1 child class?  A final tail-chain state (s, b, beta)
gives the edge  kappa = s.s.b.beta -> beta  (chain length 0: 'dec'; length >= 1: 'new' if the state has an incoming
chain edge).  Syntactic edges preserve the flag by the certified closure facts."""
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
flag = lambda k: P[1][k[0]]
hnf = lambda k: Mm[1][k[1]] == 1
one = collections.defaultdict(list); two = collections.defaultdict(list)
for x in J:
    one[mul(s, x)].append(x)
    for y in J: two[mul(mul(s, x), y)].append((x, y))
states = [(a, b, be) for a in J for b in J for be in J if hnf(mul(mul(mul(s, a), b), be))]
Sset = set(states); indeg = collections.Counter()
for (a, b, be) in states:
    for x in one.get(a, []):
        t = (x, be, mul(b, be))
        if t in Sset: indeg[t] += 1
    if a != s and a in two:
        for (a2, b2) in two.get(mul(a, be), []):
            if b2 == s: continue
            t = (a2, b2, mul(b, be))
            if t in Sset: indeg[t] += 1
bad = collections.Counter()
for (a, b, be) in states:
    if a != s: continue
    kap = mul(mul(mul(s, a), b), be)
    if flag(kap) == 0 and hnf(kap):
        if flag(be) == 1:
            bad[("dec", kap, be)] += 1
            if indeg[(a, b, be)]: bad[("new", kap, be)] += 1
print("joint classes:", len(J), "chain states:", len(states))
print("flag-0 -> flag-1 computed edges:", dict(bad) if bad else "NONE")
