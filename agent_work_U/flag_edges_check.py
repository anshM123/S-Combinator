"""Validate the abstraction used for flag invariance on concrete leftmost walks: every computed step (node with >= 3
arguments -> leftmost child) of every walk from terms <= n leaves must be an edge kappa -> beta of a final chain state
(s, b, beta) of G with kappa = s.s.b.beta; and no concrete step goes from a flag-0 node to a flag-1 child."""
import sys, collections
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/code")
from verify_model import load
from dm import *
from classes import cls, LFl, MFl, clear_cache
from stackview import hnf
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
edges = set()
for b in J:
    for be in J:
        kap = mul(mul(mul(s, s), b), be)
        if hnfc(kap): edges.add((kap, be))
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
miss = 0; flagviol = 0; steps = 0
for n in range(3, int(sys.argv[1]) + 1):
    for t in trees(n):
        m = mark(); u = t
        for j in range(40):
            if u == 0: break
            a = spine(u)[0]
            if len(a) <= 2: u = a[0]; continue
            H = hnf(u, bud=5000)
            if H is None: break
            cu, cc = cls(u), cls(H[0]); steps += 1
            if (cu, cc) not in edges: miss += 1
            if LFl[cu[0]] == 0 and LFl[cc[0]] == 1: flagviol += 1
            u = H[0]
        truncate(m); clear_cache(m)
print("concrete computed steps:", steps, "missing from abstraction:", miss, "flag-0 -> flag-1 steps:", flagviol)
