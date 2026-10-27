"""Hunt for L36 inconsistencies: random spines over a pool (reload pieces + small terms); a walk that reaches a reload
node N_i N_k S (proved infinite) must have flag 1; a walk that ends at the leaf S must have flag 0."""
import sys, random
from dm import *
from classes import cls, LFl, MFl
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
B = parse("S(SS)(SS)")
SS = app(0, 0)
Ns = [B]
for _ in range(6): Ns.append(app(SS, Ns[-1]))
Nset = {n: i for i, n in enumerate(Ns)}
def is_reload(u):
    a, h = spine(u)
    # N_i N_k S  ==  for i>=1: S S N_{i-1} N_k S ; for i = 0: S(SS)(SS) N_k S
    # second slot must be N_k with k >= 1 (= SS N_{k-1}); N_0 = B in that slot does NOT reload
    if len(a) == 4 and a[0] == 0 and a[1] in Nset and Nset.get(a[2], 0) >= 1 and a[3] == 0: return True
    if len(a) == 4 and a[0] == SS and a[1] == SS and Nset.get(a[2], 0) >= 1 and a[3] == 0: return True
    return False
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
small = [t for n in range(1, 6) for t in trees(n)]
pool = small + Ns[:4] + [parse("S(SS)"), parse("SS(S(SS))")]
def walk(u, nodes=60, budget=3000):
    for j in range(nodes):
        if is_reload(u): return "reload"
        args, h = spine(u)
        if len(args) == 0: return "S"
        if len(args) <= 2: u = args[0]; continue
        st = list(reversed(args)); k = 0
        while len(st) > 2 and k < budget:
            a = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
            if k % 200 == 0 and size(st[-1]) > 4000: break
        if len(st) > 2: return "bot?"
        u = st[-1]
    return "long"
from collections import Counter
stat = Counter(); bad = []
N = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
for it in range(N):
    m = random.randint(3, 6)
    t = 0
    for _ in range(m): t = app(t, random.choice(pool))
    if random.random() < 0.5: t = app(random.choice(pool), t) if random.random() < 0.5 else t
    c = cls(t)
    w = walk(t)
    stat[(w, LFl[c[0]])] += 1
    if (w == "reload" and LFl[c[0]] == 0) or (w == "S" and LFl[c[0]] == 1):
        if len(bad) < 20: bad.append((show(t), c, w))
print(stat); print("INCONSISTENT:", bad)
