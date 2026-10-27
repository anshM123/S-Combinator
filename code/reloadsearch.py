"""Targeted search for indefinite reloading in the flag-0 D2 classes of the leftmost-path model L36.

Candidates are counter-shaped terms built from small parts: (SS)^j B M R and S S K M R and S K M R (spine 3-5), with
B, K, M, R ranging over a pool of small terms. Kept only if [t] is flag 0 in L36 and its M35 class is in D2.
Each candidate's leftmost walk is run for up to CAP nodes; a walk still running after CAP nodes would contradict the
model (every flag-0 verdict claims a finite path) and is reported with its node-size profile.
Usage: python reloadsearch.py POOLMAX CAP
"""
import sys, collections, itertools
sys.setrecursionlimit(1000000)
from verify_model import load
from symb import trees, show

L = load("../data/model36_leftpath.txt"); Mm = load("../data/model35_hn.txt")
sL, sM = L[0].index("S"), Mm[0].index("S")
D2 = {24, 26, 28, 31, 34}
memo = {}
def jc(t):
    if t == "S": return (sL, sM)
    r = memo.get(t)
    if r is None:
        a, b = jc(t[0]), jc(t[1]); r = (int(L[2][a[0], b[0]]), int(Mm[2][a[1], b[1]])); memo[t] = r
    return r
def H(t):
    if t == "S": return ()
    return App(H(t[0]), t[1])
def App(h, v):
    while len(h) == 2:
        p, q = h
        h, v = App(H(p), v), (q, v)
    return h + (v,)
def size(t):
    n = 0; st = [t]
    while st:
        u = st.pop()
        if u == "S": n += 1
        else: st.append(u[0]); st.append(u[1])
    return n
def walk_len(t, cap):
    u = t; sizes = []
    for i in range(cap):
        k = jc(u)
        if not Mm[1][k[1]]: return i, "bot", sizes
        h = H(u)
        if not h: return i, "S", sizes
        u = h[0]; sizes.append(size(u))
    return cap, "RUNNING", sizes

POOLMAX, CAP = int(sys.argv[1]), int(sys.argv[2])
pool = [t for n in range(1, POOLMAX + 1) for t in trees(n)]
SS = ("S", "S")
def nest(j, b):
    for _ in range(j): b = (SS, b)
    return b
cands = set()
for B, M, R in itertools.product(pool, pool, pool[:40]):
    for j in (0, 1, 2, 3):
        cands.add(((nest(j, B), M), R))
    cands.add((((SS, B), M), R))
    cands.add(((("S", B), M), R))
print(f"pool {len(pool)}, candidates {len(cands)}", flush=True)
stat = collections.Counter(); longest = []
for t in cands:
    k = jc(t)
    if L[1][k[0]] != 0 or k[1] not in D2: continue
    n, how, sizes = walk_len(t, CAP)
    stat[how] += 1
    longest.append((n, show(t), how, sizes[-5:]))
longest.sort(reverse=True)
print("flag-0 D2 candidates by outcome:", dict(stat))
for row in longest[:8]:
    print("   ", row)
