"""Shape of size-increasing ('NEW') nodes on leftmost walks of flag-0 terms in the D2 joint classes, and how the
argument slots of consecutive NEW nodes relate.

For each NEW node u = S.[e1..em] we record m and whether e1 = S. For consecutive NEW nodes u, u' we describe each
argument e'_i of u' relative to the arguments of u: 'eq k' (equal to e_k), 'sub k' (proper subterm of e_k), 'sup k'
(e_k is a proper subterm of e'_i), or 'new'.
Usage: python reloadshape.py NMAX RAND SEED
"""
import sys, collections, random
sys.setrecursionlimit(100000)
from verify_model import load
from symb import trees, show, spine
from opencount_rand import random_tree

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
def subterms(t):
    acc = set(); st = [t]
    while st:
        u = st.pop()
        if u in acc: continue
        acc.add(u)
        if u != "S": st.append(u[0]); st.append(u[1])
    return acc
def rel(x, args):
    for k, e in enumerate(args):
        if x == e: return f"eq{k}"
    for k, e in enumerate(args):
        if x in subterms(e): return f"sub{k}"
    for k, e in enumerate(args):
        if e in subterms(x): return f"sup{k}"
    return "new"

shapes = collections.Counter(); trans = collections.Counter(); ex = {}
def walk(t, cap=40):
    u = t; prev = None
    for _ in range(cap):
        k = jc(u)
        if not Mm[1][k[1]]: return
        h = H(u)
        if not h: return
        c = h[0]
        if c not in subterms(u) or c == u:
            _, args = spine(u)
            shp = (len(args), args[0] == "S", k)
            shapes[shp] += 1
            if prev is not None:
                key = (prev[0], shp[:2], tuple(rel(x, prev[1]) for x in args))
                trans[key] += 1
                ex.setdefault(key, show(t))
            prev = (shp[:2], args)
        u = c

if __name__ == "__main__":
    NMAX, NR, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    pool = [t for n in range(5, NMAX + 1) for t in trees(n)]
    rng = random.Random(SEED)
    pool += [random_tree(rng.randint(NMAX + 1, NMAX + 12), rng) for _ in range(NR)]
    cnt = 0
    for t in pool:
        k = jc(t)
        if L[1][k[0]] == 0 and k[1] in D2:
            cnt += 1; walk(t)
    print(f"flag-0 D2 roots walked: {cnt}")
    print("NEW-node shapes (spine length, first arg is S, joint class):", shapes.most_common(12))
    print("consecutive NEW-node slot relations (prev shape, next shape, relation of each next arg):")
    for key, v in trans.most_common(25):
        print(f"   {v:6d}  {key}   e.g. {ex[key]}")
