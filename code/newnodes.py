"""Measure test between consecutive NEW nodes of a leftmost Böhm-tree walk.

A step node -> leftmost child is NEW when the child is not a proper subterm of the node (it was built by the head run).
For each walk we list the NEW nodes u_1, u_2, ... and test, for consecutive ones, (a) |u_{i+1}| < |u_i| (size) and
(b) pieces(u_{i+1}) < pieces(u_i) in the multiset extension of 'strictly inside' on occurrences of the root term
(pieces = provenance occurrences making up the node). Reported separately for L36 flag 0 / flag 1 terms.
Usage: python newnodes.py NMAX | python newnodes.py rand COUNT SEED
"""
import sys, collections, random
from verify_model import load
from symb import trees, show
from piecewalk import number, pieces, mul_less

L = load("../data/model36_leftpath.txt"); Mm = load("../data/model35_hn.txt")
sL, sM = L[0].index("S"), Mm[0].index("S")

def jclass(t):
    memo = {}
    def jc(u):
        if u == "S": return (sL, sM)
        r = memo.get(id(u))
        if r is None:
            a, b = jc(u[0]), jc(u[1]); r = (int(L[2][a[0], b[0]]), int(Mm[2][a[1], b[1]])); memo[id(u)] = r
        return r
    return jc(t)

def size(t): return 1 if t == "S" else size(t[0]) + size(t[1])

def subterms(t, acc):
    stack = [t]
    while stack:
        u = stack.pop()
        if u in acc: continue
        acc.add(u)
        if u != "S": stack.append(u[0]); stack.append(u[1])
    return acc

def walk(t, steps=60, budget=3000):
    root, kids, parent = number(t)
    occ = []
    def go(u):
        if u == "S": occ.append(u); return
        go(u[0]); go(u[1]); occ.append(u)
    go(t)
    def term_of(e):
        u = occ[e[0]]
        for x in e[1]: u = (u, term_of(x))
        return u
    node = (root, ()); news = []
    for _ in range(steps):
        K = [(k, ()) for k in kids[node[0]]] + list(node[1]); w = 0
        while len(K) >= 3 and w < budget:
            a, b, c = K[0], K[1], K[2]
            K = [(k, ()) for k in kids[a[0]]] + list(a[1]) + [c, (b[0], b[1] + (c,))] + K[3:]; w += 1
        if len(K) >= 3 or not K: break
        child = K[0]
        tn, tc = term_of(node), term_of(child)
        if tc not in subterms(tn, set()) or tc == tn:
            news.append((node, tn))
        node = child
    bad_size = bad_piece = 0
    for (e1, t1), (e2, t2) in zip(news, news[1:]):
        if not size(t2) < size(t1): bad_size += 1
        if not mul_less(pieces(e2, collections.Counter()), pieces(e1, collections.Counter()), parent): bad_piece += 1
    return len(news), bad_size, bad_piece

def run(terms):
    stat = collections.Counter(); ex = {}
    for t in terms:
        k = jclass(t)
        if not Mm[1][k[1]]: continue
        fl = int(L[1][k[0]])
        nn, bs, bp = walk(t)
        for key, bad in ((("size", fl), bs), (("pieces", fl), bp)):
            stat[(key, bad > 0)] += 1
            if bad and key not in ex: ex[key] = show(t)
    return stat, ex

if __name__ == "__main__":
    if sys.argv[1] == "rand":
        from opencount_rand import random_tree
        rng = random.Random(int(sys.argv[3]))
        terms = [random_tree(rng.randint(8, 24), rng) for _ in range(int(sys.argv[2]))]
        stat, ex = run(terms)
        print("random:", dict(sorted(stat.items())), "\n  examples:", ex)
    else:
        for n in range(3, int(sys.argv[1]) + 1):
            stat, ex = run(trees(n))
            print(f"n={n}:", dict(sorted(stat.items())), "examples:", ex, flush=True)
