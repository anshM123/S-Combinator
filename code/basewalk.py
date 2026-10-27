"""Hypothesis test: along a leftmost Böhm-tree path, at successive 'NEW' steps the base occurrence of the node strictly
decreases (lies strictly inside the previous one).

Provenance elements (occurrence, extras); a node's spine is ch(occurrence) ++ extras. A step from node u to its
leftmost child c is 'NEW' when c is not a sub-element of u (it was built by the head run), otherwise 'dec'.
For flag-0 terms (L36) with an hnf we record whether the bases of consecutive NEW nodes always descend, separately for
NEW nodes whose M35 class is 28 or 26 (the resisting component) and others.
Usage: python basewalk.py NMAX [STEPS] | python basewalk.py rand COUNT SEED
"""
import sys, collections, random
from verify_model import load
from symb import trees, show
from piecewalk import number

L = load("../data/model36_leftpath.txt"); Mm = load("../data/model35_hn.txt")
sL, sM = L[0].index("S"), Mm[0].index("S")

def classes(t):
    memo = {}
    def jc(u):
        if u == "S": return (sL, sM)
        r = memo.get(id(u))
        if r is None:
            a, b = jc(u[0]), jc(u[1]); r = (int(L[2][a[0], b[0]]), int(Mm[2][a[1], b[1]])); memo[id(u)] = r
        return r
    return jc

def elem_class(e, occ_cls):
    k = occ_cls[e[0]]
    for x in e[1]:
        xk = elem_class(x, occ_cls)
        k = (int(L[2][k[0], xk[0]]), int(Mm[2][k[1], xk[1]]))
    return k

def subelements(e, acc):
    acc.add(e)
    for x in e[1]:
        subelements(x, acc)
    return acc

def walk(t, steps=80, budget=3000):
    root, kids, parent = number(t)
    jc = classes(t)
    occ = []
    def go(u):
        if u == "S": occ.append(u); return
        go(u[0]); go(u[1]); occ.append(u)
    go(t)
    occ_cls = [jc(u) for u in occ]
    def inside(u, w):
        p = parent[u]
        while p is not None:
            if p == w: return True
            p = parent[p]
        return False
    node = (root, ()); last_new = None; viol = collections.Counter(); nnew = 0
    for _ in range(steps):
        K = [(k, ()) for k in kids[node[0]]] + list(node[1])
        work = 0
        while len(K) >= 3 and work < budget:
            a, b, c = K[0], K[1], K[2]
            K = [(k, ()) for k in kids[a[0]]] + list(a[1]) + [c, (b[0], b[1] + (c,))] + K[3:]
            work += 1
        if len(K) >= 3 or not K:
            break
        child = K[0]
        if child not in subelements(node, set()):
            nnew += 1
            m = elem_class(node, occ_cls)[1]
            grp = "scc" if m in (26, 28) else "other"
            if last_new is not None and not inside(node[0], last_new[0]):
                viol[(grp, "base not inside previous NEW base")] += 1
            last_new = node
        node = child
    return nnew, viol

if __name__ == "__main__":
    if sys.argv[1] == "rand":
        from opencount_rand import random_tree
        COUNT, SEED = int(sys.argv[2]), int(sys.argv[3])
        rng = random.Random(SEED); tot = collections.Counter(); hits = 0; ex = None
        for _ in range(COUNT):
            t = random_tree(rng.randint(8, 26), rng)
            jc = classes(t); k = jc(t)
            if L[1][k[0]] != 0 or not Mm[1][k[1]] or k[1] not in (26, 28):
                continue
            hits += 1
            nnew, viol = walk(t)
            tot.update(viol)
            if viol and ex is None: ex = show(t)
        print(f"random flag-0 terms in M35 classes 26/28: {hits}; violations {dict(tot)}; example {ex}")
    else:
        NMAX = int(sys.argv[1])
        for n in range(3, NMAX + 1):
            tot = collections.Counter(); cnt = 0; ex = {}
            for t in trees(n):
                jc = classes(t); k = jc(t)
                if L[1][k[0]] != 0 or not Mm[1][k[1]]:
                    continue
                cnt += 1
                nnew, viol = walk(t)
                for key in viol:
                    tot[key] += 1
                    ex.setdefault(key, show(t))
            print(f"n={n}: flag-0 terms {cnt}; terms with violations {dict(tot)}; examples {ex}", flush=True)
