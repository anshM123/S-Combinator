"""Does the multiset of original 'pieces' decrease along leftmost Böhm-tree paths?

Provenance elements: (occurrence of the root term, extras). A node of the leftmost walk is an element; its spine is
ch(occurrence) ++ extras. Head run on the spine, final configuration [c, b.c] (or shorter); the leftmost child is c.
pieces(e) = multiset of occurrences: e's own occurrence plus the pieces of its extras.
Order on occurrences: u < w iff u lies strictly inside w. Multiset extension (Dershowitz-Manna).
For every term with <= NMAX leaves we walk the leftmost path (STEPS steps at most) and count steps where the child's
pieces are NOT smaller than the node's, separately for terms whose L36 flag is 0 (finite) and 1 (infinite).
Usage: python piecewalk.py NMAX [STEPS]
"""
import sys, collections
from verify_model import load
from symb import trees, show

L = load("../data/model36_leftpath.txt"); Mm = load("../data/model35_hn.txt")
sL, sM = L[0].index("S"), Mm[0].index("S")
memo = {}
def jc(t):
    if t == "S": return (sL, sM)
    r = memo.get(t)
    if r is None:
        a, b = jc(t[0]), jc(t[1]); r = (int(L[2][a[0], b[0]]), int(Mm[2][a[1], b[1]])); memo[t] = r
    return r

def number(t):
    kids, parent = [], []
    def go(u):
        if u == "S":
            kids.append(()); parent.append(None); return len(kids) - 1
        l = go(u[0]); r = go(u[1])
        kids.append(kids[l] + (r,)); parent.append(None); me = len(kids) - 1
        for c in kids[l] + (r,):
            parent[c] = me
        return me
    root = go(t)
    # 'inside' relation via spine-children parent links: u inside w iff w is a proper ancestor of u
    return root, kids, parent

def pieces(e, out):
    out[e[0]] += 1
    for x in e[1]:
        pieces(x, out)
    return out

def less(u, w, parent):            # u strictly inside w
    p = parent[u]
    while p is not None:
        if p == w: return True
        p = parent[p]
    return False

def mul_less(N, M, parent):        # N <_mul M ?
    if N == M: return False
    A = M - N; B = N - M           # Counter subtraction keeps positive parts
    return all(any(less(y, x, parent) for x in A) for y in B)

def walk(t, steps, budget=2000):
    root, kids, parent = number(t)
    node = (root, ())                # the root occurrence itself as an element
    bad = 0; n = 0
    for _ in range(steps):
        K = [(k, ()) for k in kids[node[0]]] + list(node[1])
        work = 0
        while len(K) >= 3 and work < budget:
            a, b, c = K[0], K[1], K[2]
            K = [(k, ()) for k in kids[a[0]]] + list(a[1]) + [c, (b[0], b[1] + (c,))] + K[3:]
            work += 1
        if len(K) >= 3 or not K:
            break                    # no hnf within budget (bottom) or leaf S
        child = K[0]
        P0 = pieces(node, collections.Counter()); P1 = pieces(child, collections.Counter())
        n += 1
        if not mul_less(P1, P0, parent):
            bad += 1
        node = child
    return n, bad

if __name__ == "__main__":
    NMAX = int(sys.argv[1]); STEPS = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    for nn in range(3, NMAX + 1):
        stat = collections.Counter(); ex = {}
        for t in trees(nn):
            fl = L[1][jc(t)[0]]
            if not Mm[1][jc(t)[1]]:
                continue
            n, bad = walk(t, STEPS)
            key = (fl, bad > 0)
            stat[key] += 1
            if key not in ex: ex[key] = show(t)
        print(f"n={nn}: (flag, some step not decreasing) -> count {dict(sorted(stat.items()))}; examples {ex}", flush=True)
