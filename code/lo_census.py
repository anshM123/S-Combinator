"""LO census: where does leftmost-outermost evaluation of every S-term up to NMAX leaves end, and what does it do there?

For each term: if it normalises (bounded check), skip. Otherwise follow LO through the Böhm tree (descend into the first
non-normalising hnf component, lo_bt.py logic) until a node WITHOUT hnf is reached (an infinite head run) or the depth
budget runs out (a long/infinite Böhm-tree path). Distinct hnf-free endpoints are then classified by their head runs
(factor complexity + affine-periodic blocks/gaps, as in cxclassify.py, fixed version).
Usage: python lo_census.py NMAX DEPTH STEPS
"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import trees, show, hnf
from lo_bt import cls, MF, normalises
from factorcx import opcodes, pcx
from cxclassify import blocks_of, affine_periodic

def endpoint(t, depth):
    u = t
    for lvl in range(depth):
        if not MF[cls(u)]: return ("bottom", u, lvl)
        r = hnf(u, 20000)
        if r[0] != "hnf": return ("budget", u, lvl)
        nxt = None
        for x in r[1]:
            if not normalises(x): nxt = x; break
        if nxt is None: return ("normal", None, lvl)
        u = nxt
    return ("deep", u, depth)

def classify(u, steps):
    seq = opcodes(u, steps)
    if seq is None: return "hnf?"
    s = seq[steps // 3:]
    ps = [pcx(s, m) for m in (8, 16, 32, 64)]
    if ps[-1] <= ps[0] * 1.05 or (ps[3] <= 2.5 * ps[2] and ps[2] <= 2.5 * ps[1]): return "bounded/linear"
    best = None
    for op in range(4):
        b = blocks_of(seq, op)
        if b and (best is None or max(b) > max(best[1])): best = (op, b)
    if best is not None and affine_periodic(best[1]): return "one affine counter"
    for op in range(4):
        pos = [i for i, x in enumerate(seq) if x == op]
        g = [b - a for a, b in zip(pos, pos[1:])]
        if len(g) >= 12 and affine_periodic(g + [0]): return "one affine counter (gaps)"
    return "OTHER"

if __name__ == "__main__":
    NMAX, DEPTH, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    kinds = collections.Counter(); ends = {}; others = []
    for n in range(1, NMAX + 1):
        for t in trees(n):
            if normalises(t): kinds["normalises"] += 1; continue
            how, u, lvl = endpoint(t, DEPTH)
            kinds[how] += 1
            if how == "bottom": ends.setdefault(u, show(t))
    print("terms:", dict(kinds), "| distinct hnf-free endpoints:", len(ends))
    ck = collections.Counter()
    for u, origin in ends.items():
        c = classify(u, STEPS)
        ck[c] += 1
        if c == "OTHER" and len(others) < 15: others.append((show(u), "from", origin))
    print("endpoint head runs:", dict(ck))
    for o in others: print("   OTHER:", o)
