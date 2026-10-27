"""Can one Böhm-tree step move a marker X one position right in a word of S's?
Node: S C w1..wm E, w = S^i X S^j (i>=0, j>=1). Accept if a fixed component index k and fixed closed prefix/suffix
lengths give args = P ++ (S^(i+1) X S^(j-1)) ++ Q for all i, j with 3 <= m <= 6 (P, Q fixed lists)."""
import sys, itertools
from symb import *
G = [t for n in range(1, 6) for t in trees(n)]
def comps_of(t):
    r = hnf(t, budget=4 * size(t) + 200)
    return r[1] if r[0] == "hnf" else None
cases = [(i, m - i - 1) for m in range(3, 7) for i in range(0, m - 1)]
def accept(C, X, E):
    sol = None
    for (i, j) in cases:
        w = ["S"] * i + [X] + ["S"] * j
        tgt = ["S"] * (i + 1) + [X] + ["S"] * (j - 1)
        cs = comps_of(app("S", C, *w, E))
        if cs is None: return False
        opts = set()
        for k, comp in enumerate(cs):
            _, args = spine(comp)
            n = len(tgt)
            for s in range(0, len(args) - n + 1):
                if args[s:s + n] == tgt:
                    opts.add((k, tuple(args[:s]), tuple(args[s + n:])))
        sol = opts if sol is None else (sol & opts)
        if not sol: return False
    return bool(sol)
hits = 0; tested = 0
for X in G:
    if X == "S": continue
    for C in G:
        for E in G:
            tested += 1
            if accept(C, X, E):
                hits += 1; print("SHIFT FOUND X=%s C=%s E=%s" % (show(X), show(C), show(E))); sys.stdout.flush()
print("tested", tested, "shift gadgets found", hits)
