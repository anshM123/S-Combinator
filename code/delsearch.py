"""Can one Böhm-tree step delete an unbounded suffix after a marker, keeping the prefix?
Node: S C S^k m S^j E. Accept if a fixed component index and fixed prefix/suffix give args = P ++ S^k ++ Q for all
k in 1..4, j in 1..4 (the j trailing S's and the marker are gone). Also report 'keep-suffix' variants (S^j kept)."""
import sys
from symb import *
G = [t for n in range(1, 6) for t in trees(n)]
def comps_of(t):
    r = hnf(t, budget=4 * size(t) + 200)
    return r[1] if r[0] == "hnf" else None
cases = [(k, j) for k in range(1, 5) for j in range(1, 5)]
def accept(C, m, E, keep):
    sol = None
    for (k, j) in cases:
        w = ["S"] * k + [m] + ["S"] * j
        tgt = ["S"] * (j if keep else k)
        cs = comps_of(app("S", C, *w, E))
        if cs is None: return False
        opts = set()
        for idx, comp in enumerate(cs):
            _, args = spine(comp)
            n = len(tgt)
            for s0 in range(0, len(args) - n + 1):
                if args[s0:s0 + n] == tgt:
                    pre, suf = tuple(args[:s0]), tuple(args[s0 + n:])
                    # prefix/suffix must not contain bare S-runs that could absorb the count ambiguity
                    opts.add((idx, pre, suf))
        sol = opts if sol is None else (sol & opts)
        if not sol: return False
    return bool(sol)
hits = {True: 0, False: 0}; tested = 0
for m in G:
    if m == "S": continue
    for C in G:
        for E in G:
            tested += 1
            for keep in (False, True):
                if accept(C, m, E, keep):
                    hits[keep] += 1
                    if hits[keep] <= 5:
                        print(("KEEP-SUFFIX" if keep else "DELETE-SUFFIX"), "m=%s C=%s E=%s" % (show(m), show(C), show(E))); sys.stdout.flush()
print("tested", tested, " delete-suffix gadgets:", hits[False], " keep-suffix (delete-prefix) gadgets:", hits[True])
