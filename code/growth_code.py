"""Template-free growth detection with closed control code in front (main agent, frontier research).

Initial term C · A · B · F · w1 w2 w3: C closed (<= CMAX leaves), A = nest_i, B = nest_k over a common base b0
(<= BMAX leaves) from families N (SS-nests) or X (head-style, r = 1), F = S. Flags runs in which the deepest nest
(either family) occurring anywhere inside the top 4 list entries keeps increasing across time windows.
Usage: python growth_code.py CMAX BMAX STEPS
"""
import sys, itertools
sys.setrecursionlimit(100000)
from symb import spine, show, trees
import growth_search as G

def run(C, b0, famA, famB, i, k, steps, windows=6):
    t = (((((((C, G.make(i, famA, 1, b0)), G.make(k, famB, 1, b0)), "S"), "w1"), "w2"), "w3"))
    h, K = spine(t); K = list(K)
    wmax = [0] * windows; wlen = steps // windows
    memos = {"N": {}, "X": {}}
    for n in range(steps):
        w = min(n // wlen, windows - 1)
        for e in K[:4]:
            for f in ("N", "X"):
                d = G.maxd(e, f, 1, b0, memos[f])
                if d > wmax[w]: wmax[w] = d
        if len(K) < 3: return ("hnf", wmax)
        a = K[0]; ha, aa = spine(a)
        if ha != "S": return ("stuck", wmax)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        if len(K) > 20000: return ("long", wmax)
    return ("ran", wmax)

if __name__ == "__main__":
    CMAX, BMAX, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    codes = [t for n in range(1, CMAX + 1) for t in trees(n)]
    bases = [t for n in range(1, BMAX + 1) for t in trees(n)]
    flagged = []; stats = {}
    for C in codes:
        for b0 in bases:
            for famA, famB in (("N", "N"), ("X", "X"), ("X", "N"), ("N", "X")):
                for (i, k) in ((2, 1), (3, 2)):
                    how, w = run(C, b0, famA, famB, i, k, STEPS)
                    stats[how] = stats.get(how, 0) + 1
                    if how == "ran" and w[-1] >= max(w[:2]) + 2 and w[-1] > w[-3] and all(w[j] <= w[j + 1] for j in range(len(w) - 3, len(w) - 1)):
                        flagged.append((show(C), show(b0), famA + famB, (i, k), w))
    print(stats)
    print("GROWING runs:", len(flagged))
    seen = set()
    for f in flagged:
        key = (f[0], f[1], f[2])
        if key in seen: continue
        seen.add(key); print("   ", f)
        if len(seen) >= 40: break
