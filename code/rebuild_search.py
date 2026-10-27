"""Search for a flat -> nest rebuild (the loophole left by the write-pass theorem) (main agent, frontier research).

Initial list [C, W_n, Z, S, w1, w2]: C closed code (<= CMAX leaves), W_n = S·S^n a comb holding n units, Z a seed nest
(X_1 or N_1 over base S(SS)(SS)), fuel S, opaque tape. In time windows we record (largest pure comb size, deepest pure
nest) among the top four entries. A run is flagged when the nest depth rises by >= 2 while the comb size falls by >= 2
over the same windows (units moving from flat into nesting).
Usage: python rebuild_search.py CMAX STEPS
"""
import sys
sys.setrecursionlimit(100000)
from symb import spine, show, trees
import growth_search as G
SS = ("S", "S")
B0 = (("S", SS), SS)

def comb(n):
    t = "S"
    for _ in range(n): t = (t, "S")
    return t

def comb_size(t):
    m = 0
    while isinstance(t, tuple) and t[1] == "S": t = t[0]; m += 1
    return m if t == "S" and m >= 1 else None

def run(C, n, fam, steps, windows=5):
    K = [C, comb(n), G.make(1, fam, 1, B0), "S", "w1", "w2"]
    wl = steps // windows
    cmax = [0] * windows; dmax = [0] * windows
    for s in range(steps):
        w = min(s // wl, windows - 1)
        for e in K[:4]:
            c = comb_size(e)
            if c is not None and c > cmax[w]: cmax[w] = c
            d = G.depth(e, fam, 1, B0)
            if d is not None and d > dmax[w]: dmax[w] = d
        if len(K) < 3: return ("hnf", cmax, dmax)
        a = K[0]; ha, aa = spine(a)
        if ha != "S": return ("stuck", cmax, dmax)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        if len(K) > 20000: return ("long", cmax, dmax)
    return ("ran", cmax, dmax)

if __name__ == "__main__":
    CMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
    codes = [t for m in range(1, CMAX + 1) for t in trees(m)]
    flagged = []; stats = {}
    for C in codes:
        for fam in ("X", "N"):
            for n in (4, 6, 8):
                how, cm, dm = run(C, n, fam, STEPS)
                stats[how] = stats.get(how, 0) + 1
                if dm[-1] >= dm[0] + 2 and cm[0] >= cm[-1] + 2:
                    flagged.append((show(C), fam, n, cm, dm, how))
    print(stats)
    print("flat->nest candidates:", len(flagged))
    for f in flagged[:30]: print("   ", f)
