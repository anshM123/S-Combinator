"""Growth detection with closed TAPES (main agent, frontier research).

Front node A · S^n · B · S over a closed tape [c1, c2, c3, c4] (followed by opaque w's), A = X_i, B = X_k head-style
over base S (so the zero test of A hands over to the flat comb iterator S·S^n·B·S -> S·S^(n-2)·B·S, and its exit runs
B with the tape as arguments), or over base S(SS)(SS). Tape constants: closed terms <= TMAX leaves (all 4-tuples from
a pool would be too many: we take tapes c c c c and c d c d). Flags runs whose deepest X- or N-nest inside the top four
entries keeps increasing.
Usage: python growth_tape.py TMAX STEPS
"""
import sys, itertools
sys.setrecursionlimit(100000)
from symb import spine, show, trees
import growth_search as G
SS = ("S", "S")

def run(b0, i, n, k, tape, steps, windows=6):
    A = G.make(i, "X", 1, b0); B = G.make(k, "X", 1, b0)
    t = A
    for _ in range(n): t = (t, "S")
    t = ((t, B), "S")
    K = [t] + list(tape) + ["w1", "w2"]
    wmax = [0] * windows; wlen = steps // windows
    memos = {"N": {}, "X": {}}
    for s in range(steps):
        w = min(s // wlen, windows - 1)
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
    TMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
    pool = [t for m in range(1, TMAX + 1) for t in trees(m)]
    tapes = [(c, c, c, c) for c in pool] + [(c, d, c, d) for c in pool for d in pool if c != d]
    stats = {}; flagged = []
    for b0 in ("S", (("S", SS), SS)):
        for tape in tapes:
            for (i, n, k) in ((2, 0, 2), (3, 1, 2)):
                how, w = run(b0, i, n, k, tape, STEPS)
                stats[how] = stats.get(how, 0) + 1
                if how == "ran" and w[-1] >= max(w[:2]) + 2 and w[-1] > w[-3] and all(w[j] <= w[j + 1] for j in range(len(w) - 3, len(w) - 1)):
                    flagged.append((show(b0) if b0 != "S" else "S", [show(x) for x in tape], (i, n, k), w))
    print(stats)
    print("GROWING runs:", len(flagged))
    for f in flagged[:30]: print("   ", f)
