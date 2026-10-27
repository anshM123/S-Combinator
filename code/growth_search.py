"""Template-free growth detection for full re-execution designs (main agent, frontier research).

Initial term: A · B · F · w1 w2 w3, where A = X_i and B = X_k are head-style nests over a common base b0
(X_j = S S X_{j-1} S^r) or SS-nests N_j = SS·N_{j-1} over b0, F = S (fuel), w's opaque. We run STEPS head steps and, in
windows, record the largest pure nest (over b0, of the chosen family) that appears among the top TOP list entries.
A run is flagged GROWING if the late maximum exceeds the early maximum by >= 2 and keeps increasing across windows —
i.e. a counter in the active region grows without bound, whatever the loop's shape. Sanity check: the sawtooth
(N-nests over S(SS)(SS)) must be flagged.
Usage: python growth_search.py BMAX STEPS FAMILY R   (FAMILY = X or N)
"""
import sys
sys.setrecursionlimit(100000)
from symb import spine, show, trees
SS = ("S", "S")

def make(k, fam, r, b0):
    t = b0
    for _ in range(k):
        if fam == "N": t = (SS, t)
        else:
            t = (SS, t)
            for _ in range(r): t = (t, "S")
    return t

def depth(t, fam, r, b0, cap=10**6):
    d = 0
    while t != b0:
        if fam == "N":
            if isinstance(t, tuple) and t[0] == SS: t = t[1]; d += 1
            else: return None
        else:
            u = t
            for _ in range(r):
                if isinstance(u, tuple) and u[1] == "S": u = u[0]
                else: return None
            if isinstance(u, tuple) and u[0] == SS: t = u[1]; d += 1
            else: return None
        if d > cap: return None
    return d

def maxd(t, f, r, b0, memo):
    """deepest pure nest (family f over b0) occurring anywhere inside t (DAG-memoised)"""
    k = id(t)
    hit = memo.get(k)
    if hit is not None and hit[0] is t: return hit[1]      # object stored: a recycled id cannot return a stale value
    d = depth(t, f, r, b0) or 0
    if isinstance(t, tuple):
        d = max(d, maxd(t[0], f, r, b0, memo), maxd(t[1], f, r, b0, memo))
    memo[k] = (t, d)
    return d

DEEP = False

def run(b0, fam, r, i, k, steps, top=4, windows=8):
    famA, famB = (fam[0], fam[1]) if len(fam) == 2 else (fam, fam)
    t = (((((make(i, famA, r, b0), make(k, famB, r, b0)), "S"), "w1"), "w2"), "w3")
    h, K = spine(t); K = list(K)
    wmax = [0] * windows; wlen = steps // windows
    memos = {f: {} for f in set(fam)}
    for n in range(steps):
        for e in K[:top]:
            for f in set(fam):
                d = maxd(e, f, r, b0, memos[f]) if DEEP else depth(e, f, r, b0)
                if d is not None and d > wmax[min(n // wlen, windows - 1)]:
                    wmax[min(n // wlen, windows - 1)] = d
        if len(K) < 3: return ("hnf", n, wmax)
        a = K[0]; ha, aa = spine(a)
        if ha != "S": return ("stuck", n, wmax)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        if len(K) > 20000: return ("long", n, wmax)
    return ("ran", steps, wmax)

if __name__ == "__main__":
    BMAX, STEPS, FAM, R = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    DEEP = len(sys.argv) > 5 and sys.argv[5] == "deep"
    flagged = []; stats = {}
    for nb in range(1, BMAX + 1):
        for b0 in trees(nb):
            for (i, k) in [(2, 1), (2, 3), (3, 2)]:
                how, n, w = run(b0, FAM, R, i, k, STEPS)
                stats[how] = stats.get(how, 0) + 1
                late, early = max(w[-3:]), max(w[:2])
                incr = all(w[j] <= w[j + 1] for j in range(len(w) - 4, len(w) - 1))
                if how == "ran" and late >= early + 2 and incr and w[-1] > w[-4]:
                    flagged.append((show(b0), (i, k), w))
    print(FAM, "r =", R, stats)
    print("GROWING runs:", len(flagged))
    for f in flagged[:30]: print("   ", f)
