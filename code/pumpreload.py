"""Search for a reload in the head-style pump loop.

Round rule (verified for k <= 6, n <= 5): with X_k = S S X_{k-1} S over a base B0, the head run maps
T(k, n) = [S, X_k, S^n, SS, SS, r1, ...] to T(k-1, n+1). At k = 0 the base B0 runs. A RELOAD is a later list with prefix
[S, X_m(B0), S^p, SS, SS] with m >= 1 (the loop re-enters, over the same base). We search bases B0 (closed, <= BMAX leaves)
and n = 0..NMAX, STEPS head steps, tail r1 r2 r3 opaque (a branch that opens r_i is dead).
Usage: python pumpreload.py BMAX NMAX STEPS
"""
import sys
sys.setrecursionlimit(100000)
from symb import spine, show, trees
SS = ("S", "S")

def depth_over(t, base):
    """m if t = X_m(base) with X_j = S S X_{j-1} S, else None"""
    m = 0
    while t != base:
        if isinstance(t, tuple) and t[1] == "S" and isinstance(t[0], tuple) and t[0][0] == SS:
            t = t[0][1]; m += 1
        else:
            return None
    return m

def match(K, base):
    if len(K) < 4 or K[0] != "S": return None
    m = depth_over(K[1], base)
    if m is None or m < 1: return None
    p = 0; i = 2
    while i < len(K) and K[i] == "S": p += 1; i += 1
    if K[i:i + 2] != [SS, SS]: return None
    return (m, p)

def run(base, n, steps):
    K = ["S", base] + ["S"] * n + [SS, SS, "r1", "r2", "r3"]
    for s in range(1, steps + 1):
        if len(K) < 3: return ("hnf", s)
        a = K[0]
        h, aa = spine(a)
        if h != "S": return ("stuck", s)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        m = match(K, base)
        if m: return ("RELOAD", s, m)
        if len(K) > 4000: return ("long", s)
    return ("budget", steps)

if __name__ == "__main__":
    BMAX, NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    hits = []; stats = {}
    for nb in range(1, BMAX + 1):
        for base in trees(nb):
            outs = [run(base, n, STEPS) for n in range(NMAX + 1)]
            for o in outs: stats[o[0]] = stats.get(o[0], 0) + 1
            if any(o[0] == "RELOAD" for o in outs):
                hits.append((show(base), outs))
    print(stats)
    print("bases with a reload for some n:", len(hits))
    for h in hits[:25]: print("  ", h)
