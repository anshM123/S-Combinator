"""Search for a reload in the head-style iterator loop (main agent, round 6 side search).

Round: the head run of X_i X_m S w1 w2 w3 (X_j = S S X_{j-1} S^r over a common base B0) counts A = i down, each pass
adding r leaves S to the thunk; at A = 0 the base B0 is at the front applied to [S^{r i}, X_m, S]. A RELOAD is a later
front element of the form X_a · X_b · S · (anything) over the same base with a >= 1, b >= 1 (a new round starts).
We search closed bases B0 (<= BMAX leaves), small (i, m), and report the observed (i, m) -> (a, b) maps.
Usage: python hsreload.py BMAX R STEPS
"""
import sys
sys.setrecursionlimit(100000)
from symb import spine, show, trees
SS = ("S", "S")

def Xr(k, r, base):
    t = base
    for _ in range(k):
        t = (SS, t)
        for _ in range(r): t = (t, "S")
    return t

def depth(t, r, base):
    k = 0
    while t != base:
        u = t
        for _ in range(r):
            if isinstance(u, tuple) and u[1] == "S": u = u[0]
            else: return None
        if isinstance(u, tuple) and u[0] == SS: t = u[1]; k += 1
        else: return None
    return k

def round_start(f, r, base):
    """f = X_a X_b S ... ? return (a, b)"""
    args = []
    g = f
    while isinstance(g, tuple):
        a = depth(g, r, base)
        if a is not None and a >= 1:
            args.reverse()
            if len(args) >= 2 and args[1] == "S":
                b = depth(args[0], r, base)
                if b is not None and b >= 1: return (a, b)
            return None
        args.append(g[1]); g = g[0]
    return None

def run(base, r, i, m, steps):
    t = (((((Xr(i, r, base), Xr(m, r, base)), "S"), "w1"), "w2"), "w3")
    h, K = spine(t); K = list(K)
    for n in range(1, steps + 1):
        if len(K) < 3: return ("hnf", n)
        a = K[0]; ha, aa = spine(a)
        if ha != "S": return ("stuck", n)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        rs = round_start(K[0], r, base)
        if rs and n > 1: return ("ROUND", n, rs)
        if len(K) > 6000: return ("long", n)
    return ("budget", steps)

if __name__ == "__main__":
    BMAX, R, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    hits = []
    for nb in range(1, BMAX + 1):
        for base in trees(nb):
            res = {}
            for (i, m) in [(1, 1), (1, 2), (2, 2), (2, 3), (3, 2)]:
                res[(i, m)] = run(base, R, i, m, STEPS)
            rounds = {k: v[2] for k, v in res.items() if v[0] == "ROUND"}
            # ignore the trivial 'next pass' re-detections: a round start with a = i-1, b = m is just the countdown
            new = {k: v for k, v in rounds.items() if v != (k[0] - 1, k[1])}
            if new: hits.append((show(base), new, {k: v[0] for k, v in res.items()}))
    print("bases with a new-round start:", len(hits))
    for h in hits[:30]: print("  ", h)
