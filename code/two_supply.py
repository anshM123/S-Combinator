"""Can a pass move units between two flat supplies? (main agent, frontier research)

Front node H · S^n · M · S^m · B · S (H = S, the flat iterator head, or a head-style nest over base S), marker M closed
(<= MMAX leaves), B a nest, opaque tape. Run until the front element again has the shape H' · S^n' · M · S^m' · B · S
with H' in {S} or a head-style nest, and record (n, m) -> (n', m'). Reports markers giving a TRANSFER (n decreases while
m increases) for all tested n, m.
Usage: python two_supply.py MMAX STEPS
"""
import sys, collections
sys.setrecursionlimit(100000)
from symb import spine, show, trees
SS = ("S", "S")

def Xs(k):
    t = "S"
    for _ in range(k): t = ((SS, t), "S")
    return t

def build(H, n, M, m, Bt):
    t = H
    for _ in range(n): t = (t, "S")
    t = (t, M)
    for _ in range(m): t = (t, "S")
    return ((t, Bt), "S")

def parse(f, M, Bt):
    """f = H · S^n · M · S^m · B · S with H = S (flat) -> ('flat', n, m) """
    if not (isinstance(f, tuple) and f[1] == "S"): return None
    g = f[0]
    if not (isinstance(g, tuple) and g[1] == Bt): return None
    g = g[0]; m = 0
    while isinstance(g, tuple) and g[1] == "S": g = g[0]; m += 1
    if not (isinstance(g, tuple) and g[1] == M): return None
    g = g[0]; n = 0
    while isinstance(g, tuple) and g[1] == "S": g = g[0]; n += 1
    if g == "S": return ("flat", n, m)
    return None

def step_from(n, m, M, Bt, steps):
    K = [build("S", n, M, m, Bt), "w1", "w2", "w3"]
    for s in range(1, steps):
        a = K[0]; ha, aa = spine(a)
        if ha != "S": return ("stuck", s)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        p = parse(K[0], M, Bt)
        if p: return (p[1], p[2], s)
    return ("budget",)

if __name__ == "__main__":
    MMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
    Bt = Xs(2)
    kinds = collections.Counter(); ex = {}
    for nm in range(1, MMAX + 1):
        for M in trees(nm):
            res = {}
            for n in range(0, 7):
                for m in range(0, 4):
                    r = step_from(n, m, M, Bt, STEPS)
                    if len(r) == 3: res[(n, m)] = (r[0] - n, r[1] - m)
            if not res: continue
            effects = collections.Counter(res.values())
            key = tuple(sorted(effects))
            kinds[key] += 1
            ex.setdefault(key, (show(M), dict(list(res.items())[:6])))
    for key, c in kinds.most_common(20):
        print(f"{c:4d} markers, effects (dn, dm) seen: {key}   e.g. M = {ex[key][0]}  {ex[key][1]}")
