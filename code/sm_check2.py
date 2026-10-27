"""Lemma SM with B tracked by identity: B is a MARKED occurrence ('M','B',term) — opening it exposes term's spine
(corw_check semantics) — so a lookalike built from supply leaves cannot be mistaken for B. Supply leaves are plain S.
Usage: python sm_check2.py TRIALS LMAX BMAX NMAX STEPS SEED"""
import sys, random, collections
sys.setrecursionlimit(100000)
from corw_check import is_mark, open_top, full_spine
from sm_check import rand_term, rand_ctx

def node(h, n, Bm):
    t = h
    for _ in range(n): t = (t, "S")
    return ((t, Bm), "S")

def target_m(f):
    if not (isinstance(f, tuple) and not is_mark(f) and f[1] == "S"): return None
    g = f[0]
    if not (isinstance(g, tuple) and not is_mark(g) and is_mark(g[1]) and g[1][1] == "B"): return None
    g = g[0]; m = 0
    while isinstance(g, tuple) and not is_mark(g) and g[1] == "S": g = g[0]; m += 1
    return m if g == "p" else None

if __name__ == "__main__":
    T, LMAX, BMAX, NMAX, STEPS, SEED = (int(x) for x in sys.argv[1:7])
    rng = random.Random(SEED)
    reached = 0; viol = []; deltas = collections.Counter()
    for tr in range(T):
        L = rand_ctx(rng.randint(2, LMAX), rng)
        Bm = ("M", "B", rand_term(rng.randint(1, BMAX), rng))
        n = rng.randint(0, NMAX)
        K = [node(L, n, Bm), "w1", "w2", "w3", "w4"]
        for s in range(STEPS):
            m = target_m(K[0])
            if m is not None and s > 0:
                reached += 1; deltas[m - n] += 1
                if m < n: viol.append((L, Bm[2], n, m))
                break
            if len(K) < 3: break
            h, _ = full_spine(K[0])
            if h != "S": break                      # p (or a tape variable) at the head: stop
            K = open_top(K[0]) + [K[2], (K[1], K[2])] + K[3:]
    print(f"trials {T}; marked next-node form reached {reached}; violations of m >= n: {len(viol)}")
    print("observed m - n:", dict(sorted(deltas.items())))
    for v in viol[:6]: print("  VIOLATION", v)
