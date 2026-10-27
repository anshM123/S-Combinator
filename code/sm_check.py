"""Random exact test of Lemma SM (supply monotonicity), far beyond the structured census.

Random one-hole context L (2..LMAX leaves, hole p opaque), random closed body B (1..BMAX leaves), supply n = 0..NMAX,
opaque tape. Run from [L[p]·S^n·B·S, w1, w2, w3, w4]; whenever the FRONT element equals p·S^m·B·S exactly (p never
opened), record m. Lemma SM claims m >= n. Also records how often the form is reached and the observed m - n.
Usage: python sm_check.py TRIALS LMAX BMAX NMAX STEPS SEED
"""
import sys, random, collections
sys.setrecursionlimit(100000)
from symb import spine

def rand_term(n, rng):
    if n == 1: return "S"
    k = rng.randint(1, n - 1)
    return (rand_term(k, rng), rand_term(n - k, rng))

def rand_ctx(n, rng):
    if n == 1: return "p"
    k = rng.randint(1, n - 1)
    if rng.random() < 0.5: return (rand_ctx(k, rng), rand_term(n - k, rng))
    return (rand_term(k, rng), rand_ctx(n - k, rng))

def node(h, n, B):
    t = h
    for _ in range(n): t = (t, "S")
    return ((t, B), "S")

def target_m(f, B):
    if not (isinstance(f, tuple) and f[1] == "S"): return None
    g = f[0]
    if not (isinstance(g, tuple) and g[1] == B): return None
    g = g[0]; m = 0
    while isinstance(g, tuple) and g[1] == "S": g = g[0]; m += 1
    return m if g == "p" else None

if __name__ == "__main__":
    T, LMAX, BMAX, NMAX, STEPS, SEED = (int(x) for x in sys.argv[1:7])
    rng = random.Random(SEED)
    reached = 0; viol = []; deltas = collections.Counter()
    for tr in range(T):
        L = rand_ctx(rng.randint(2, LMAX), rng)
        B = rand_term(rng.randint(1, BMAX), rng)
        n = rng.randint(0, NMAX)
        K = [node(L, n, B), "w1", "w2", "w3", "w4"]
        for s in range(STEPS):
            m = target_m(K[0], B)
            if m is not None and s > 0:
                reached += 1; deltas[m - n] += 1
                if m < n: viol.append((L, B, n, m))
                break
            if len(K) < 3: break
            a = K[0]; ha, aa = spine(a)
            if ha != "S": break
            K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
    print(f"trials {T}; next-node form reached {reached} times; violations of m >= n: {len(viol)}")
    print("observed m - n:", dict(sorted(deltas.items())))
    for v in viol[:5]: print("  VIOLATION", v)
