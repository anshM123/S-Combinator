"""Disprover test: can a head run INCREASE the 'head-style depth' of a datum?

Data = subterms containing the opaque variable z (never opened: the run stops when z reaches the front).
A head-style frame around an occurrence of z is a spine position where the argument containing that occurrence is
directly followed by a closed argument (MODE 'adj') or followed anywhere later by a closed argument (MODE 'any'); the
whole list counts as one more spine (stack level). hs(z-occurrence) = number of frames on its path; HS(config) = max.
Head-style counters (agent U's P_k) have HS = 2k. Question: is HS(config) non-increasing along every head run?
Random initial configurations: random closed terms with z planted at random places. Reports the first increase found.
Usage: python hsdepth.py TRIALS STEPS SEED MODE
"""
import sys, random
sys.setrecursionlimit(100000)

def spine(t):
    args = []
    while isinstance(t, tuple):
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

def has_z(t, memo):
    if t == "z": return True
    if t == "S": return False
    k = id(t)
    if k not in memo: memo[k] = has_z(t[0], memo) or has_z(t[1], memo)
    return memo[k]

def frames_list(args, i, memo, mode):
    """1 if the element args[i] (contains z) is followed by a closed element"""
    if mode == "adj":
        return 1 if i + 1 < len(args) and not has_z(args[i + 1], memo) else 0
    return 1 if any(not has_z(a, memo) for a in args[i + 1:]) else 0

def hs_term(t, memo, mode, cache):
    """max frames over z-occurrences inside t (frames of t's own spine and below); -1 if no z"""
    if t == "z": return 0
    if t == "S": return -1
    k = id(t)
    if k in cache: return cache[k]
    h, args = spine(t)
    best = 0 if h == "z" else -1
    for i, a in enumerate(args):
        if has_z(a, memo):
            best = max(best, hs_term(a, memo, mode, cache) + frames_list(args, i, memo, mode))
    cache[k] = best
    return best

def HS(K, mode):
    memo, cache = {}, {}
    best = -1
    for i, e in enumerate(K):
        if has_z(e, memo):
            best = max(best, hs_term(e, memo, mode, cache) + frames_list(K, i, memo, mode))
    return best

def rand_term(n, rng):
    if n == 1: return "S"
    k = rng.randint(1, n - 1)
    return (rand_term(k, rng), rand_term(n - k, rng))

def plant(t, rng, p):
    """replace some leaves by z (probability p)"""
    if t == "S": return "z" if rng.random() < p else "S"
    return (plant(t[0], rng, p), plant(t[1], rng, p))

def run(K, steps, mode):
    h0 = HS(K, mode); hist = [h0]
    for n in range(steps):
        if len(K) < 3: return hist, "hnf", K
        a = K[0]
        ha, aa = spine(a)
        if ha != "S": return hist, "stuck", K
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        hist.append(HS(K, mode))
        if hist[-1] > max(hist[:-1]): return hist, "INCREASE", K
    return hist, "budget", K

if __name__ == "__main__":
    trials, steps, seed, mode = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    stat = {}
    for tr in range(trials):
        n = rng.randint(4, 14)
        m = rng.randint(3, 6)
        K = [plant(rand_term(rng.randint(1, n), rng), rng, rng.choice([0.0, 0.1, 0.25])) for _ in range(m)]
        if not any(has_z(e, {}) for e in K): continue
        hist, how, Kf = run(K, steps, mode)
        stat[how] = stat.get(how, 0) + 1
        if how == "INCREASE" and stat[how] <= 3:
            print("INCREASE at step", len(hist) - 1, "HS", hist[:len(hist)][-6:])
    print(mode, stat)
