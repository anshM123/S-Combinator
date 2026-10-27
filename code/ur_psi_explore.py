"""Orbits of the Φ-map Ψ of unique-redex runs (main agent, 2026-10-26).
Theorem UR-R: in the Φ-regime a unique-redex run is the map c -> Ψ(c) on its Φ-element (round machine of Lemma R′ with
registers (S c, S c); nothing below is read). This samples Φ-elements c directly — random normal forms whose left spine
ends with B = S(SSS)S, A = SSS, built bottom-up from random type-1 layers S x and type-2 layers S x t (t = S or S y) — and
iterates Ψ, recording per round the number m of type-1 steps and whether the last one is consecutive with the one before.
Each orbit is classified: dies (a round is not unique-redex or loses the Φ form), type A (m = 1 from some round on),
type II (m = 2 consecutive from some round on), or other. Usage: python ur_psi_explore.py SAMPLES ROUNDS SEED"""
import sys, random, collections
sys.setrecursionlimit(1000000)
import hc
from symb import parse

def rand_nf(rng, depth):
    """a random normal form of spine <= 2 with small depth"""
    if depth <= 0 or rng.random() < 0.3: return 0
    k = rng.choice((1, 2))
    r = 0
    for _ in range(k): r = hc.app(r, rand_nf(rng, depth - 1))
    return r

def rand_phi_element(rng, layers):
    B = hc.from_tuple(parse("S(SSS)S")); c = B
    for _ in range(layers):
        if rng.random() < 0.35: c = hc.app(0, c)                          # type-1 layer S c
        else:
            t = 0 if rng.random() < 0.3 else hc.app(0, rand_nf(rng, 3))     # t = S or S y
            c = hc.app(hc.app(0, c), t)                                     # type-2 layer S c t
    return c

def psi(c):
    """one Φ-round: (c', m, consecutive_last) or None if the round is not unique-redex or the successor is not Φ"""
    u, v, pushed = hc.app(0, c), hc.app(0, c), None
    x = c; types = []
    while x != 0:
        args, h = hc.spine(x)
        if len(args) == 1:
            u, v = v, hc.app(u, v); types.append(1)
        else:
            pushed = hc.app(u, v); u, v = args[1], v; types.append(2)
        if len(hc.spine(u)[0]) >= 2: return None
        x = args[0]
    if u != 0 or pushed != hc.app(0, v): return None
    ones = [i for i, ty in enumerate(types) if ty == 1]
    return v, len(ones), len(ones) >= 2 and ones[-1] == ones[-2] + 1

if __name__ == "__main__":
    n, R, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed); kinds = collections.Counter(); examples = {}
    for i in range(n):
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
        c = rand_phi_element(rng, rng.randint(1, 8)); c0 = c; hist = []
        for k in range(R):
            r = psi(c)
            if r is None: break
            c, m, cons = r; hist.append((m, cons))
        if len(hist) < R: kind = "dies"
        else:
            tail = hist[R // 2:]
            if all(h == (1, False) for h in tail): kind = "type A (m = 1)"
            elif all(h == (2, True) for h in tail): kind = "type II (m = 2, consecutive)"
            else: kind = "other: " + str(sorted(set(tail)))
        kinds[kind] += 1
        if kind not in examples: examples[kind] = hc.show(c0)
    for k, v in kinds.most_common(): print(f"{v:6d}  {k}   e.g. c0 = {examples[k][:80]}")
    print(f"other regimes: {sum(v for k, v in kinds.items() if k.startswith('other'))}")
