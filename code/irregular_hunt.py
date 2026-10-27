"""Targeted search for irregular head runs (main agent, 2026-10-26).
Every run proved so far is a loop, nested loop, counter or recursion of a fixed shape — opcode words of low Lempel–Ziv
complexity. This searches for the opposite: random S-terms (L leaves) and their mutants, scored by the LZ76 complexity
of the head run's opcode word over N steps, normalised by N / log2 N (about 1 for random words, near 0 for regular ones).
A small evolutionary loop keeps the most complex runs and mutates them (a random subterm replaced by a random small
term). Runs reaching a head normal form or whose list exceeds a size cap are dropped. Prints the top terms.
Usage: python irregular_hunt.py POP GENERATIONS STEPS SEED"""
import sys, random, math
sys.setrecursionlimit(1000000)
import hc

def lz76(w):
    """Lempel–Ziv (1976) complexity: number of phrases of the exhaustive history parsing (Kaspar–Schuster)"""
    n = len(w)
    if n == 0: return 0
    c, l, i, k, kmax = 1, 1, 0, 1, 1
    while True:
        if l + k > n: c += 1; break
        if w[i + k - 1] == w[l + k - 1]:
            k += 1
            if l + k > n: c += 1; break
        else:
            kmax = max(k, kmax); i += 1
            if i == l:
                c += 1; l += kmax
                if l + 1 > n: break
                i, k, kmax = 0, 1, 1
            else:
                k = 1
    return c

def rand_term(rng, leaves):
    if leaves == 1: return "S"
    k = rng.randint(1, leaves - 1)
    return (rand_term(rng, k), rand_term(rng, leaves - k))

def size(t): return 1 if t == "S" else size(t[0]) + size(t[1])

def mutate(rng, t):
    """replace a random subterm by a random term of 1..5 leaves"""
    if t == "S" or rng.random() < 0.25: return rand_term(rng, rng.randint(1, 5))
    return (mutate(rng, t[0]), t[1]) if rng.random() < 0.5 else (t[0], mutate(rng, t[1]))

def show(t):
    if t == "S": return "S"
    f, x = t; xs = show(x)
    return show(f) + (xs if x == "S" else "(" + xs + ")")

def run_word(t, N, cap=400_000):
    hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
    args, h = hc.spine(hc.from_tuple(t)); stk = args[::-1]; ops = []
    for n in range(N):
        if len(stk) < 3 or len(stk) > cap or len(hc.L) > 3_000_000: return None
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return "".join(chr(48 + min(o, 60)) for o in ops)

def score(t, N):
    w = run_word(t, N)
    if w is None: return None
    return lz76(w) / (N / math.log2(N))

if __name__ == "__main__":
    POP, GEN, N, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed); pop = []
    while len(pop) < POP:
        t = rand_term(rng, rng.randint(15, 40)); s = score(t, N)
        if s is not None: pop.append((s, t))
    for g in range(GEN):
        pop.sort(key=lambda x: -x[0]); elite = pop[:POP // 4]
        kids = []
        while len(kids) < POP - len(elite):
            parent = rng.choice(elite)[1]; child = mutate(rng, parent)
            if size(child) > 60: continue
            s = score(child, N)
            if s is not None: kids.append((s, child))
        pop = elite + kids
        best = max(pop, key=lambda x: x[0])
        print(f"generation {g}: best normalised LZ {best[0]:.4f}  median {sorted(p[0] for p in pop)[len(pop) // 2]:.4f}", flush=True)
    pop.sort(key=lambda x: -x[0])
    print("top runs:")
    seen = set()
    for s, t in pop:
        st = show(t)
        if st in seen: continue
        seen.add(st); print(f"  {s:.4f}  {st}")
        if len(seen) >= 15: break
