"""Check of Proposition MW(a) (main agent, 2026-10-26): every S-step t -> u (any redex, any position) satisfies
|u| = |t| + |z| - 1 >= |t| (z = third argument of the contracted redex), and when z = S the total leaf depth D drops by
exactly |x| >= 1 — so (|t|, -D(t)) increases strictly in lexicographic order and the multiway graph of every term is acyclic.
Exhaustive over all terms with <= NMAX leaves and all their one-step reducts, plus random larger terms.
Usage: python multiway_check.py NMAX NRANDOM"""
import sys, random
sys.setrecursionlimit(100000)
from symb import trees

def size(t): return 1 if t == "S" else size(t[0]) + size(t[1])
def D(t, d=0): return d if t == "S" else D(t[0], d + 1) + D(t[1], d + 1)

def steps(t):
    """all one-step reducts with the contracted redex's (x, z)"""
    out = []
    if t != "S":
        f, z = t
        if f != "S" and f[0] != "S" and f[0][0] == "S":          # t = S x y z
            x, y = f[0][1], f[1]
            out.append((((x, z), (y, z)), x, z))
        for u, x_, z_ in steps(f): out.append(((u, z), x_, z_))
        for u, x_, z_ in steps(z): out.append(((f, u), x_, z_))
    return out

def check(t):
    st, dt = size(t), D(t); bad = 0; n = 0
    for u, x, z in steps(t):
        n += 1; su, du = size(u), D(u)
        if su != st + size(z) - 1: bad += 1
        if z == "S" and du - dt != -size(x): bad += 1
        if not (su > st or (su == st and du < dt)): bad += 1
    return n, bad

def rand_term(n):
    if n == 1: return "S"
    k = random.randint(1, n - 1)
    return (rand_term(k), rand_term(n - k))

if __name__ == "__main__":
    NMAX, NR = int(sys.argv[1]), int(sys.argv[2])
    tot = bad = terms = 0
    for n in range(1, NMAX + 1):
        for t in trees(n):
            a, b = check(t); tot += a; bad += b; terms += 1
    random.seed(7)
    for _ in range(NR):
        t = rand_term(random.randint(13, 60)); a, b = check(t); tot += a; bad += b; terms += 1
    print(f"{terms} terms, {tot} one-step reductions checked: violations {bad}")
