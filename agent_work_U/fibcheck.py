"""Check Lemma Fib: for t with >= 2 spine args and a NON-tower bottom Z (some right-spine multiplier of Z is not S),
the leftmost child of t.Z (if the head run ends) is Fw(Z, c0, K) where H(t) = S (tw K) c0, Fw 0 = Z, Fw 1 = c0 Z,
Fw (i+2) = Fw i . Fw (i+1)."""
import sys, random
from dm import *
from stackview import hnf
def tw(m):
    x = 0
    for _ in range(m): x = app(0, x)
    return x
def is_tower(z):
    while z != 0:
        if L[z] != 0: return False
        z = R[z]
    return True
def Fw(z, c0, K):
    a, b = z, app(c0, z)
    if K == 0: return a
    for _ in range(K - 1): a, b = b, app(a, b)
    return b
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rand_term(k), rand_term(n - k))
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); checked = 0; fib = 0; bad = 0; nohnf = 0
for it in range(N):
    m = mark()
    t = rand_term(random.randint(3, 14)); Z = rand_term(random.randint(2, 12))
    if len(spine(t)[0]) < 2 or is_tower(Z): truncate(m); continue
    u = app(t, Z)
    H = hnf(u, bud=3000)
    if H is None or len(H) != 2: nohnf += 1; truncate(m); continue
    ht = hnf(t, bud=3000)
    checked += 1
    ok = False
    if ht is not None and len(ht) == 2:
        x0, c0 = ht
        K = 0; x = x0
        while x != 0 and L[x] == 0: x = R[x]; K += 1
        if x == 0 and H[0] == Fw(Z, c0, K): ok = True; fib += 1
    if not ok:
        bad += 1
        if bad <= 5: print("COUNTEREXAMPLE?", show(t), "|", show(Z))
    truncate(m)
print("seed", sys.argv[1], "checked", checked, "fibonacci", fib, "bad", bad, "no hnf / budget", nohnf)
