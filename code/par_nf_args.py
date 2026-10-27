"""Theorem CA-par check with normal-form (non-atomic) arguments (main agent): random tree calls C, random normal-form
S-terms x, y (so x·y may be a redex), atomic tape; the parallel head machine must bring x·y to the front at pass T(C)."""
import sys, random
sys.setrecursionlimit(1000000)
import hc
from parallel_eval import step_fn
from waiting_nf import is_nf, seq
from sm_check import rand_term
P = step_fn(); rng = random.Random(5)
def rand_nf(n):
    while True:
        t = hc.from_tuple(rand_term(n, rng))
        if is_nf(t): return t
pool = [(hc.app(0, 0), 2)]; ok = bad = 0; redex_products = 0
for it in range(160):
    k = rng.randint(2, 4); As = [rng.choice(pool) for _ in range(k)]
    T = sum(t for _, t in As) + k
    if T > 1500: continue
    C = seq([a for a, _ in As]); pool.append((C, T))
    x, y = rand_nf(rng.randint(1, 9)), rand_nf(rng.randint(1, 9)); xy = hc.app(x, y)
    redex_products += not is_nf(xy)
    lst = [C, x, y, -3, -4, -5, -6]; got = None
    for n in range(T + 5):
        if lst[0] == xy: got = n; break
        a, b, c, rest = lst[0], lst[1], lst[2], lst[3:]
        args, h = hc.spine(a)
        if h != 0: break
        lst = args + [c, hc.app(b, c)] + [P(e) for e in rest]
    if got == T: ok += 1
    else: bad += 1; print("mismatch", T, got)
print(f"{ok + bad} tree calls with normal-form arguments under parallel evaluation: x·y at the front at pass T in {ok}, "
      f"mismatches {bad}; products x·y that were redexes: {redex_products}")
