"""Call algebra check (main agent): calls are SS and seq(A_1..A_k) = S·(S A_1 (S A_2 (... (S A_{k-1} (A_k S))))),
k >= 2, A_i calls. Claim: T(seq) = sum T(A_i) + k, x·y reaches the front, the tape is never touched.
Random compositions over a growing pool (seeded)."""
import random, sys
sys.setrecursionlimit(1000000)
from kary_check import run
def seq(As):
    t = (As[-1], "S")
    for A in reversed(As[:-1]): t = (("S", A), t)
    return ("S", t)
random.seed(7)
pool = [(("S", "S"), 2)]
bad = 0; n = 0
for it in range(400):
    k = random.randint(2, 4)
    As = [random.choice(pool[-12:] if random.random() < .5 else pool) for _ in range(k)]
    pred = sum(t for _, t in As) + k
    if pred > 200000: continue
    C = seq([a for a, _ in As])
    T, xy, touched = run(C, cap=pred + 10)
    n += 1
    if T != pred or not xy or touched: bad += 1; print("MISMATCH", k, [t for _, t in As], T, pred, xy, touched)
    pool.append((C, pred))
print(f"{n} random compositions tested, {bad} mismatches; largest T = {max(t for _, t in pool)}")
