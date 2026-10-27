"""Theorem CA-par check with normal-form arguments whose product x·y is a NORMALISING redex (main agent): random tree
calls C (T <= 800), random normal-form x with two spine arguments (so x·y is a redex) and y, such that x·y normalises
within 20 passes; atomic tape; the parallel head machine must bring x·y to the front at pass T(C). Runs whose DAG grows
past a limit are skipped (counted)."""
import sys, random
sys.setrecursionlimit(1000000)
import hc
from parallel_eval import step_fn
from waiting_nf import is_nf, seq
from sm_check import rand_term
P = step_fn(); rng = random.Random(5)
def rand_nf(n, need_two=False):
    for _ in range(1000):
        t = hc.from_tuple(rand_term(n, rng))
        if is_nf(t) and (not need_two or len(hc.spine(t)[0]) == 2): return t
    return None
def normalises(t, k=20):
    for _ in range(k):
        u = P(t)
        if u == t: return True
        t = u
    return False
pool = [(hc.app(0, 0), 2)]; ok = bad = skipped = 0
for it in range(400):
    k = rng.randint(2, 4); As = [rng.choice(pool) for _ in range(k)]
    T = sum(t for _, t in As) + k
    if T > 800: continue
    C = seq([a for a, _ in As]); pool.append((C, T))
    x = rand_nf(rng.randint(3, 8), need_two=True); y = rand_nf(rng.randint(1, 6))
    if x is None or y is None: continue
    xy = hc.app(x, y)
    if is_nf(xy) or not normalises(xy): continue
    lst = [C, x, y, -3, -4, -5, -6]; got = None; start = len(hc.L)
    for n in range(T + 5):
        if lst[0] == xy: got = n; break
        a, b, c, rest = lst[0], lst[1], lst[2], lst[3:]
        args, h = hc.spine(a)
        if h != 0: break
        lst = args + [c, hc.app(b, c)] + [P(e) for e in rest]
        if len(hc.L) - start > 3_000_000: got = "skip"; break
    if got == "skip": skipped += 1
    elif got == T: ok += 1
    else: bad += 1; print("mismatch: T =", T, "got", got)
    if (ok + bad + skipped) % 20 == 0 and ok + bad + skipped: print(f"  {ok} ok, {bad} mismatches, {skipped} skipped", flush=True)
print(f"tree calls with normal-form arguments whose product is a normalising redex: x·y at the front at pass T in {ok}, "
      f"mismatches {bad}, skipped (memory) {skipped}")
