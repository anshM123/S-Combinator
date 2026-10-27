"""Exact check of the max-plus law (Lemma PJ, agent_work_P/LOG.md) on random instances, with direct ReplaceAll passes.
Instance: list [x, y, z] ++ R where x = P^w(x0) (x0 a random term that is not head-normal, w random), so the term is
S x y z R1 ... . Prediction (from Lemma LZ): let h = first internal time with P^h(x0) head-normal. Opening x costs one pass. Then
  * for 0 <= j <= max(0, h - w): list_j = spine(P^(w+j)(x0)) ++ [z?] ... more precisely, the whole term after j passes is
    S (spine(P^(w+j) x0)) z' ... only while spine(P^(w+j-1) x0) has >= 3 elements; at j* = max(0, h - w) the first
    len(spine(P^(max(w,h)) x0)) list elements are exactly spine(P^(max(w,h)) x0), followed by the aged rest.
  * under leftmost-outermost head steps, x0 opened unaged takes h_LO(x0) steps instead.
We check: list at pass j* starts with spine(P^max(w,h)(x0)) and the remaining elements equal P^{j*}(y), P^{j*}(z), ...
when j* > 0 (y, z are below the window only while x's run has >= 3 elements); plus the time formula max(T, b + h)."""
import sys, random
from ptools import *
sys.setrecursionlimit(100000)
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
def rand_term(leaves):
    if leaves == 1: return 0
    k = rng.randint(1, leaves - 1)
    return hc.app(rand_term(k), rand_term(leaves - k))
def iterate(t, n):
    for _ in range(n): t = P(t)
    return t
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
ok = bad = skipped = 0
for trial in range(N):
    x0 = rand_term(rng.randint(4, 12))
    # internal hnf time of x0 under passes
    h = None; t = x0
    for n in range(60):
        if is_hnf(t): h = n; break
        if size(t) > 5000: break
        t = P(t)
    if h is None or h == 0: skipped += 1; continue
    w = rng.randint(0, h + 3)
    x = iterate(x0, w)
    rest = [rand_term(rng.randint(1, 8)) for _ in range(rng.randint(2, 4))]
    term = build(0, [x] + rest)
    jstar = max(0, h - w)
    # opening x costs one pass: list_1 = spine(x) ++ [r2, r1.r2, r3, ...]; then x's own run continues for jstar passes
    u = iterate(term, 1 + jstar)
    args, hd = spine(u)
    target = spine(iterate(x0, max(w, h)))[0]
    good = hd == 0 and args[:len(target)] == target
    # r1, r2 sit in the window at pass 0 (not aged); r3, r4, ... age at pass 0 as well
    aged = [iterate(r, jstar) for r in [rest[1], hc.app(rest[0], rest[1])]] + [iterate(r, 1 + jstar) for r in rest[2:]]
    good = good and args[len(target):] == aged
    if good: ok += 1
    else:
        bad += 1
        print('MISMATCH', show(x0), 'w', w, 'h', h)
print(f"max-plus law: {ok} instances agree, {bad} mismatches, {skipped} skipped (x0 head-normal or no hnf within 60 passes)")
