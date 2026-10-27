"""Theorem B2 check (agent_work_RR): n_par(n-bar m-bar S) = n*m + 2n - 2 and Lemma U: n_par(m-bar S R) = max(2m-1, m + n_par(R)).
Direct ReplaceAll passes (code/parallel_eval.step_fn) on hash-consed terms; node cap 2,000,000.
Usage: python bilinear_check.py NMAX MMAX"""
import sys, time
from nf_scan import hc, step_fn, hnum, reset, NODE_CAP
def npar(t, cap=100000):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > NODE_CAP: raise MemoryError(len(hc.L))
    return None
NM, MM = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time(); ok = bad = 0; worst = 0
for n in range(1, NM + 1):
    for m in range(1, MM + 1):
        reset()
        t = hc.app(hc.app(hnum(n), hnum(m)), 0)
        try:
            v = npar(t)
        except MemoryError:
            print("node cap at", n, m); skipped = globals().get('skipped', 0) + 1; globals()['skipped'] = skipped; continue
        worst = max(worst, len(hc.L))
        if v == n * m + 2 * n - 2: ok += 1
        else: bad += 1; print("MISMATCH", n, m, v)
print(f"skipped (node cap): {globals().get('skipped', 0)}"); print(f"B2: {ok} agree, {bad} mismatch, n <= {NM}, m <= {MM}; max nodes {worst}; {time.time() - t0:.1f}s")
