"""Clock-channel capacity (agent_work_P, 2026-10-27).  By Lemma PJ (MACHINE-CHECKED, lean/ParTime.lean `lemmaPJ`), a
waiting element W opened at age w delivers spine(P^max(w,h)(W)) (h = first head-normal time of W's own ReplaceAll run)
and nothing else depends on w except the delivery time 1 + max(T, b + h).  So the information a clock can carry is the
number of distinct delivered contents D(w), w = 0, 1, 2, ...
Classes, for every S-term W with at most L leaves (direct passes, size cap, horizon K):
  N  : W reaches its normal form at internal time N(W): D(w) is constant for w >= N(W) -> at most N(W)+1 values (saturates)
  H  : W reaches a head normal form but not a normal form within K passes (components keep evolving): D(w) may change forever
  U  : no head normal form within K passes (opening W hands the head to W's own run, shifted by w)
  ?  : size cap hit before a verdict
Usage: python clock_capacity.py L K CAP"""
import sys
from ptools import *
def terms(n, memo={}):
    if n in memo: return memo[n]
    if n == 1: r = [0]
    else:
        r = []
        for k in range(1, n):
            for a in terms(k):
                for b in terms(n - k): r.append(hc.app(a, b))
    memo[n] = r; return r
Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
K = int(sys.argv[2]) if len(sys.argv) > 2 else 40
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
from collections import Counter
tot = Counter(); maxN = 0; distinctH = []
for L in range(1, Lmax + 1):
    cnt = Counter()
    for W in terms(L):
        t = W; h = None; verdict = None; contents = []
        for n in range(K + 1):
            if h is None and is_hnf(t): h = n
            if is_normal(t): verdict = 'N'; maxN = max(maxN, n); break
            if size(t) > CAP: verdict = '?'; break
            if h is not None: contents.append(tuple(spine(t)[0]))
            t = P(t)
        if verdict is None: verdict = 'U' if h is None else 'H'
        if verdict == 'H': distinctH.append(len(set(contents)))
        cnt[verdict] += 1
    tot.update(cnt)
    print(f"leaves {L}: {dict(cnt)}", flush=True)
print(f"total <= {Lmax} leaves: {dict(tot)}; largest normalisation time among class N: {maxN}")
if distinctH: print(f"class H: distinct delivered contents within horizon K={K}: min {min(distinctH)}, max {max(distinctH)}")

# refine the '?' class with the leftmost-outermost head run (head steps only), which decides hnf existence in the limit
if len(sys.argv) > 4:
    HC = int(sys.argv[4])
    ref = Counter()
    for L in range(1, Lmax + 1):
        for W in terms(L):
            t = W; verdict = None
            for n in range(K + 1):
                if is_normal(t): verdict = 'N'; break
                if size(t) > CAP: verdict = '?'; break
                t = P(t)
            if verdict != '?': continue
            u = W; got = None
            for n in range(HC):
                if is_hnf(u): got = n; break
                if size(u) > 10 ** 6: break
                u = head_step(u)
            ref['hnf (head run ends)' if got is not None else 'no hnf within %d head steps' % HC] += 1
    print("refinement of '?':", dict(ref))
