"""Pass-through processes (agent_work_P): S-terms A whose own ReplaceAll run first reaches a head normal form of the form
S S c (spine [S, c]) at internal time h.  By Lemma PJ, in the list [A, r1, B, ...] the element B is opened right
after A's hnf, so the list computes a JOIN: B's hnf reaches the front at pass 3 + max(h_A, h_B) under ReplaceAll,
versus 3 + h_LO(A) + h_LO(B) under leftmost-outermost.  This scan lists all A <= L leaves with that shape and h >= 3,
with their parallel and leftmost-outermost hnf times."""
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
L = int(sys.argv[1]) if len(sys.argv) > 1 else 10
found = []
for n in range(1, L + 1):
    for A in terms(n):
        t = A; h = None
        for k in range(60):
            if is_hnf(t): h = k; break
            if size(t) > 50000: break
            t = P(t)
        if h is None or h < 3: continue
        a, hd = spine(t)
        if hd == 0 and len(a) == 2 and a[0] == 0:
            u = A; hl = None
            for k in range(5000):
                if is_hnf(u): hl = k; break
                u = head_step(u)
            found.append((h, hl, n, show(A), show(a[1])[:40]))
found.sort()
for f in found[-25:]: print(f)
print('count', len(found))
