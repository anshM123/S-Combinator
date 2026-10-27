"""Write-free two-parameter durations (agent_work_P, exploratory).  Theorem RR needs race processes whose durations are
non-separable in two parameters.  Writes (closed code applied to data) are what the barriers restrict; terms whose head
is a datum ('data in control', data applied to data and to closed material) need no write.  Here N = n-bar, M = m-bar
(S-numerals: 1 = SS, k+1 = SS(k)), A, B, C range over small closed terms, and we compute the leftmost-outermost
head-normalisation time T(n, m) of each write-free template for n, m = 1..6 and test separability:
T(n,m) - T(n,1) - T(1,m) + T(1,1) = 0 for all n, m  <=>  separable.  Prints the non-separable templates found."""
import sys, itertools
from ptools import *
def numeral(k):
    t = hc.app(0, 0)
    for _ in range(k - 1): t = app(0, 0, t)
    return t
def terms(n, memo={}):
    if n in memo: return memo[n]
    if n == 1: r = [0]
    else:
        r = []
        for k in range(1, n):
            for a in terms(k):
                for b in terms(n - k): r.append(hc.app(a, b))
    memo[n] = r; return r
closed = [t for n in range(1, 4) for t in terms(n)]
templates = {
  'N M A B':     lambda N, M, A, B: app(N, M, A, B),
  'M N A B':     lambda N, M, A, B: app(M, N, A, B),
  'N A M B':     lambda N, M, A, B: app(N, A, M, B),
  'N (M A) B':   lambda N, M, A, B: app(N, app(M, A), B),
  'N A (M B)':   lambda N, M, A, B: app(N, A, app(M, B)),
  'N (M A B) A': lambda N, M, A, B: app(N, app(M, A, B), A),
  'N M A B A':   lambda N, M, A, B: app(N, M, A, B, A),
  'N (M A) B A': lambda N, M, A, B: app(N, app(M, A), B, A),
}
class MemoryGuard(Exception):
    pass
NODE_LIMIT = 2_000_000                     # hash-cons table limit (memory guard; the first run without it used 15 GB)
def hlo(t, cap=3000, maxsize=20000):
    for k in range(cap):
        if is_hnf(t): return k
        if size(t) > maxsize: return None
        if len(hc.L) > NODE_LIMIT: raise MemoryGuard()
        t = head_step(t)
    return None
K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
found = 0
try:
  for name, f in templates.items():
      for A in closed:
          for B in closed:
              Tm = {}
              ok = True
              for n in range(1, K + 1):
                  for m in range(1, K + 1):
                      v = hlo(f(numeral(n), numeral(m), A, B))
                      if v is None: ok = False; break
                      Tm[n, m] = v
                  if not ok: break
              if not ok: continue
              nonsep = [(n, m) for n in range(2, K + 1) for m in range(2, K + 1)
                        if Tm[n, m] - Tm[n, 1] - Tm[1, m] + Tm[1, 1] != 0]
              if nonsep:
                  found += 1
                  row = [Tm[n, n] for n in range(1, K + 1)]
                  print(f"{name:12s} A={show(A):5s} B={show(B):5s} non-separable; T(n,n) = {row}; "
                        f"T(n,2) = {[Tm[n,2] for n in range(1, K+1)]}; T(2,m) = {[Tm[2,m] for m in range(1, K+1)]}", flush=True)
except MemoryGuard:
    print('STOPPED by the memory guard (hash-cons table > %d nodes); results above are partial' % NODE_LIMIT)
print('non-separable template instances:', found)
