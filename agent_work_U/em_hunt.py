"""EM hunt: random closed terms in L36 flag-1 classes (where infinite leftmost walks live); walk the leftmost path
for NODES nodes and count, after a burn-in of BURN nodes, the steps that violate 'eventually monotone':
pops (top S), jumps (top S p) and returns (computed step whose child is the node's last argument)."""
import sys, random, time
from dm import *
from classes import cls, LFl, clear_cache
from stackview import hnf
from collections import Counter
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rand_term(k), rand_term(n - k))
def walk(t, nodes, burn):
    u = t; ty = Counter()
    for j in range(nodes):
        if u == 0: return None
        q1, Z = L[u], R[u]
        if q1 == 0:
            if j >= burn: ty["pop"] += 1
            u = Z; continue
        a = spine(q1)[0]
        if len(a) == 1:
            if j >= burn: ty["jump"] += 1
            u = a[0]; continue
        Hn = hnf(u, bud=max(20000, 20 * size(u)))
        if Hn is None: return None
        c = Hn[0]
        if j >= burn: ty["return" if c == Z else "push"] += 1
        u = c
        if size(u) > 300000: return None
    return ty
if __name__ == "__main__":
  seed, N, lo, hi, nodes, burn = [int(x) for x in sys.argv[1:7]]
  random.seed(seed); t0 = time.time(); tot = Counter(); nw = 0; viol = []
  for it in range(N):
      m = mark()
      t = rand_term(random.randint(lo, hi))
      c = cls(t)
      if LFl[c[0]] == 1:
          ty = walk(t, nodes, burn)
          if ty is not None:
              nw += 1; tot.update(ty)
              if (ty["pop"] or ty["jump"] or ty["return"]) and len(viol) < 10: viol.append((show(t)[:100], dict(ty)))
      truncate(m); clear_cache(m)
  print("seed", seed, "flag-1 walks completing", nodes, "nodes:", nw, "step counts after burn-in:", dict(tot), round(time.time() - t0), "s")
  print("walks with pops/jumps/returns after burn-in:", viol)
