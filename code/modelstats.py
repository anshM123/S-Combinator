"""Structure of a learned finite S-model: S-identity, closure conditions, aperiodicity of the context monoid,
and the joint model with M35 (HN) and P39 (productivity).  usage: python modelstats.py MODELFILE [MONOIDCAP]"""
import sys
import numpy as np
from verify_model import load

path = sys.argv[1]; CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 3_000_000
reps, F, T = load(path)
n = len(reps); s = reps.index("S")
viol = sum(1 for x in range(n) for y in range(n) for z in range(n) if T[T[T[s, x], y], z] != T[T[x, z], T[y, z]])
print(f"classes {n}, accepting {int(F.sum())}, S-identity violations {viol}")
print("S x y in F <=> x,y in F:", all(F[T[T[s, x], y]] == (F[x] and F[y]) for x in range(n) for y in range(n)),
      "| S x in F <=> x in F:", all(F[T[s, x]] == F[x] for x in range(n)))
nonF = [c for c in range(n) if not F[c]]
print("non-accepting classes:", len(nonF), " left-absorbing:", [c for c in nonF if all(T[c, x] == c for x in range(n))][:5],
      " right-absorbing:", [c for c in nonF if all(T[x, c] == c for x in range(n))][:5])

# joint with M35 and P39 (generated sub-magma)
M_reps, M_F, M = load("../data/model35_hn.txt"); P_reps, P_F, P = load("../data/model39_productivity.txt")
start = (s, M_reps.index("S"), P_reps.index("S"))
seen = {start}; order = [start]; frontier = [start]
while frontier:
    new = []
    for a in list(order):
        for b in list(order):
            for x, y in ((a, b), (b, a)):
                c = (int(T[x[0], y[0]]), int(M[x[1], y[1]]), int(P[x[2], y[2]]))
                if c not in seen: seen.add(c); order.append(c); new.append(c)
    frontier = new
print(f"joint (this, M35, P39) classes realised: {len(order)}")
print("  accepted but no hnf (M35 bottom):", sum(1 for c in order if F[c[0]] and not M_F[c[1]]),
      "| no hnf but not accepted:", sum(1 for c in order if not F[c[0]] and not M_F[c[1]]))

# context monoid: maps x -> a*x, x -> x*a ; aperiodic iff every element f has f^k = f^(k+1)
gens = [tuple(int(T[a, x]) for x in range(n)) for a in range(n)] + [tuple(int(T[x, a]) for x in range(n)) for a in range(n)]
gens = list(dict.fromkeys(gens))
ident = tuple(range(n)); mon = {ident}; frontier = [ident]; capped = False
while frontier and not capped:
    new = []
    for g in frontier:
        for h in gens:
            c = tuple(h[g[x]] for x in range(n))
            if c not in mon:
                mon.add(c); new.append(c)
                if len(mon) >= CAP: capped = True; break
        if capped: break
    frontier = new
aper, maxidx, bad = True, 0, None
for g in mon:
    seen_p = {}; r = ident; k = 0
    while r not in seen_p: seen_p[r] = k; r = tuple(g[r[x]] for x in range(n)); k += 1
    if k - seen_p[r] != 1: aper = False; bad = (k - seen_p[r]); break
    maxidx = max(maxidx, seen_p[r])
print(f"context monoid: {len(mon)} elements{' (CAPPED — partial)' if capped else ''}; aperiodic: {aper}"
      + (f" (found period {bad})" if not aper else f"; max index {maxidx}"))
