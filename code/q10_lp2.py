"""Search for a termination certificate for BEKW Question 10 (M35 = BEKW Fig. 14).

Head machine on lists: [x, y, z | R] => ch(x) ++ [z, y.z | R].  Ranking function
    Phi(list) = sum_i W(class(e_i), lambda_i) * |e_i|
where lambda_i is the right-multiplication monoid element of the elements below e_i (x -> x.e_{i+1}...e_m) and |e| is the
number of leaves.  For a step on a non-bottom configuration, Phi strictly decreases provided
  (1) W(yz, R)                 <= W(y, R.rho_z)
  (2) W(z, R.rho_yz) + W(yz, R) <= W(z, R)
  (3) W(c_j, lambda_j)         <= W(x, R.rho_z.rho_y)      for every spine argument x_j of x,
since |x| = 1 + sum |x_j| and |y.z| = |y| + |z|; the decrease is >= W(x, .) >= 1.  Constraint (3) over all spines of
class x is encoded exactly with V(q, lam) >= W(c, lam), V(q, lam) >= V(q', lam.rho_c) for every peel q'.c = q with q'
a prefix class (reachable from s), and V(x, R.rho_yz.rho_z) <= W(x, R.rho_z.rho_y).
A feasible W proves: every closed S-term whose M35 class is not bottom has a head normal form.
"""
import sys, time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from verify_model import load

reps, F, M = load(sys.argv[1] if len(sys.argv) > 1 else "../data/model35_hn.txt")
n = len(reps); s = reps.index("S"); M = np.asarray(M, dtype=np.int64)
# right-multiplication monoid
ident = tuple(range(n))
rho = [tuple(int(M[x, c]) for x in range(n)) for c in range(n)]
idx = {ident: 0}; maps = [ident]; frontier = [ident]
while frontier:
    new = []
    for g in frontier:
        for c in range(n):
            comp = tuple(rho[c][g[x]] for x in range(n))      # x -> g(x).c  : first g then rho_c  (append below)
            if comp not in idx: idx[comp] = len(maps); maps.append(comp); new.append(comp)
    frontier = new
L = len(maps)
# ext(lam, c) = lam o rho_c : x -> lam(x.c)   ("c inserted directly below")
ext = np.zeros((L, n), dtype=np.int64)
for li, lam in enumerate(maps):
    for c in range(n):
        ext[li, c] = idx[tuple(lam[int(M[x, c])] for x in range(n))]
lamv = np.array(maps, dtype=np.int64)          # lamv[li, x] = lam(x)
P = sorted({maps[li][s] for li in range(L)})    # prefix classes reachable from s
print(f"classes {n}, monoid {L}, prefix classes {len(P)}", flush=True)

NW = n * L
def W(c, li): return c * L + li
def V(q, li): return NW + q * L + li
rows, cols, vals = [], [], []
r = 0
def add(terms):
    global r
    for col, v in terms: rows.append(r); cols.append(col); vals.append(v)
    r += 1

t0 = time.time()
seen12 = set(); seen3 = set(); opened = set()
for li in range(L):
    lam = lamv[li]
    for y in range(n):
        for z in range(n):
            yz = int(M[y, z])
            xs = [x for x in range(n) if F[lam[int(M[int(M[x, z]), yz])]]]
            if not xs: continue
            key = (li, y, z)
            if key not in seen12:
                seen12.add(key)
                add([(W(yz, li), 1.0), (W(y, int(ext[li, z])), -1.0)])                       # (1)
                add([(W(z, int(ext[li, yz])), 1.0), (W(yz, li), 1.0), (W(z, li), -1.0)])      # (2)
            mu = int(ext[int(ext[li, yz]), z]); nu = int(ext[int(ext[li, z]), y])
            for x in xs:
                k3 = (x, mu, nu)
                if k3 in seen3: continue
                seen3.add(k3)
                add([(V(x, mu), 1.0), (W(x, nu), -1.0)])                                       # (3b)
                opened.add(W(x, nu))
print(f"configuration constraints: {r} (rows so far), {time.time()-t0:.0f}s", flush=True)
Pset = set(P)
peels = [(q2, c, int(M[q2, c])) for q2 in P for c in range(n)]
for li in range(L):
    for q2, c, q in peels:
        add([(W(c, li), 1.0), (V(q, li), -1.0)])                                             # (3a) W <= V
        add([(V(q2, int(ext[li, c])), 1.0), (V(q, li), -1.0)])                                # (3a) V <= V
print(f"total constraints {r}, variables {2*NW}, {time.time()-t0:.0f}s", flush=True)
A = coo_matrix((vals, (rows, cols)), shape=(r, 2 * NW)).tocsr()
b = np.zeros(r)
cost = np.concatenate([np.ones(NW), np.zeros(NW)])
bounds = [((1, None) if i in opened else (0, None)) for i in range(NW)] + [(0, None)] * NW   # W >= 1 only where opened
print("weights that must be >= 1 (opened elements):", len(opened), flush=True)
res = linprog(cost, A_ub=A, b_ub=b, bounds=bounds, method="highs")
print("status:", res.status, res.message, f"{time.time()-t0:.0f}s", flush=True)
if res.status == 0:
    Wsol = res.x[:NW]
    np.save("../data/q10_W.npy", Wsol)
    print("FEASIBLE: max W", Wsol.max(), "min W", Wsol.min())
