"""Q10 ranking certificate with three labels: W(p, c, lam) = weight per leaf of an element of class c whose above-prefix
class is p (class of S e1...e_{i-1}) and whose below-context is lam.  The above-prefix of untouched elements is invariant
under a head step (S-identity), so Phi = sum_i W(p_i, c_i, lam_i) |e_i| only changes in the top part.
Step [x, y, z | R] => [x1..xk, z, y.z | R]   (before: x above s; y above s.x; z above s.x.y;
after: x_j above p_{j-1} (prefix of x's spine); z above [x]; y.z above [x].z).  Constraints (F-valued configs):
  (1) W(xz, yz, R)                       <= W(sx, y, R.rho_z)
  (2) W(x, z, R.rho_yz) + W(xz, yz, R)   <= W(sxy, z, R)
  (3) W(p_{j-1}, c_j, lam_j)             <= W(s, x, R.rho_z.rho_y)   for all spine decompositions of x
  W(s, x, R.rho_z.rho_y) >= 1 (x is opened).
"""
import sys, time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from verify_model import load

reps, F, M = load(sys.argv[1] if len(sys.argv) > 1 else "../data/model35_hn.txt")
n = len(reps); s = reps.index("S"); M = np.asarray(M, dtype=np.int64)
ident = tuple(range(n))
rho = [tuple(int(M[x, c]) for x in range(n)) for c in range(n)]
idx = {ident: 0}; maps = [ident]; frontier = [ident]
while frontier:
    new = []
    for g in frontier:
        for c in range(n):
            comp = tuple(rho[c][g[x]] for x in range(n))
            if comp not in idx: idx[comp] = len(maps); maps.append(comp); new.append(comp)
    frontier = new
L = len(maps)
ext = np.zeros((L, n), dtype=np.int64)
for li, lam in enumerate(maps):
    for c in range(n):
        ext[li, c] = idx[tuple(lam[int(M[x, c])] for x in range(n))]
P = sorted({maps[li][s] for li in range(L)})
var = {}
def W(p, c, li):
    k = ("W", p, c, li)
    if k not in var: var[k] = len(var)
    return var[k]
def V(q, li):
    k = ("V", q, li)
    if k not in var: var[k] = len(var)
    return var[k]
rows, cols, vals = [], [], []; r = 0
def add(terms):
    global r
    for col, v in terms: rows.append(r); cols.append(col); vals.append(v)
    r += 1
opened = set(); seen = set(); needV = set()
t0 = time.time()
for li in range(L):
    lam = maps[li]
    for x in range(n):
        sx = int(M[s, x])
        for y in range(n):
            sxy = int(M[sx, y])
            for z in range(n):
                yz = int(M[y, z]); xz = int(M[x, z])
                if not F[lam[int(M[xz, yz])]]: continue
                k = (li, x, y, z)
                if k in seen: continue
                seen.add(k)
                add([(W(xz, yz, li), 1.0), (W(sx, y, int(ext[li, z])), -1.0)])                       # (1)
                add([(W(x, z, int(ext[li, yz])), 1.0), (W(xz, yz, li), 1.0), (W(sxy, z, li), -1.0)])  # (2)
                mu = int(ext[int(ext[li, yz]), z]); nu = int(ext[int(ext[li, z]), y])
                wx = W(s, x, nu); opened.add(wx)
                add([(V(x, mu), 1.0), (wx, -1.0)])                                                     # (3b)
                needV.add((x, mu))
print(f"configuration constraints: {r}, vars {len(var)}, {time.time()-t0:.0f}s", flush=True)
# peel closure only over states reachable from needed (x, mu)
peels_by_q = {}
for q2 in P:
    for c in range(n):
        peels_by_q.setdefault(int(M[q2, c]), []).append((q2, c))
stack = list(needV); done = set(needV)
while stack:
    q, li = stack.pop()
    for q2, c in peels_by_q.get(q, []):
        add([(W(q2, c, li), 1.0), (V(q, li), -1.0)])
        nxt = (q2, int(ext[li, c]))
        add([(V(nxt[0], nxt[1]), 1.0), (V(q, li), -1.0)])
        if nxt not in done: done.add(nxt); stack.append(nxt)
nv = len(var)
print(f"total constraints {r}, variables {nv}, {time.time()-t0:.0f}s", flush=True)
A = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr()
cost = np.zeros(nv)
for k, i in var.items():
    if k[0] == "W": cost[i] = 1.0
bounds = [((1, None) if i in opened else (0, None)) for i in range(nv)]
res = linprog(cost, A_ub=A, b_ub=np.zeros(r), bounds=bounds, method="highs")
print("status:", res.status, res.message, f"{time.time()-t0:.0f}s", flush=True)
if res.status == 0:
    import pickle
    pickle.dump({"var": var, "x": res.x}, open("../data/q10_W3.pkl", "wb"))
    print("FEASIBLE: max", res.x.max())
