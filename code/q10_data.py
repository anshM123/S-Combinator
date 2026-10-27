"""Data-driven feasibility test of the size-weighted ranking ansatz for Q10: collect actual head steps of terminating
runs (all terms up to N leaves) and ask for W(label) >= 0 with Phi(before) - Phi(after) >= 1 on every observed step,
where Phi = sum_i W(label_i) * |e_i| and label = (above-prefix class, class, below-context map) [LABELS=3] or
(class, below-context) [LABELS=2]."""
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from verify_model import load
from symb import trees, spine, size

N = int(sys.argv[1]); LABELS = int(sys.argv[2])
reps, F, M = load("../data/model35_hn.txt"); n = len(reps); s = reps.index("S")
memo = {}
def cl(t):
    if t == "S": return s
    if t in memo: return memo[t]
    r = int(M[cl(t[0]), cl(t[1])]); memo[t] = r; return r
def labels(lst):
    """labels of list elements: (above-prefix class, class, below-map as tuple)"""
    cs = [cl(e) for e in lst]
    out = []; above = s
    below_maps = []
    # below map for element i: x -> x . c_{i+1} ... c_m
    m = len(cs)
    for i in range(m):
        out.append((above, cs[i]))
        above = int(M[above, cs[i]])
    tail = list(range(n))
    bel = [None] * m
    for i in range(m - 1, -1, -1):
        bel[i] = tuple(tail)
        tail = [tail[int(M[x, cs[i]])] for x in range(n)]   # prepend c_i:  x -> tail(x.c_i)
    return [(a, c, b) if LABELS == 3 else (c, b) for (a, c), b in zip(out, bel)]
var = {}
def vid(k):
    if k not in var: var[k] = len(var)
    return var[k]
rows, cols, vals = [], [], []; r = 0
for nn in range(4, N + 1):
    for t in trees(nn):
        if not F[cl(t)]: continue
        h, args = spine(t); st = list(args); steps = 0; ok = True; trace = []
        while len(st) >= 3:
            if steps > 4 * nn + 20: ok = False; break
            a, b, c = st[0], st[1], st[2]
            _, ch = spine(a)
            new = list(ch) + [c, (b, c)] + st[3:]
            trace.append((st, new)); st = new; steps += 1
        if not ok: continue
        for before, after in trace:
            coef = {}
            for lab, e in zip(labels(before), before): coef[vid(lab)] = coef.get(vid(lab), 0) + size(e)
            for lab, e in zip(labels(after), after): coef[vid(lab)] = coef.get(vid(lab), 0) - size(e)
            # Phi(before) - Phi(after) >= 1   <=>   -(sum coef * W) <= -1
            for k, v in coef.items():
                if v: rows.append(r); cols.append(k); vals.append(-float(v))
            r += 1
nv = len(var)
print(f"N={N} labels={LABELS}: observed steps {r}, label variables {nv}", flush=True)
A = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr()
res = linprog(np.ones(nv), A_ub=A, b_ub=-np.ones(r), bounds=[(0, None)] * nv, method="highs")
print("status:", res.status, res.message)
