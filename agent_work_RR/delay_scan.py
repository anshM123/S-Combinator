"""E3 (agent_work_RR): search for 'delay gadgets' X (templates over N, M, S, s=SS) such that the ReplaceAll normalisation
time of X S R exceeds that of a slow process R by an exact non-separable polynomial Delta(n, m).
R = j-bar S (n_par = j - 1, normal form after j - 1 passes), j = J (large).  Usage: python delay_scan.py K GRID J CAP"""
import sys, itertools, time
from nf_scan import hc, step_fn, reset, hnum, NODE_CAP
from shape_scan import trees, label, txt, write_free
from rr_tools import fit_poly2
def npar(t, cap):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > NODE_CAP: return None
    return None
def hb(t, n, m):
    if t == "S": return 0
    if t == "s": return hc.app(0, 0)
    if t == "N": return hnum(n)
    if t == "M": return hnum(m)
    return hc.app(hb(t[0], n, m), hb(t[1], n, m))
K, GRID, J, CAP = map(int, sys.argv[1:5])
t0 = time.time(); res = []
for k in range(1, K + 1):
    for tr in trees(k):
        for labs in itertools.product("NMSs", repeat=k):
            if "N" not in labs or "M" not in labs: continue
            X = label(tr, labs); data = {}; bad = False
            for n in range(1, GRID + 1):
                for m in range(1, GRID + 1):
                    reset(); R = hc.app(hnum(J), 0)
                    v = npar(hc.app(hc.app(hb(X, n, m), 0), R), CAP)
                    if v is None: bad = True; break
                    data[(n, m)] = v - (J - 1)
                if bad: break
            if bad: continue
            co, ok = fit_poly2(data, 3)
            if ok and any(i > 0 and j > 0 for (i, j) in co):
                res.append((txt(X), write_free(X), {f"n^{i}m^{j}": str(v) for (i, j), v in sorted(co.items())}))
            elif not ok: res.append((txt(X), write_free(X), "NONPOLY", sorted(data.items())[:6]))
print(f"{time.time() - t0:.1f}s")
for r in res: print(r)
