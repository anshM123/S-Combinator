"""E2 (agent_work_RR): ReplaceAll NORMALISATION times of small templates over {N, M, S, s2 = SS}, N = n-bar, M = m-bar.
n_par(t) = first k with P^k(t) = P^(k+1)(t) (direct passes, code/parallel_eval.step_fn, hash-consed).
Reports templates whose n_par is an exact polynomial (degree <= DEG) on the grid with a non-separable monomial.
Usage: python nf_scan.py K TWO GRID DEG CAP [ALPHABET]
"""
import sys, itertools, time
sys.setrecursionlimit(1000000)
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "code"))
import hc
from parallel_eval import step_fn
from rr_tools import fit_poly2
from shape_scan import trees, label, txt, write_free
NODE_CAP = 2_000_000
def reset():
    del hc.L[1:]; del hc.R[1:]; hc.TAB.clear()
def hnum(n):
    t = hc.app(0, 0)
    for _ in range(n - 1): t = hc.app(hc.app(0, 0), t)
    return t
def hbuild(t, n, m):
    if t == "S": return 0
    if t == "s": return hc.app(0, 0)
    if t == "N": return hnum(n)
    if t == "M": return hnum(m)
    return hc.app(hbuild(t[0], n, m), hbuild(t[1], n, m))
def npar(t, cap):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > NODE_CAP: return None
    return None
if __name__ == "__main__":
    K, TWO, GRID, DEG, CAP = map(int, sys.argv[1:6])
    ALPH = sys.argv[6] if len(sys.argv) > 6 else ("NMSs" if TWO else "NSs")
    t0 = time.time(); found = []; nshape = 0; skipped = 0
    for k in range(2, K + 1):
        for tr in trees(k):
            for labs in itertools.product(ALPH, repeat=k):
                if "N" not in labs or (TWO and "M" not in labs): continue
                t = label(tr, labs); nshape += 1
                data = {}; bad = False
                for n in range(1, GRID + 1):
                    for m in (range(1, GRID + 1) if TWO else [1]):
                        reset()
                        h = npar(hbuild(t, n, m), CAP)
                        if h is None: bad = True; break
                        data[(n, m)] = h
                    if bad: break
                if bad: skipped += 1; continue
                if len(set(data.values())) <= 1: continue
                co, ok = fit_poly2(data, DEG)
                if not ok: found.append((txt(t), "NONPOLY", write_free(t), sorted(data.items())[:8])); continue
                nonsep = any(i > 0 and j > 0 for (i, j) in co) if TWO else any(i >= 2 for (i, j) in co)
                found.append((txt(t), {f"n^{i}m^{j}": str(v) for (i, j), v in sorted(co.items())}, write_free(t), nonsep))
    print(f"{nshape} templates, {skipped} not normalising within cap on the grid, {time.time() - t0:.1f}s")
    for f in found:
        if f[1] == "NONPOLY" or f[3]: print(f)
    lin = [f for f in found if f[1] != "NONPOLY" and not f[3]]
    print("--- polynomial but separable/linear:", len(lin))
    for f in lin[:40]: print(f)
