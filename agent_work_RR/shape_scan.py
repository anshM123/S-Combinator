"""E1 (agent_work_RR): ReplaceAll hnf times of small templates over the leaves {N, M, S}, N = n-bar, M = m-bar (S-numerals).
For every binary tree with K leaves labelled N, M or S (N and M each at least once if TWO, else only N),
compute h_par(t(n, m)) on a grid and test for an exact polynomial of degree <= DEG.
Reports templates whose h_par is an exact polynomial with a nonzero n*m (or n^2) coefficient, plus write-freeness:
a template is write-free if no closed subterm is applied to a data-containing argument.
Usage: python shape_scan.py K TWO(0/1) GRID DEG CAP
"""
import sys, itertools, time
from fractions import Fraction
from rr_tools import *

def trees(k):
    if k == 1: return ["L"]
    out = []
    for i in range(1, k):
        for a in trees(i):
            for b in trees(k - i): out.append((a, b))
    return out
def label(tr, labs):
    it = iter(labs)
    def go(t):
        if t == "L": return next(it)
        return (go(t[0]), go(t[1]))
    return go(tr)
def txt(t):
    if isinstance(t, str): return t
    a, b = t
    return txt(a) + (("(" + txt(b) + ")") if isinstance(b, tuple) else txt(b))
def has_data(t):
    if isinstance(t, str): return t in ("N", "M")
    return has_data(t[0]) or has_data(t[1])
def write_free(t):
    if isinstance(t, str): return True
    a, b = t
    if has_data(b) and not has_data(a): return False
    return write_free(a) and write_free(b)
def build(t, n, m):
    if t == "S": return S
    if t == "N": return num(n)
    if t == "M": return num(m)
    return ap(build(t[0], n, m), build(t[1], n, m))

if __name__ == "__main__":
    K, TWO, GRID, DEG, CAP = map(int, sys.argv[1:6])
    t0 = time.time(); found = []; nshape = 0; skipped = 0
    for k in range(3, K + 1):
        for tr in trees(k):
            for labs in itertools.product("NMS" if TWO else "NS", repeat=k):
                if "N" not in labs or (TWO and "M" not in labs): continue
                t = label(tr, labs)
                nshape += 1
                data = {}; bad = False
                for n in range(1, GRID + 1):
                    for m in (range(1, GRID + 1) if TWO else [1]):
                        LP.reset()
                        try:
                            h = hpar(build(t, n, m), CAP)
                        except Cap:
                            h = None
                        if h is None: bad = True; break
                        data[(n, m)] = h
                    if bad: break
                if bad: skipped += 1; continue
                vals = set(data.values())
                if len(vals) <= 1: continue
                co, ok = fit_poly2(data, DEG)
                if not ok: found.append((txt(t), "NONPOLY", write_free(t), sorted(data.items())[:6])); continue
                nonsep = any(i > 0 and j > 0 for (i, j) in co) if TWO else any(i >= 2 for (i, j) in co)
                found.append((txt(t), {f"n^{i}m^{j}": str(v) for (i, j), v in sorted(co.items())}, write_free(t), nonsep))
    print(f"{nshape} templates, {skipped} without hnf within cap/grid, {time.time() - t0:.1f}s")
    for f in found:
        if f[1] == "NONPOLY" or f[3]: print(f)
    print("--- separable/linear ones:", sum(1 for f in found if f[1] != "NONPOLY" and not f[3]))
