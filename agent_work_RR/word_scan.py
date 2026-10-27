"""E4 (agent_work_RR): single-datum (word) clocks.  D(a, b) = (SS.)^a (Z b-bar): a numeral-like word with a
separator Z (closed) above the inner numeral b-bar.  D is built by front-wrapping only (one closed layer per step), the
data shape a BT generator may produce under Theorem J.  Measure n_par of the processes D D S and D S (ReplaceAll
normalisation time) and fit exact polynomials in (a, b).  Usage: python word_scan.py ZMAX GRID CAP"""
import sys, itertools, time
from nf_scan import hc, step_fn, reset, hnum, NODE_CAP
from rr_tools import fit_poly2
from shape_scan import trees, label, txt
def npar(t, cap):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > NODE_CAP: return None
    return None
def hb(t):
    if t == "S": return 0
    return hc.app(hb(t[0]), hb(t[1]))
def D(Z, a, b):
    t = hc.app(hb(Z), hnum(b))
    for _ in range(a): t = hc.app(hc.app(0, 0), t)
    return t
ZMAX, GRID, CAP = map(int, sys.argv[1:4])
t0 = time.time()
for k in range(1, ZMAX + 1):
    for tr in trees(k):
        Z = label(tr, "S" * k)
        for name, mk in (("DDS", lambda d: hc.app(hc.app(d, d), 0)), ("DS", lambda d: hc.app(d, 0))):
            data = {}; bad = False
            for a in range(0, GRID):
                for b in range(1, GRID + 1):
                    reset(); v = npar(mk(D(Z, a, b)), CAP)
                    if v is None: bad = True; break
                    data[(a, b)] = v
                if bad: break
            if bad: continue
            co, ok = fit_poly2(data, 3)
            if not ok: print(txt(Z), name, "NONPOLY", sorted(data.items())[:8]); continue
            ns = any(i > 0 and j > 0 for (i, j) in co)
            if ns: print(txt(Z), name, {f"a^{i}b^{j}": str(v) for (i, j), v in sorted(co.items())})
print(f"done {time.time() - t0:.1f}s")
