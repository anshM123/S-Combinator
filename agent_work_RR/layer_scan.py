"""E6 (agent_work_RR): two-letter data built by FRONT-WRAPPING only: D(a, b) = L^b ((SS.)^(a-1) SS) (b layers of a closed
wrapper L outside the numeral a-bar), and the reverse order D'(a, b) = (SS.)^a (L^b SS).  Is the ReplaceAll normalisation
time of D D S an exact polynomial in (a, b) whose quadratic part is NOT c*(linear form)^2 (i.e. genuinely two-parameter)?
Usage: python layer_scan.py LMAX GRID CAP"""
import sys, time
from fractions import Fraction
from nf_scan import hc, step_fn, reset, hnum, NODE_CAP
from rr_tools import fit_poly2
from shape_scan import trees, label, txt
def npar(t, cap):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > 800000: return None
    return None
def hb(t):
    if t == "S": return 0
    return hc.app(hb(t[0]), hb(t[1]))
LMAX, GRID, CAP = map(int, sys.argv[1:4]); t0 = time.time()
for k in range(1, LMAX + 1):
    for tr in trees(k):
        L = label(tr, "S" * k)
        for order in ("L_outside", "L_inside"):
            for name in ("DDS", "DS", "DSS"):
                data = {}; bad = False
                for a in range(1, GRID + 1):
                    for b in range(0, GRID):
                        reset(); l = hb(L)
                        if order == "L_outside":
                            d = hnum(a)
                            for _ in range(b): d = hc.app(l, d)
                        else:
                            d = hc.app(hc.app(0, 0), 0)
                            for _ in range(b): d = hc.app(l, d)
                            for _ in range(a): d = hc.app(hc.app(0, 0), d)
                        t = {"DDS": hc.app(hc.app(d, d), 0), "DS": hc.app(d, 0), "DSS": hc.app(hc.app(d, 0), 0)}[name]
                        v = npar(t, CAP)
                        if v is None: bad = True; break
                        data[(a, b)] = v
                    if bad: break
                if bad: continue
                co, ok = fit_poly2(data, 3)
                if not ok: continue
                c20, c11, c02 = co.get((2, 0), 0), co.get((1, 1), 0), co.get((0, 2), 0)
                if any(i + j >= 3 for (i, j) in co) or (c11 != 0 and c11 * c11 != 4 * c20 * c02):
                    print(txt(L), order, name, {f"a^{i}b^{j}": str(v) for (i, j), v in sorted(co.items())})
print(f"done {time.time() - t0:.1f}s")
