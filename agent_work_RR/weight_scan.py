"""E8 (agent_work_RR): per-letter weights of a front-wrapping layer L in the two roles of a datum.
D(a, b) = L^b (a-bar).  spine role: delay(a, b) = n_par(D S R) - n_par(R) with R = 40-bar S (slow, time 39);
iterator role: it(a, b, k) = n_par(D k-bar S) for k = 3, 5 (B2 gives (iterations)(k + 2) + const for numerals).
Reports layers L for which both are exact affine functions of (a, b) (on the grid) with NON-PROPORTIONAL letter weights:
then D D S would be a genuinely two-parameter clock.  Usage: python weight_scan.py LMAX AMAX BMAX CAP"""
import sys, time
from fractions import Fraction
from nf_scan import hc, step_fn, reset, hnum
from rr_tools import fit_poly2
from shape_scan import trees, label, txt
def npar(t, cap):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > 600000: return None
    return None
def hb(t):
    if t == "S": return 0
    return hc.app(hb(t[0]), hb(t[1]))
LMAX, AMAX, BMAX, CAP = map(int, sys.argv[1:5]); t0 = time.time(); nl = 0
for kl in range(1, LMAX + 1):
    for tr in trees(kl):
        L = label(tr, "S" * kl); nl += 1
        res = {}
        for role in ("sp", "it3", "it5"):
            data = {}; bad = False
            for a in range(1, AMAX + 1):
                for b in range(0, BMAX + 1):
                    reset(); d = hnum(a); l = hb(L)
                    for _ in range(b): d = hc.app(l, d)
                    if role == "sp":
                        v = npar(hc.app(hc.app(d, 0), hc.app(hnum(40), 0)), CAP); v = None if v is None else v - 39
                    else:
                        k = 3 if role == "it3" else 5
                        v = npar(hc.app(hc.app(d, hnum(k)), 0), CAP)
                    if v is None: bad = True; break
                    data[(a, b)] = v
                if bad: break
            if bad: break
            co, ok = fit_poly2(data, 1)
            if not ok: break
            res[role] = co
        if len(res) == 3:
            wa_sp, wb_sp = res["sp"].get((1, 0), 0), res["sp"].get((0, 1), 0)
            wa_it = (res["it5"].get((1, 0), 0) - res["it3"].get((1, 0), 0)) / 2
            wb_it = (res["it5"].get((0, 1), 0) - res["it3"].get((0, 1), 0)) / 2
            prop = wa_sp * wb_it == wb_sp * wa_it
            if wb_sp != 0 or wb_it != 0:
                print(txt(L), "spine weights (a, b):", (str(wa_sp), str(wb_sp)), " iterator weights:", (str(wa_it), str(wb_it)), "PROPORTIONAL" if prop else "NON-PROPORTIONAL")
print(f"{nl} layers, {time.time() - t0:.1f}s")
