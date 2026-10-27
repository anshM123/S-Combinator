"""Probe (agent_work_RR): normalisation times of three-numeral templates (N, M, K numerals), exact polynomial fit."""
import sys, itertools
from fractions import Fraction
from nf_scan import hc, step_fn, reset, hnum, NODE_CAP
def npar(t, cap=20000):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > NODE_CAP: return None
    return None
def fit(data, deg):
    pts = sorted(data); nv = len(pts[0])
    mons = [e for e in itertools.product(range(deg + 1), repeat=nv) if sum(e) <= deg]
    def val(p, e):
        r = Fraction(1)
        for x, k in zip(p, e): r *= Fraction(x) ** k
        return r
    rows = []; vals = []
    import copy
    def rank(M):
        M = [r[:] for r in M]; rk = 0
        for c in range(len(mons)):
            piv = next((r for r in range(rk, len(M)) if M[r][c] != 0), None)
            if piv is None: continue
            M[rk], M[piv] = M[piv], M[rk]
            for r in range(len(M)):
                if r != rk and M[r][c] != 0:
                    f = M[r][c] / M[rk][c]; M[r] = [a - f * b for a, b in zip(M[r], M[rk])]
            rk += 1
        return rk
    for p in pts:
        row = [val(p, e) for e in mons]
        if rank(rows + [row]) > len(rows): rows.append(row); vals.append(Fraction(data[p]))
        if len(rows) == len(mons): break
    if len(rows) < len(mons): return None
    n = len(mons); M = [rows[i][:] + [vals[i]] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[piv] = M[piv], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    co = {mons[i]: M[i][n] / M[i][i] for i in range(n)}
    if all(sum(co[e] * val(p, e) for e in mons) == data[p] for p in pts):
        return {e: v for e, v in co.items() if v != 0}
    return None
def build(t, v):
    if t == "S": return 0
    if t == "s": return hc.app(0, 0)
    if isinstance(t, str) and t in "NMK": return hnum(v["NMK".index(t)])
    return hc.app(build(t[0], v), build(t[1], v))
TEMPL = {"N(MK)S": (("N", ("M", "K")), "S"), "NMKS": ((("N", "M"), "K"), "S"), "N(MKS)": ("N", (("M", "K"), "S")),
         "NM(KS)": (("N", "M"), ("K", "S")), "N(M(KS))": ("N", ("M", ("K", "S"))), "N(M(K S)) S": (("N", ("M", ("K", "S"))), "S"),
         "N(MKS)S": (("N", (("M", "K"), "S")), "S")}
G = int(sys.argv[1]) if len(sys.argv) > 1 else 4
for name, t in TEMPL.items():
    data = {}; bad = False
    for v in itertools.product(range(1, G + 1), repeat=3):
        reset(); h = npar(build(t, v))
        if h is None: bad = True; break
        data[v] = h
    if bad: print(name, "no nf within caps"); continue
    co = fit(data, 3)
    print(name, {"n^%d m^%d k^%d" % e: str(c) for e, c in sorted(co.items())} if co else ("NONPOLY", list(data.items())[:10]))
