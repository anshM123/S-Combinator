"""E5 (agent_work_RR): all templates with K leaves over {N, M, K3, S, s} containing the three numerals N, M, K3:
ReplaceAll normalisation time on the grid {1..G}^3, exact polynomial fit (degree <= 3)."""
import sys, itertools, time
from nf_scan import hc, step_fn, reset, hnum, NODE_CAP
from shape_scan import trees, label, txt, write_free
from tri_check import fit
def npar(t, cap):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > 500000: return None
    return None
def hb(t, v):
    if t == "S": return 0
    if t == "s": return hc.app(0, 0)
    if t in ("N", "M", "K"): return hnum(v["NMK".index(t)])
    return hc.app(hb(t[0], v), hb(t[1], v))
KL, G, CAP = map(int, sys.argv[1:4])
t0 = time.time()
for tr in trees(KL):
    for labs in itertools.product("NMKSs", repeat=KL):
        if not all(c in labs for c in "NMK"): continue
        t = label(tr, labs); data = {}; bad = False
        for v in itertools.product(range(1, G + 1), repeat=3):
            reset(); h = npar(hb(t, v), CAP)
            if h is None: bad = True; break
            data[v] = h
        if bad: continue
        co = fit(data, 3)
        if co is None: print(txt(t), "NONPOLY", list(data.items())[:6]); continue
        deg = max(sum(e) for e in co)
        print(txt(t), write_free(t), "deg", deg, {"n^%d m^%d k^%d" % e: str(c) for e, c in sorted(co.items())})
print(f"done {time.time() - t0:.1f}s")
