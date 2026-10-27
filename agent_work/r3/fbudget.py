"""R3 agent: sanity check - in the cases that cover.py assigns to PAF or NHALL, did any F(c) computation end with
'budget' (abstract run of a code on two holes not finished within 2000 steps; then NH is NOT certified)?"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover, classify as CL, fc0
hm = CL.hm; P, Y, X, Rr = CL.P, CL.Y, CL.X, CL.Rr
st = collections.Counter()
data = list(CL.family(sys.argv[1:])); M0 = hm.mark()
for D in data:
    r = cover.classify(D)
    if r is not None and r[0] in ("PAF", "NHALL", "PAM-F", "PAM-F'"):
        lst = [Rr, Y, X, D]; hm.run(lst, 1500)
        V = lst[-3]; ws = []; t = V
        while t != Y: ws.append(hm.L[t]); t = hm.R[t]
        cs = [hm.R[w] for w in ws] if r[0] == "NHALL" else [hm.R[ws[-1]]]
        vals = [fc0.F(c, budget=20000) for c in cs]
        st[(r[0], "some F budget even at 20000" if "budget" in vals else ("some F = h" if any(v in ("h1", "h2") for v in vals) else "all F settled, no hole call"))] += 1
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
