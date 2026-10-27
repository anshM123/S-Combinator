"""R3 agent: sanity check of class LN0 in cover.py: does the next phase really never open an Ln'-prefixed element,
or did the check merely hit its 3000-step budget?  Re-run every LN0 case with 50,000 steps."""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover, classify as CL
hm, tg = CL.hm, CL.tg
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
st = collections.Counter()
data = list(CL.family(sys.argv[1:])); M0 = hm.mark()
for D in data:
    r = cover.classify(D)
    if r is not None and r[0] == "LN0":
        lst = [Rr, Y, X, D]; hm.run(lst, 1500)
        V = lst[-3]; ws = []; t = V
        while t != Y: ws.append(hm.L[t]); t = hm.R[t]
        vn3 = tg.subst(ws[-1], P, C); Ln3 = hm.app(vn3, P)
        D3 = tg.subst(tg.subst(V, P, C), Y, P)
        s3 = [Rr, Y, X, D3]; res = "budget 50000"
        for k in range(50000):
            if len(s3) < 3: res = "hnf (never opened)"; break
            if hm.head(s3[-1]) != 0: res = "stuck (never opened)"; break
            if CL.pre(s3[-1], Ln3): res = "OPENED"; break
            hm.step(s3)
        st[res] += 1
    hm.truncate(M0)
print(dict(st))
