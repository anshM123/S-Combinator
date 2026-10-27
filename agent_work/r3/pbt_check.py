"""R3 agent: sanity check of the per-case hypotheses used by cover.py for class PBT: is a1 (c0 = S.a1) S-headed?"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover, classify as CL
hm = CL.hm; P, Y, X, Rr = CL.P, CL.Y, CL.X, CL.Rr
st = collections.Counter()
data = list(CL.family(sys.argv[1:])); M0 = hm.mark()
for D in data:
    r = cover.classify(D)
    if r is not None and r[0] == "PBT":
        lst = [Rr, Y, X, D]; hm.run(lst, 1500)
        w = hm.L[lst[-3]]; c0 = hm.R[w]; a1 = hm.R[c0]
        st["a1 S-headed" if hm.head(a1) == 0 else "a1 NOT S-headed"] += 1
    hm.truncate(M0)
print(dict(st))
