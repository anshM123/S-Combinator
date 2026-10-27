"""R3 agent: the residual condition of Theorem BETA0.  H1ok(c0): at the first atom-headed front of the run of
args(c0) ++ [h1, h2] (if it is h1-headed), the front is h1.h2.(...) or the bare h1 with h2 at position 3.
For every real single-wrapper pattern-beta handler: c0 on (w, y) in phase 2?  F(c0)?  H1ok(c0)?
usage: h1ok.py N | h1ok.py t NK WK NT | h1ok.py o N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0, beta3
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y = CL.P, CL.Y
H = fc0.H
def h1ok(g, budget=2000):
    a, h = hm.spine(g)
    st = list(reversed(H)) + list(reversed(a))
    for t in range(budget):
        if len(st) < 3: return "hnf"
        hd = hm.head(st[-1])
        if hd != 0:
            if hd != H[0]: return "not h1"
            args, _ = hm.spine(st[-1])
            if args and args[0] == H[1]: return "H1ok (h1.h2...)"
            if not args and st[-3] == H[1]: return "H1ok (h1, _, h2)"
            return "H1 RESIDUAL"
        hm.step(st)
    return "budget"
def info(D):
    r = beta3.info(D)
    if r is None: return None
    lst = [CL.Rr, Y, CL.X, D]
    s, k = hm.run(lst, 1500)
    w = hm.L[lst[-3]]; c0 = hm.R[w]
    return r + (h1ok(c0),)
if __name__ == "__main__":
    data = list(CL.family(sys.argv[1:]))
    st = collections.Counter(); ex = collections.defaultdict(list); M0 = hm.mark()
    for D in data:
        r = info(D)
        if r is not None:
            st[r] += 1
            if len(ex[r]) < 2: ex[r].append(hm.show(D))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k], ex[k])
