"""R3 agent: the abstract outcome F(g) of a code g: first atom-headed front of the run of args(g) ++ [h1, h2, h3, h4]
(h_i fresh atoms; bottom holes h3, h4 are never read before an h1-/h2-front, two-barrier argument).
For every real single-wrapper handler V = w.y, w = b0.c0 (S-headed b0, c0): F(c0), the pattern of the glue, whether
phase 2 opens a c0-prefixed element before its transfer, and the phase-3 outcome.
usage: fc0.py N | fc0.py t NK WK NT | fc0.py o N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
H = [hm.atom("h%d" % i) for i in range(1, 5)]
def F(g, budget=2000):
    a, h = hm.spine(g)
    if h != 0: return "notS"
    st = list(reversed(H)) + list(reversed(a))
    for t in range(budget):
        if len(st) < 3: return "hnf"
        hd = hm.head(st[-1])
        if hd != 0:
            if hd in H: return "h%d" % (H.index(hd) + 1)
            if hd == P: return "p"
            if hd == Y: return "y"
            return "frozen"
        hm.step(st)
    return "budget"
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None            # single wrapper only
    w = hm.L[V]
    if CL.lp_reaches(w): return ("FH",)
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    pat = "alpha" if hist[gl[0]][-1] == c0 else "beta"
    aV, _ = hm.spine(V); k = len(aV)
    igen = any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist)
    openc0 = any(CL.pre(L[-1], c0) for L in hist)
    o3 = CL.phase3(V)[0]
    return ("b0=S" if b0 == 0 else "b0 other", pat, "Igen" if igen else "-", "c0 opened" if openc0 else "c0 never opened",
            "F(c0)=" + F(c0), o3)
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
