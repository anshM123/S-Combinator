"""R3 agent: in phase-2 runs from ORDERED data with ONE occurrence of p that end in a proper position-3 transfer:
(a) is the bare y always the first Y-element (Y = contains x, y or r) of every list before the transfer?
(b) does every list have the shape CL* P* Y* with |P| <= 2?
usage: ytop.py one N | ytop.py rand SEED N COUNT"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, r3search as RS
hm, tg, T3 = CL.hm, CL.tg, CL.T3
P, Y, X, Rr = CL.P, CL.Y, CL.X, CL.Rr
INP = {X, Y, Rr}
def cls(t):
    a = tg.atoms(t)
    if any(v in a for v in INP): return "Y"
    if P in a: return "P"
    return "C"
def check(D, st, ex, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return
    st["transfers"] += 1
    V = lst[-3]; inner = V
    while hm.R[inner] != Y: inner = hm.R[inner]
    w = hm.L[inner]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    tglue = gl[0] if gl else len(hist)
    b0, c0 = (hm.L[w], hm.R[w]) if w > 0 else (None, None)
    tc = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == b0 and L[-3] == c0]
    tcre = tc[0] + 1 if tc else 1
    oky = okp = True
    for L in hist[tcre:tglue + 1]:
        seq = [cls(e) for e in reversed(L)]
        # shape CL* P* Y*
        s = "".join(seq)
        import re
        if not re.fullmatch(r"C*P*Y*", s): okp = False
        if s.count("P") > 2: okp = False
        firstY = next((e for e in reversed(L) if cls(e) == "Y"), None)
        if firstY != Y: oky = False
    st[("bare y is Y-top" if oky else "Y-top NOT bare y", "CL*P*Y* with |P|<=2" if okp else "shape violated")] += 1
    if not oky and len(ex) < 4: ex.append(hm.show(D))
if __name__ == "__main__":
    st = collections.Counter(); ex = []
    if sys.argv[1] == "one":
        for n in range(2, int(sys.argv[2]) + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and RS.pg.ordered(D): check(D, st, ex)
                hm.truncate(M0)
    else:
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and RS.pg.ordered(D): check(D, st, ex)
            hm.truncate(M0)
    for k in sorted(st, key=str): print(k, st[k])
    for e in ex: print("example:", e)
