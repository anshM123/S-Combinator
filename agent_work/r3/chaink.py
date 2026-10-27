"""R3 agent: P-pair chain after the creation of the single wrapper w = b0.c0 (ordered single-occurrence data).
At the creation step [a', b0, c0, z | R]: is z the bare y?  Then the chain E0 = c0, E1 = w, E_{k+2} = E_k.E_{k+1}:
which chain element is the first one opened (front) after the creation, and what is at position 3 then?
usage: chaink.py one N | chaink.py rand SEED N COUNT"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, r3search as RS
hm, tg, T3 = CL.hm, CL.tg, CL.T3
P, Y, X, Rr = CL.P, CL.Y, CL.X, CL.Rr
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return ("multi",)
    w = hm.L[V]
    if w <= 0 or CL.lp_reaches(w): return ("FH",)
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    pat = "alpha" if hist[gl[0]][-1] == c0 else "beta"
    tc = [t for t, L in enumerate(hist) if len(L) >= 4 and L[-2] == b0 and L[-3] == c0]
    if not tc: return (pat, "w not created by a glue (subterm of D?)")
    t0 = tc[0]; z = hist[t0][-4]
    if z != Y: return (pat, "z != y")
    chain = [c0, w]
    for k in range(12): chain.append(hm.app(chain[-2], chain[-1]))
    cset = {e: i for i, e in enumerate(chain)}
    for t in range(t0 + 1, len(hist)):
        f = hist[t][-1]
        if f in cset:
            k = cset[f]
            pos3 = hist[t][-3]
            return (pat, "z = y", "first chain front E_%d" % k, "pos3 = y" if pos3 == Y else "pos3 != y")
    return (pat, "z = y", "no chain front before transfer")
if __name__ == "__main__":
    st = collections.Counter(); ex = collections.defaultdict(list)
    def feed(D):
        r = info(D)
        if r is not None:
            st[r] += 1
            if len(ex[r]) < 2: ex[r].append(hm.show(D))
    if sys.argv[1] == "one":
        for n in range(2, int(sys.argv[2]) + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and RS.pg.ordered(D): feed(D)
                hm.truncate(M0)
    else:
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and RS.pg.ordered(D): feed(D)
            hm.truncate(M0)
    for k in sorted(st): print(k, st[k], ex[k])
