"""R3 agent: S-duplication creation of the pattern-beta wrapper w (ordered single-occurrence data): at the creation
step [S.a'', b0, c0, z | R], is z the bare y?  And what is the first hole-front of the abstract run of
args(a'') ++ [om, ka] (om := w, ka := c0.w): om or ka, top part length, element right below the top part?
usage: creation2.py one N | creation2.py rand SEED N COUNT"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s1test, r3search as RS, classify as CL, creation as CR
hm, tg, T3 = CL.hm, CL.tg, CL.T3
P, Y, X, Rr = CL.P, CL.Y, CL.X, CL.Rr
OM = hm.atom("om"); KA = hm.atom("ka")
def first_hole(a2, budget=2000):
    aa, _ = hm.spine(a2)
    st = [KA, OM] + list(reversed(aa))
    for t in range(budget):
        if len(st) < 3: return ("short", len(st))
        h = hm.head(st[-1])
        if h != 0:
            nm = "om" if h == OM else ("ka" if h == KA else ("p" if h == P else "other"))
            fa, _ = hm.spine(st[-1])
            return (nm, "front args %d" % len(fa), "top len %d" % len(st))
        hm.step(st)
    return ("budget",)
def info(D, budget=1500):
    r = s1test.info(D)
    if r is None or r[0] != "beta" or r[1] != "ordered": return None
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    V = lst[-3]; w = hm.L[V]; b0, c0 = hm.L[w], hm.R[w]
    tc = [t for t, L in enumerate(hist) if len(L) >= 4 and L[-2] == b0 and L[-3] == c0]
    if not tc: return ("no creation step",)
    L = hist[tc[0]]; a_ = L[-1]; aa, _ = hm.spine(a_)
    if len(aa) != 1: return ("front args %d" % len(aa),)
    z = L[-4]
    return ("z = y" if z == Y else "z != y",) + first_hole(aa[0])
if __name__ == "__main__":
    st = collections.Counter(); ex = collections.defaultdict(list)
    if sys.argv[1] == "one":
        for n in range(2, int(sys.argv[2]) + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0:
                    r = info(D)
                    if r: st[r] += 1; (len(ex[r]) < 2 and ex[r].append(hm.show(D)))
                hm.truncate(M0)
    else:
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and RS.pg.ordered(D):
                r = info(D)
                if r: st[r] += 1; (len(ex[r]) < 2 and ex[r].append(hm.show(D)))
            hm.truncate(M0)
    for k in sorted(st): print(k, st[k], ex[k])
