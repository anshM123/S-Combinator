"""R3 agent: for real single-wrapper pattern-beta handlers w = b0.c0 from ordered single-occurrence data: how is the
node w first created (glue [a', b0, c0] -> args(a') ++ [c0, w]; |args a'|), is c0.w created right after, and how
does 'c0 on (w, y)' arise (opening of c0.w over y?).  usage: creation.py one N | creation.py rand SEED N COUNT"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s1test, r3search as RS, classify as CL
hm, tg, T3 = CL.hm, CL.tg, CL.T3
P, Y, X, Rr = CL.P, CL.Y, CL.X, CL.Rr
def subterm(t, s):
    stack = [t]
    while stack:
        u = stack.pop()
        if u == s: return True
        if u > 0: stack.append(hm.L[u]); stack.append(hm.R[u])
    return False
def info(D, budget=1500):
    r = s1test.info(D)
    if r is None or r[0] != "beta" or r[1] != "ordered": return None
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    V = lst[-3]; w = hm.L[V]; b0, c0 = hm.L[w], hm.R[w]
    if subterm(D, w): cre = "w subterm of D"
    else:
        tc = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == b0 and L[-3] == c0]
        if not tc: cre = "w released only?"
        else:
            a_ = hist[tc[0]][-1]; aa, _ = hm.spine(a_)
            cre = "created by front with %d args" % len(aa)
    c0w = hm.app(c0, w)
    opens = any(len(L) >= 3 and CL.pre(L[-1], c0w) and L[-3] == Y for L in hist)
    return (cre, "c0.w opened over y" if opens else "c0.w NOT opened over y", r[2])
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
