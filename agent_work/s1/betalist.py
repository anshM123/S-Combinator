"""S1 agent: list the single-wrapper transfers of ORDERED single-occurrence data (<= N leaves, S-headed) whose
handler w.y was glued in pattern beta with a P-front a1 (a1 contains p, a1 != c0).  Prints the datum, w, b0, c0,
a1 and the step numbers of: creation of w (first step whose new node is w), glue, transfer.
usage: betalist.py N"""
import sys, os, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
def hasP(t): return tg.atoms(t).get(P, 0) > 0
def proper(V):
    a = tg.atoms(V)
    return V != Y and a.get(Y, 0) == 1 and not a.get(X, 0) and not a.get(Rr, 0)
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return ("multi",)
    w = hm.L[V]
    if w <= 0 or hm.head(w) != 0: return ("w atom/atom-headed",)
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    tg_ = gl[0]; a1 = hist[tg_][-1]
    if a1 == c0: return ("alpha",)
    if not hasP(a1): return ("closedglue",)
    if hm.head(c0) != 0: return ("c0 atom-headed",)
    cr = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == b0 and L[-3] == c0]
    return ("beta", hm.show(D), hm.show(w), hm.show(b0), hm.show(c0), hm.show(a1), cr[:1], tg_, len(hist))
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); out = []
    for n in range(2, N + 1):
        CS = tg.contexts(n); M0 = hm.mark()
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) == 0 and pg.ordered(D):
                r = info(D)
                if r is not None:
                    st[r[0]] += 1
                    if r[0] == "beta": out.append(r[1:])
            hm.truncate(M0)
    print(dict(st))
    for r in out: print(r)
