"""S1 agent: grammar of P-terms that contain w (single-wrapper transfers of ORDERED single-occurrence data).
Shape of a term: w -> 'w', maximal closed subterm -> 'k', maximal P-subterm not containing w -> 'q', else
application 'f(x)'.  Collects (a) shapes of top-level P-elements containing w, (b) P-region configurations
(tuple of shapes) whenever the P-region contains a w-term, with the Y-top (y or Y), over all lists before the
transfer.  usage: wshapes.py N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ytopinv as YI, wptest as WT
hm, tg, pg, P, Y = YI.hm, YI.tg, YI.pg, YI.P, YI.Y
cls = YI.cls
def shape(t, w, depth=0):
    if t == w: return "w"
    c = cls(t)
    if c == "C": return "k"
    if c == "P" and not WT.contains(t, w): return "q"
    if c == "Y": return "Y"
    if depth > 5: return "..."
    return shape(hm.L[t], w, depth + 1) + "(" + shape(hm.R[t], w, depth + 1) + ")"
if __name__ == "__main__":
    N = int(sys.argv[1]); shapes = collections.Counter(); confs = collections.Counter(); ex = {}
    for n in range(2, N + 1):
        CS = tg.contexts(n); M0 = hm.mark()
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) == 0 and pg.ordered(D):
                X, Rr = YI.X, YI.Rr
                lst = [Rr, Y, X, D]; hist = []
                for t in range(1500):
                    if len(lst) < 3 or hm.head(lst[-1]) != 0: break
                    hist.append(tuple(lst)); hm.step(lst)
                if len(lst) >= 3 and hm.head(lst[-1]) == P and YI.proper(lst[-3]) and hm.R[lst[-3]] == Y:
                    w = hm.L[lst[-3]]
                    if w > 0 and hm.head(w) == 0:
                        for L in hist[1:]:
                            Lr = list(reversed(L))
                            Pr = [e for e in Lr if cls(e) == "P"]
                            if any(WT.contains(e, w) for e in Pr):
                                ys = [e for e in Lr if cls(e) == "Y"]
                                key = tuple(shape(e, w) for e in Pr) + ("ytop=y" if ys and ys[0] == Y else "ytop=Y",)
                                confs[key] += 1
                                if key not in ex: ex[key] = hm.show(D)
                                for e in Pr:
                                    if WT.contains(e, w): shapes[shape(e, w)] += 1
            hm.truncate(M0); YI._cl.clear(); WT._cw.clear()
    print("P w-term shapes:")
    for k, v in sorted(shapes.items(), key=lambda kv: -kv[1]): print("  ", v, k)
    print("P-region configurations with a w-term:")
    for k, v in sorted(confs.items(), key=lambda kv: -kv[1]): print("  ", v, ex[k], k)
