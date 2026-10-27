"""S1 agent: symbolic P-event trace after the creation of the single wrapper w = b0.c0.
P-terms are printed as words over the names c0, w, b0 (and 'k' for a maximal closed subterm, 'p' for p, '?' for a
P-term that is none of these and not an application of P-terms).  For every step after the creation of w we print
the step type (classes of the front three elements) and, when a P- or Y-element is OPENED (front) or a P-element
is glued onto a Y-element, the event with the symbolic front, P-region and whether the Y-top is the bare y.
usage: pevents.py DATUM   |   pevents.py all N   (all ordered single-occurrence pattern-beta cases <= N leaves)"""
import sys, os, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
_cl = {}
def cls(t):
    r = _cl.get(t)
    if r is None:
        a = tg.atoms(t)
        r = "Y" if (a.get(X, 0) or a.get(Y, 0) or a.get(Rr, 0)) else ("P" if a.get(P, 0) else "C")
        _cl[t] = r
    return r
def proper(V):
    a = tg.atoms(V)
    return V != Y and a.get(Y, 0) == 1 and not a.get(X, 0) and not a.get(Rr, 0)
def sym(t, names, depth=0):
    if t in names: return names[t]
    c = cls(t)
    if c == "C": return "k"
    if t == P: return "p"
    if t == Y: return "y"
    if t < 0: return hm.show(t)
    if depth > 6: return "..."
    f, x = hm.L[t], hm.R[t]
    sf, sx = sym(f, names, depth + 1), sym(x, names, depth + 1)
    if " " in sx or "(" in sx and not sx.startswith("("): sx = "(" + sx + ")"
    elif " " in sx: sx = "(" + sx + ")"
    return sf + " " + sx if not sx.startswith("(") else sf + sx
def analyse(D, verbose=True, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    hist.append(tuple(lst))
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]
    if w <= 0 or hm.head(w) != 0: return None
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    a1 = hist[gl[0]][-1]
    if a1 == c0 or cls(a1) != "P": return None
    cr = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == b0 and L[-3] == c0]
    t0 = cr[0]
    names = {c0: "c0", w: "w"}
    if b0 > 0: names[b0] = "b0"
    out = []
    for t in range(t0 + 1, len(hist) - 1):
        L = list(reversed(hist[t]))
        f, b, c = L[0], L[1], L[2]
        typ = cls(f) + cls(b) + cls(c)
        Preg = [sym(e, names) for e in L if cls(e) == "P"]
        Ys = [e for e in L if cls(e) == "Y"]
        ytop = "y" if Ys and Ys[0] == Y else "Y*"
        if typ[0] != "C" or typ in ("CPY",):
            out.append("%d %s front=%s P=[%s] Ytop=%s" % (t, typ, sym(f, names) if cls(f) != "Y" else "Y:" + sym(f, names),
                                                      ", ".join(Preg), ytop))
        elif typ in ("CCP", "CPP"):
            out.append("%d %s P=[%s] Ytop=%s" % (t, typ, ", ".join(Preg), ytop))
    L = list(reversed(hist[-1]))
    out.append("END front=%s pos3=%s" % (sym(L[0], names), sym(L[2], names)))
    if verbose:
        print("D =", hm.show(D), " w =", hm.show(w), " b0 =", hm.show(b0), " c0 =", hm.show(c0), " a1 =", hm.show(a1))
        for o in out: print("   ", o)
    return out
if __name__ == "__main__":
    if sys.argv[1] != "all":
        analyse(hm.parse(sys.argv[1]))
    else:
        N = int(sys.argv[2])
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D):
                    analyse(D)
                hm.truncate(M0); _cl.clear()
