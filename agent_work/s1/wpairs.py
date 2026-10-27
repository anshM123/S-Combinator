"""S1 agent: anatomy of the w-bottom pairs.  For every single-wrapper transfer of ORDERED single-occurrence data
(<= N leaves) with wrapper w = b0.c0 (S-headed), list in time order the events after the creation of w:
  'pair X'   : the P-region is exactly [X, w] (two elements, w the lower one) and this is new at this step,
  'open Q'   : the front Q has w among its spine arguments (Q is opened), with the spine args after w,
  'Ytop'     : the first Y element below the P-region at each pair event.
Prints a signature per case (X given symbolically: c0, S.a1, other) and counts signatures.
usage: wpairs.py N"""
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
def info(D, budget=1500):
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
    cr = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == b0 and L[-3] == c0]
    if not cr: return ("no creation",)
    t0 = cr[0]
    names = {c0: "c0", w: "w", b0: "b0", hm.app(c0, w): "c0.w", Y: "y"}
    def nm(e):
        if e in names: return names[e]
        return cls(e) + "?"
    ev = []; lastpair = None
    for t in range(t0 + 1, len(hist)):
        L = list(reversed(hist[t]))
        Pidx = [i for i, e in enumerate(L) if cls(e) == "P"]
        Pr = [L[i] for i in Pidx]
        if len(Pr) == 2 and Pr[1] == w:
            if lastpair != (Pr[0], t - 1):
                ytop = L[Pidx[-1] + 1] if Pidx[-1] + 1 < len(L) else None
                ev.append("pair[%s,w]/%s" % (nm(Pr[0]), "y" if ytop == Y else "Ytop!=y"))
            lastpair = (Pr[0], t)
        f = L[0]
        if t < len(hist) - 1 and f > 0:
            a, h = hm.spine(f)
            if w in a:
                k = max(i for i, e in enumerate(a) if e == w)
                after = a[k + 1:]
                pos3 = L[1 + len(after)] if len(L) > 1 + len(after) else None
                ev.append("open(%s|w|%d after)%s" % (nm(a[k - 1]) if k > 0 else "-", len(after),
                          "" if after else ("/next=" + nm(L[1]) + "," + nm(L[2]))))
    return tuple(ev)
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = {}
    for n in range(2, N + 1):
        CS = tg.contexts(n); M0 = hm.mark()
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) == 0 and pg.ordered(D):
                r = info(D)
                if r is not None:
                    st[r] += 1
                    if r not in ex: ex[r] = hm.show(D)
            hm.truncate(M0)
            _cl.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], " ".join(k))
