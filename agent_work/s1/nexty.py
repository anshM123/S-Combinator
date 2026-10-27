"""S1 agent: test candidate invariants for (S1) on single-wrapper transfers of ORDERED single-occurrence data.
For the wrapper w = b0.c0 (S-headed, contains p) of the handler w.y, after the creation of w and before the
transfer, record every OPENING of a front Q that has w among its spine arguments, as
   (prefix kind, what follows w)   where prefix kind = 'c0.w' if the spine prefix ending at the LAST occurrence of w
   is c0.w, else 'X.w' (X P-class), 'k.w' (X closed) ...
and 'what follows w' = 'y' if the next argument (next spine arg of Q, or else list position 2 or 3 as the step
reads it) is the bare y, else its class.
usage: nexty.py N    |   nexty.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
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
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    a1 = hist[gl[0]][-1]
    pat = "alpha" if a1 == c0 else ("beta-P" if cls(a1) == "P" else "beta-C")
    cr = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == b0 and L[-3] == c0]
    if not cr: return (pat, "no creation")
    t0 = cr[0]
    z = hist[t0][-4] if len(hist[t0]) >= 4 else None
    ev = set()
    for t in range(t0 + 1, len(hist) - 1):
        L = list(reversed(hist[t]))
        f = L[0]
        a, h = hm.spine(f)
        if w not in a: continue
        k = max(i for i, e in enumerate(a) if e == w)
        pre = hm.L[f] if k == len(a) - 1 else None
        # prefix node X.w
        node = f
        for _ in range(len(a) - 1 - k): node = hm.L[node]
        X_ = hm.L[node]
        kind = "c0.w" if X_ == c0 else (cls(X_) + ".w")
        nxt = a[k + 1] if k + 1 < len(a) else L[2]     # after opening: args ++ [L[2], L[1].L[2]]
        ev.add((kind, "y" if nxt == Y else cls(nxt)))
    return (pat, "z=y" if z == Y else "z!=y", tuple(sorted(ev)))
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = info(D)
        if r is not None:
            st[r] += 1
            if r not in ex: ex[r] = hm.show(D)
    if sys.argv[1] != "rand":
        N = int(sys.argv[1])
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): feed(D)
                hm.truncate(M0); _cl.clear()
    else:
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0); _cl.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
