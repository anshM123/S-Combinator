"""S1 agent: anatomy of the H1-RESIDUAL single-wrapper pattern-beta transfers (ordered single-occurrence data):
F(b0) = first atom front of the abstract run of args(b0) ++ [k1, k2] (k1, k2 fresh), and of c0's run on (h1, h2):
the h1-front's first argument u1 (head) and the element e3 at position 3; the next phase's outcome.
usage: resid.py N | resid.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg
import classify as CL
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
K1, K2 = hm.atom("k"), hm.atom("m")
H1, H2 = hm.atom("h"), hm.atom("g")
def proper(V):
    a = tg.atoms(V)
    return V != Y and a.get(Y, 0) == 1 and not a.get(X, 0) and not a.get(Rr, 0)
def front(code, z1, z2, budget=3000):
    a, h = hm.spine(code)
    st = [z2, z1] + list(reversed(a))
    for t in range(budget):
        if len(st) < 3: return ("hnf", None)
        if hm.head(st[-1]) != 0: return ("front", list(reversed(st)))
        hm.step(st)
    return ("budget", None)
def name(t, d):
    h = hm.head(t)
    return d.get(h, hm.NAMES.get(h, "S" if h == 0 else "?"))
def info(D):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]
    if w <= 0 or hm.head(w) != 0: return None
    b0, c0 = hm.L[w], hm.R[w]
    if hm.head(c0) != 0 or (b0 > 0 and hm.head(b0) != 0): return None
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    a1 = hist[gl[0]][-1]
    if a1 == c0 or not tg.atoms(a1).get(P, 0): return None
    k, Lc = front(c0, H1, H2)
    if k != "front" or hm.head(Lc[0]) != H1: return None
    args, _ = hm.spine(Lc[0])
    if (args and args[0] == H2) or (not args and len(Lc) >= 3 and Lc[2] == H2): return None
    d = {H1: "h1", H2: "h2", K1: "k1", K2: "k2", P: "p"}
    u1 = name(args[0], d) + "-headed" if args else "j=0"
    e3 = ("h2" if Lc[2] == H2 else ("contains h2" if tg.atoms(Lc[2]).get(H2, 0) else "h2-free")) if len(Lc) >= 3 else "none"
    kb, Lb = front(b0, K1, K2) if b0 > 0 else ("front", [K1, K2])
    Fb = name(Lb[0], d) if kb == "front" else kb
    o3 = CL.phase3(V)[0]
    return ("u1 " + u1, "e3 " + e3, "F(b0)=" + Fb, o3)
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
                hm.truncate(M0)
    else:
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0)
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
