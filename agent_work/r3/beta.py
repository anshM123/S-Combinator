"""R3 agent: anatomy of real single-wrapper PATTERN-BETA handlers (glue [a1, w, y], a1 != c0, w = b0.c0).
For each: does the V-run (phase 3 renamed back: atoms p, y; bottom g1..g3) open an a1-prefixed element (then the
glue-time alignment with phase 2 applies), F(a1), F(c0), F(b0), I-gen, release form of w (front a released [a1, w]).
usage: beta.py N | beta.py t NK WK NT"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
G = [hm.atom("g%d" % i) for i in range(1, 4)]
def vrun_opens(V, a1, budget=3000):
    """V-run: args(V) ++ [g1, g2, g3]; return (first time an a1-prefixed front occurs or None, outcome)"""
    aV, _ = hm.spine(V)
    st = list(reversed(G)) + list(reversed(aV))
    first = None
    for t in range(budget):
        if len(st) < 3: return first, "hnf"
        h = hm.head(st[-1])
        if h != 0:
            return first, ("y-front" if h == Y else ("p-front" if h == P else ("g-front" if h in G else "other")))
        if first is None and CL.pre(st[-1], a1): first = t
        hm.step(st)
    return first, "budget"
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]
    if CL.lp_reaches(w): return None
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    a1 = hist[gl[0]][-1]
    if a1 == c0: return None
    aV, _ = hm.spine(V); k = len(aV)
    igen = any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist)
    t1, out = vrun_opens(V, a1)
    return ("b0=S" if b0 == 0 else "b0 other", "c0=S.a1" if (hm.L[c0] == 0 and hm.R[c0] == a1) else "c0 other",
            "Igen" if igen else "-", "Vrun opens a1" if t1 is not None else "Vrun never opens a1",
            "F(a1)=" + fc0.F(a1), "F(c0)=" + fc0.F(c0), "Vrun " + out)
if __name__ == "__main__":
    data = list(CL.family(sys.argv[1:]))
    st = collections.Counter(); ex = collections.defaultdict(list); M0 = hm.mark()
    for D in data:
        r = info(D)
        if r is not None:
            st[r] += 1
            if len(ex[r]) < 2: ex[r].append(hm.show(D))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k], ex[k])
