"""R3 agent: for real single-wrapper pattern-beta handlers w.y (glue [a1, w, y], a1 != c0): does phase 2 ever run
c0 on the holes (w, y), i.e. reach a list args(c0) ++ [w, y, ...]?  And on (w, anything)?
usage: beta3.py N | beta3.py t NK WK NT | beta3.py o N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
def startswith(L, pref):
    k = len(pref)
    return len(L) >= k and list(reversed(L[-k:])) == pref
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
    ac0, _ = hm.spine(c0)
    wy = any(startswith(L, ac0 + [w, Y]) for L in hist)
    wany = any(startswith(L, ac0 + [w]) for L in hist)
    aV, _ = hm.spine(V)
    igen = any(startswith(L, aV) for L in hist)
    return ("Igen" if igen else "-", "c0 on (w, y)" if wy else ("c0 on (w, .)" if wany else "c0 never on w"),
            "F(c0)=" + fc0.F(c0))
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
