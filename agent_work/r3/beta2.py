"""R3 agent: for real single-wrapper pattern-beta handlers (glue [a1, w, y], a1 != c0, w = b0.c0): does the
ABSTRACT run of args(c0) ++ [h1, h2] open an a1-prefixed front before its first atom-headed front?  (Then
F(c0) = p follows from F(a1) = p, which the glue forces unless phase 2 re-opens w.y.)  Also F(b0) on (k1, k2) and
how w was released (front a: |args a| and position of w / y).
usage: beta2.py N | beta2.py t NK WK NT"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
H = fc0.H
def opens(g, a1, budget=2000):
    a, h = hm.spine(g)
    st = list(reversed(H)) + list(reversed(a))
    for t in range(budget):
        if len(st) < 3: return False
        if hm.head(st[-1]) != 0: return False
        if CL.pre(st[-1], a1): return True
        hm.step(st)
    return False
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
    tg_ = gl[0]; a1 = hist[tg_][-1]
    if a1 == c0: return None
    prev = hist[tg_ - 1]; a = prev[-1]; aa, _ = hm.spine(a)
    rel = "args(a)=%d" % len(aa)
    aV, _ = hm.spine(V); k = len(aV)
    igen = any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist)
    return ("Igen" if igen else "-", rel, "c0 run opens a1" if opens(c0, a1) else "c0 run never opens a1",
            "F(c0)=" + fc0.F(c0), "F(b0)=" + (fc0.F(b0) if b0 > 0 else "S"))
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
