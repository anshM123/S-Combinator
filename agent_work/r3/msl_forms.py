"""R3 agent: for right-comb data (strict MSL levels = right suffixes of the datum's own level l), classify the
innermost wrapper w = b0.c0 of single-wrapper real handlers: PH / LEV (w = L_j) / LPU (L_j.us) / SLP (S-headed,
not level-prefixed, all P-args level-prefixed) / OTHER; and c0: closed / level-prefixed / other; pattern; F(c0).
usage: msl_forms.py N | msl_forms.py t NK WK NT"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
def levels(D):
    """levels of D = K.l: l, l', ..., p (right suffixes)"""
    out = []; t = hm.R[D]
    while t > 0: out.append(t); t = hm.R[t]
    out.append(P)
    return out
def lpref(t, levs):
    while True:
        if t in levs: return True
        if t <= 0: return False
        t = hm.L[t]
def wform(w, levs):
    if hm.head(w) == P: return "PH"
    if w in levs: return "LEV"
    if lpref(w, levs): return "LPU"
    a, h = hm.spine(w)
    if h == 0 and all(lpref(x, levs) for x in a if P in tg.atoms(x)): return "SLP"
    return "OTHER"
def cform(c0, levs):
    if P not in tg.atoms(c0): return "c0 closed"
    if lpref(c0, levs): return "c0 level-prefixed"
    return "c0 other"
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]; levs = set(levels(D))
    if hm.head(w) == P: return ("PH",)
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    pat = "alpha" if hist[gl[0]][-1] == c0 else "beta"
    return (wform(w, levs), pat, cform(c0, levs), "F(c0)=" + (fc0.F(c0) if hm.head(c0) == 0 else "notS"))
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
