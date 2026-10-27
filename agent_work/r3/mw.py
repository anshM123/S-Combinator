"""R3 agent: multi-wrapper real handlers V = v1.(...(vn.y)) (n >= 2, non-FH).  Phase 3 (concrete, p' = P, c = C):
find the first Ln'-prefixed front (Ln' = vn'.p'), record the bottom B after args(vn') ++ [p'] and the class of B[0]
(y-free / bare y / proper y-comb / other); F(b0), F(c0) for vn = b0.c0; I-gen (phase 2's list starts with args(V))
and I-Ln (phase 2's list starts with args(vn) ++ [y]); phase-3 outcome.
usage: mw.py N | mw.py t NK WK NT | mw.py o N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
def startswith(L, pref):
    k = len(pref)
    return len(L) >= k and list(reversed(L[-k:])) == pref
def b0class(e):
    if e is None: return "none"
    if e == Y: return "bare y"
    if Y not in tg.atoms(e): return "y-free"
    if T3.S3.proper(e): return "PROPER y-comb"
    return "other y-term"
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    if len(ws) < 2: return None
    if any(CL.lp_reaches(w) for w in ws): return ("FH",)
    vn = ws[-1]; b0, c0 = hm.L[vn], hm.R[vn]
    aV, _ = hm.spine(V); igen = any(startswith(L, aV) for L in hist)
    aLn, _ = hm.spine(hm.app(vn, Y)); iln = any(startswith(L, aLn) for L in hist)
    D3 = tg.subst(tg.subst(V, P, C), Y, P); vn3 = tg.subst(vn, P, C); Ln3 = hm.app(vn3, P)
    k0 = len(hm.spine(vn3)[0])
    s3 = [Rr, Y, X, D3]; B0 = None; opened = False
    for t in range(3000):
        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
        if CL.pre(s3[-1], Ln3):
            hm.step(s3); opened = True
            B0 = s3[-(k0 + 2)] if len(s3) >= k0 + 2 else None
            break
        hm.step(s3)
    o3 = CL.phase3(V)[0]
    return ("Igen" if igen else ("I-Ln" if iln else "-"), "Ln opened" if opened else "Ln never opened",
            "B0: " + b0class(B0), "F(b0)=" + (fc0.F(b0) if b0 > 0 else "S"), "F(c0)=" + fc0.F(c0), o3)
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
