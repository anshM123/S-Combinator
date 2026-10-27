"""R3 agent: coverage of real proper position-3 phase-2 transfers by the R3-agent theorems (hypotheses checked per
case).  Classes, first that applies:
  FH     some wrapper p-/frozen-headed or with leftmost path to p/frozen (OTD fh_rcomb, FH1, FHL)   [old, Lean]
  YD     outermost wrapper = bare S (YD yd_bareS)                                                  [old, Lean]
  IGEN   phase 2's list starts with args(V) at some time before the transfer   (R3A.lean igen_main)  [no hyp.]
  ALPHA  single wrapper glued in pattern alpha [c0, w, y]                     (R3A.lean alpha_main) [no hyp.]
  PAF    single wrapper, F(c0) not h1/h2 (handler-only)                        (R3A.lean paf_main)
  PAX    single wrapper, phase 3 never reaches a c0'-prefixed front (handler-only)          (to formalise)
  PAM-F  multi-wrapper, innermost vn = b0.c0 with F(c0) not h1/h2, B0 ok at the first Ln-opening  (to formalise)
  open   none of the above.
Also records the phase-3 outcome (sanity: never proper).
usage: cover.py N | cover.py t NK WK NT | cover.py o N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0, mw
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
def reaches_x1(V, c0, budget=3000):
    """phase 3 (concrete) of a single-wrapper handler: does it ever reach a c0'-prefixed front?"""
    D3 = tg.subst(tg.subst(V, P, C), Y, P); c03 = tg.subst(c0, P, C)
    st = [Rr, Y, X, D3]
    for t in range(budget):
        if len(st) < 3 or hm.head(st[-1]) != 0: return False
        if CL.pre(st[-1], c03): return True
        hm.step(st)
    return True   # budget: unknown, count as reaching
def classify(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    multi = "S" if len(ws) == 1 else "M"
    o3 = CL.phase3(V)[0]
    if any(CL.lp_reaches(w) for w in ws): return ("FH", multi, o3)
    if ws[0] == 0: return ("YD", multi, o3)
    aV, _ = hm.spine(V); k = len(aV)
    if any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist): return ("IGEN", multi, o3)
    vn = ws[-1]
    if vn <= 0: return ("open", multi, o3)
    b0, c0 = hm.L[vn], hm.R[vn]
    if hm.head(c0) != 0: return ("open-c0notS", multi, o3)
    nh = fc0.F(c0) not in ("h1", "h2")
    if multi == "S":
        gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == vn and L[-3] == Y]
        if gl and hist[gl[0]][-1] == c0: return ("ALPHA", multi, o3)
        if hm.L[c0] == 0 and any(len(L) >= 3 and L[-1] == hm.app(c0, vn) and L[-3] == Y for L in hist):
            return ("PBT", multi, o3)
        import h1ok as H1
        ac0, _ = hm.spine(c0)
        c0wy = any(len(L) >= len(ac0) + 2 and list(reversed(L[-(len(ac0) + 2):])) == ac0 + [vn, Y] for L in hist)
        if c0wy and H1.h1ok(c0) != "H1 RESIDUAL": return ("BETA0", multi, o3)
        if nh: return ("PAF", multi, o3)
        if not reaches_x1(V, c0): return ("PAX", multi, o3)
        return ("open", multi, o3)
    allnh = True
    for w in ws:
        if w <= 0 or hm.head(w) != 0 or hm.L[w] <= -1 or hm.head(hm.R[w]) != 0 or hm.head(hm.L[w]) != 0:
            allnh = False; break
        if fc0.F(hm.R[w]) in ("h1", "h2"): allnh = False; break
    if allnh: return ("NHALL", multi, o3)
    r = mw.info(D)
    if r is not None and r[1] == "Ln never opened": return ("LN0", multi, o3)
    b0ok = r is not None and r[0] != "FH" and (r[2] in ("B0: bare y", "B0: y-free", "B0: none"))
    if nh and b0ok: return ("PAM-F", multi, o3)
    b0np = r is not None and r[0] != "FH" and r[2] != "B0: PROPER y-comb"
    if nh and (b0 == 0 or b0np): return ("PAM-F'", multi, o3)
    return ("open", multi, o3)
if __name__ == "__main__":
    data = list(CL.family(sys.argv[1:]))
    st = collections.Counter(); ex = collections.defaultdict(list); M0 = hm.mark()
    for D in data:
        r = classify(D)
        if r is not None:
            st[r] += 1
            if len(ex[r[0]]) < 3: ex[r[0]].append(hm.show(D))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
    tot = sum(st.values()); op = sum(v for k, v in st.items() if k[0].startswith("open"))
    print("total", tot, "open", op)
    for k in sorted(ex): print("example", k, ex[k])
