"""S1 agent: computational audit of the lemmas of the hand proof of (S1) (LOG 07:11).
For every S-headed ORDERED single-occurrence datum (<= N leaves, or random), run phase 2 from L_1 while the front is
S-headed and |P| <= 2 (stop checking once |P| >= 3: AB regime), and check at every list:
  F    : list is CL* P* Y*
  C1   : no 2P term (U.V with U, V P-terms) is alone in the P-region
  C2   : no subterm K.Z with K closed and Z a 2P term
  FA   : if a 2P term Z' is in the P-region with Ytop y, or Z'.y is a subterm, then every 2P term on the right spine
         of Z' is GOOD (created earlier by a step [k, left Z, right Z, y, ...])
and, if the run ends in a proper single-wrapper transfer w.y (w = b0.c0 S-headed):
  FW   : every subterm M.w with M a P-term, and every pair-top U of a P-region [U, w], is in the X-sequence of c0
  FB   : every list with P-region [X_i, w] (i >= 1) and Ytop y is preceded (or equal) by args(c0) ++ [w, y, ...]
  S1   : for a glue [a1, w, y] with a1 a P-term != c0: (S1) holds before it.
usage: lemcheck.py N | lemcheck.py rand SEED NMAX COUNT"""
import sys, os, collections, random
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
def is2P(t): return t > 0 and cls(t) == "P" and cls(hm.L[t]) == "P" and cls(hm.R[t]) == "P"
_kz = {}
def hasKZ(t):
    if t <= 0: return False
    r = _kz.get(t)
    if r is None:
        f, x = hm.L[t], hm.R[t]
        r = (cls(f) == "C" and is2P(x)) or hasKZ(f) or hasKZ(x)
        _kz[t] = r
    return r
def subterms(t, acc):
    st = [t]
    while st:
        s = st.pop()
        if s <= 0 or s in acc: continue
        acc.add(s); st.append(hm.L[s]); st.append(hm.R[s])
def proper(V):
    a = tg.atoms(V)
    return V != Y and a.get(Y, 0) == 1 and not a.get(X, 0) and not a.get(Rr, 0)
def check(D, st, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    hm.step(lst)
    good = set(); viol = set()
    for t in range(budget):
        L = list(reversed(lst))
        cl = [cls(e) for e in L]
        s = "".join(cl)
        ok = True
        # F
        i = 0
        while i < len(s) and s[i] == "C": i += 1
        j = i
        while j < len(s) and s[j] == "P": j += 1
        if any(ch != "Y" for ch in s[j:]): viol.add("F")
        Pr = L[i:j]
        if len(Pr) >= 3: break
        ytop_y = j < len(L) and L[j] == Y
        if len(Pr) == 1 and is2P(Pr[0]): viol.add("C1")
        if any(hasKZ(e) for e in L): viol.add("C2")
        # FA
        cands = [z for z in Pr if is2P(z) and ytop_y]
        for e in L:
            if cls(e) == "Y":
                sub = set(); subterms(e, sub)
                for u in sub:
                    if hm.R[u] == Y and is2P(hm.L[u]): cands.append(hm.L[u])
        for z in cands:
            q = z
            while is2P(q):
                if q not in good: viol.add("FA")
                q = hm.R[q]
        hist.append(tuple(lst))
        if len(L) < 3 or hm.head(L[0]) != 0: break
        # creation record for GOOD
        if len(L) >= 4 and cls(L[1]) == "P" and cls(L[2]) == "P" and L[3] == Y:
            good.add(hm.app(L[1], L[2]))
        hm.step(lst)
    for v in viol: st["VIOL " + v] += 1
    st["runs"] += 1
    L = list(reversed(lst))
    if not (len(L) >= 3 and hm.head(L[0]) == P and proper(L[2]) and hm.R[L[2]] == Y): return viol
    w = hm.L[L[2]]
    if w <= 0 or hm.head(w) != 0: return viol
    st["single-wrapper transfers"] += 1
    b0, c0 = hm.L[w], hm.R[w]
    Xs = [c0]
    while True:
        a, h = hm.spine(Xs[-1])
        pa = [u for u in a if cls(u) == "P"]
        if h != 0 or len(pa) != 1: break
        Xs.append(pa[0])
    Xset = set(Xs)
    ac0, _ = hm.spine(c0) if hm.head(c0) == 0 else ([], 0)
    s1time = None
    for t, H in enumerate(hist):
        L = list(reversed(H))
        if s1time is None and hm.head(c0) == 0 and len(L) >= len(ac0) + 2 and L[:len(ac0)] == ac0 and L[len(ac0)] == w and L[len(ac0) + 1] == Y:
            s1time = t
        sub = set()
        for e in L: subterms(e, sub)
        for u in sub:
            if hm.R[u] == w and cls(hm.L[u]) == "P" and hm.L[u] not in Xset: viol.add("FW-sub"); st["VIOL FW-sub"] += 1
        Pr = [e for e in L if cls(e) == "P"]
        ys = [e for e in L if cls(e) == "Y"]
        if len(Pr) == 2 and Pr[1] == w:
            if Pr[0] not in Xset: viol.add("FW-pair"); st["VIOL FW-pair"] += 1
            elif Pr[0] != c0 and ys and ys[0] == Y and s1time is None:
                viol.add("FB"); st["VIOL FB"] += 1
        if len(L) >= 3 and L[1] == w and L[2] == Y and cls(L[0]) == "P" and L[0] != c0:
            st["beta-P glues"] += 1
            if s1time is None: viol.add("S1"); st["VIOL S1"] += 1
    return viol
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        v = check(D, st)
        for k in v:
            if k not in ex: ex[k] = hm.show(D)
    if sys.argv[1] != "rand":
        N = int(sys.argv[1])
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): feed(D)
                hm.truncate(M0); _cl.clear(); _kz.clear()
    else:
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0); _cl.clear(); _kz.clear()
    for k in sorted(st): print(k, st[k])
    for k in sorted(ex): print("example", k, ex[k])
