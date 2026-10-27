"""S1 agent: test WP = 'every list (from the first list to the transfer) whose P-region is exactly [U, w] (two
elements, the lower one the wrapper w of the single-wrapper handler) has the bare y as its first Y-element', and
WY = 'whenever some P-element contains w, the first Y-element is the bare y' and WG = 'every subterm M.e of a list
element with M a P-term containing w and e a Y-term has e = y', on single-wrapper transfers of ORDERED
single-occurrence data, split IGEN / non-IGEN.  usage: wptest.py N | wptest.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ytopinv as YI
hm, tg, pg, P, Y = YI.hm, YI.tg, YI.pg, YI.P, YI.Y
cls = YI.cls
_cw = {}
def contains(t, w):
    key = (t, w)
    r = _cw.get(key)
    if r is None:
        if t == w: r = True
        elif t <= 0: r = False
        else: r = contains(hm.L[t], w) or contains(hm.R[t], w)
        _cw[key] = r
    return r
def wg_ok(t, w, seen):
    # every subterm M.e with M P containing w and e Y has e = y
    st = [t]
    while st:
        s = st.pop()
        if s <= 0 or s in seen: continue
        seen.add(s)
        M, e = hm.L[s], hm.R[s]
        if cls(M) == "P" and cls(e) == "Y" and e != Y and contains(M, w): return False
        st.append(M); st.append(e)
    return True
def info(D, budget=1500):
    X, Rr = YI.X, YI.Rr
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    hist.append(tuple(lst))
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and YI.proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]
    if w <= 0 or hm.head(w) != 0: return None
    aV, _ = hm.spine(V); k = len(aV)
    igen = any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist[:-1])
    wp = wy = wg = True; seen = set()
    for t in range(1, len(hist)):
        L = list(reversed(hist[t]))
        Pr = [e for e in L if cls(e) == "P"]
        ys = [e for e in L if cls(e) == "Y"]
        ytop_y = bool(ys) and ys[0] == Y
        if len(Pr) == 2 and Pr[1] == w and not ytop_y: wp = False
        if any(contains(e, w) for e in Pr) and not ytop_y and t < len(hist) - 1: wy = False
        if wg:
            for e in L:
                if not wg_ok(e, w, seen): wg = False; break
    return ("IGEN" if igen else "nonIGEN", "WP" if wp else "WP-fails", "WY" if wy else "WY-fails", "WG" if wg else "WG-fails")
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
                hm.truncate(M0); YI._cl.clear(); _cw.clear()
    else:
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0); YI._cl.clear(); _cw.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
