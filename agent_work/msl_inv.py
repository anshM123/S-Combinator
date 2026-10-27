"""Exact MSL invariant check (hand proof 2026-10-27 ~02:00).  Lv = right combs over p with closed wrappers
(inductive: p, or d.l with d closed and l in Lv); LP(e) = some left-spine prefix of e is in Lv; good(e) = LP(e) or
every P spine argument of e is LP.  MSLI(L): regions CL* P* Y*, every S-headed subterm ordered (spine args
non-decreasing in CL < P < Y), and either |P| >= 3 (then Lemma AB takes over) or
  MQ  : P = [] or some P-element is LP
  MT  : |P| = 2 -> each non-LP P-element has only LP P-arguments
  MA1h: every subterm l.u with l in Lv and u in P has good(u)
  GLh : every subterm w.q with w in P, q in Y has good(w)
Run from args(d1) ++ [L2, y, x.y, r] for every multi-level right comb d1.(d2.(...(dk.p))), k >= 2, closed d_i."""
import sys, collections, random
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
MEMO = {}
def cls(t):
    k = ('c', t)
    if k not in MEMO:
        a = tg.atoms(t)
        MEMO[k] = 2 if (a.get(X) or a.get(Y) or a.get(Rr)) else (1 if a.get(P) else 0)
    return MEMO[k]
def lv(t):
    k = ('v', t)
    if k not in MEMO:
        MEMO[k] = (t == P) or (t > 0 and cls(hm.L[t]) == 0 and lv(hm.R[t]))
    return MEMO[k]
def lp(e):
    t = e
    while True:
        if lv(t): return True
        if t <= 0: return False
        t = hm.L[t]
def good(e):
    if lp(e): return True
    args, _ = hm.spine(e)
    return all(lp(s) for s in args if cls(s) == 1)
def hered(t):
    """(ordered, ma1h, glh) for all subterms of t"""
    k = ('h', t)
    if k in MEMO: return MEMO[k]
    if t <= 0: r = (True, True, True)
    else:
        l, u = hm.L[t], hm.R[t]
        a, b = hered(l), hered(u)
        o, m, g = a[0] and b[0], a[1] and b[1], a[2] and b[2]
        if hm.head(t) == 0:
            args, _ = hm.spine(t)
            cs = [cls(s) for s in args]
            if any(cs[i] > cs[i + 1] for i in range(len(cs) - 1)): o = False
        if lv(l) and cls(u) == 1 and not good(u): m = False
        if cls(l) == 1 and cls(u) == 2 and not good(l): g = False
        r = (o, m, g)
    MEMO[k] = r
    return r
def check(L):
    cl = [cls(e) for e in L]
    if any(cl[i] > cl[i + 1] for i in range(len(cl) - 1)): return "REGIONS"
    if not all(hered(e)[0] for e in L): return "ORDERED"
    Pel = [e for e, c in zip(L, cl) if c == 1]
    if len(Pel) >= 3: return "BIG"
    if Pel and not any(lp(e) for e in Pel): return "MQ"
    if len(Pel) == 2:
        for e in Pel:
            if not lp(e):
                args, _ = hm.spine(e)
                if not all(lp(s) for s in args if cls(s) == 1): return "MT"
    if not all(hered(e)[1] for e in L): return "MA1h"
    if not all(hered(e)[2] for e in L): return "GLh"
    return None
def run(D, steps, st, ex):
    lst = [Rr, Y, X, D]
    hm.step(lst)
    for s in range(steps):
        v = check(list(reversed(lst)))
        if v:
            st[v] += 1
            if v != "BIG": ex.setdefault(v, (hm.show(D), s, hm.show_list(lst, maxn=6)[:160]))
            return
        if len(lst) < 3 or hm.step(lst) < 0:
            st["stuck/hnf"] += 1; return
    st["budget"] += 1
if __name__ == "__main__":
    N = int(sys.argv[1]); steps = int(sys.argv[2])
    st = collections.Counter(); ex = {}
    data = [D for D in c3.rcombs(N) if hm.R[D] != P and hm.head(D) == 0]
    M0 = hm.mark()
    for D in data:
        run(D, steps, st, ex)
        st["runs"] += 1
        hm.truncate(M0); MEMO.clear()
    print(st)
    for k, v in ex.items(): print(k, v)
