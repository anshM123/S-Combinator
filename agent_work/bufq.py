"""FAST version of the buffer / two-C / sigma_C tests on general single-level phase-3 shapes W.p' (memoised
classes, only the region above the Y-part is scanned, 800-step budget).
Events: buf = a C-element glued onto a P'-element; two = C-region >= 2 while the P'-region is exactly [bare p'];
sig = sigma_C (C-front, the only P'-element at position 2, bare y at position 3); Cafter = #C right after sigma_C."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg, p3shape_pos3 as S3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
MEMO = {}
def cls(t):
    r = MEMO.get(t)
    if r is None:
        a = tg.atoms(t)
        r = 3 if (a.get(X) or a.get(Y) or a.get(Rr)) else (2 if a.get(P) else (1 if a.get(C) else 0))
        MEMO[t] = r
    return r
def top(lst):
    """classes from the front down to (and including) the first Y element"""
    out = []
    for e in reversed(lst):
        k = cls(e); out.append((e, k))
        if k == 3: break
    return out
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); Wn = int(sys.argv[3]); pc = float(sys.argv[4])
st = collections.Counter(); ex = {}; M0 = hm.mark()
for it in range(N):
    Wt = S3.rand_term(random.randint(2, Wn), pc)
    if C not in tg.atoms(Wt) or hm.head(Wt) != 0 or not pg.ordered(Wt): hm.truncate(M0); MEMO.clear(); continue
    lst = [Rr, Y, X, hm.app(Wt, P)]
    buf = two = False; cafter = None; pend = False
    for t in range(800):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        tp = top(lst)
        if pend and cafter is None: cafter = sum(1 for e, k in tp if k == 1); pend = False
        ks = [k for e, k in tp]
        nC = ks.count(1); Pel = [e for e, k in tp if k == 2]
        if nC >= 2 and Pel == [P]: two = True
        if len(tp) >= 3 and tp[1][1] == 1 and tp[2][1] == 2: buf = True
        if cafter is None and len(tp) >= 3 and tp[0][1] == 1 and tp[1][1] == 2 and len(Pel) == 1 and lst[-3] == Y: pend = True
        hm.step(lst)
    proper = len(lst) >= 3 and hm.head(lst[-1]) == P and S3.proper(lst[-3])
    key = ("buf" if buf else "-", "two" if two else "-", "sig C=%s" % (min(cafter, 3) if cafter is not None else "-"),
           "PROPER" if proper else "no")
    st[key] += 1
    if proper: ex.setdefault(key, hm.show(Wt))
    hm.truncate(M0); MEMO.clear()
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("example", k, v)
