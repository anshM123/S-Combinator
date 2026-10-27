"""General single-level phase-3-shaped data W.p' (W random, contains c, ordered).  Test:
  (B1) if a buffer (C-element glued onto a P'-element) is ever created, no proper position-3 transfer follows;
  (B2) if the C-region ever has >= 2 elements while the P'-top is the bare p', no proper position-3 transfer."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg, p3shape_pos3 as S3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); Wn = int(sys.argv[3]); pc = float(sys.argv[4])
st = collections.Counter(); ex = {}; M0 = hm.mark()
for it in range(N):
    Wt = S3.rand_term(random.randint(2, Wn), pc)
    if C not in tg.atoms(Wt) or hm.head(Wt) != 0 or not pg.ordered(Wt): hm.truncate(M0); continue
    lst = [Rr, Y, X, hm.app(Wt, P)]
    buf = False; two = False
    for t in range(3000):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        L = list(reversed(lst))
        cls = [E.cls(e) for e in L]
        nC = cls.count("C")
        firstP = next((e for e, k in zip(L, cls) if k == "P"), None)
        if nC >= 2 and firstP == P: two = True
        if cls[1] == "C" and cls[2] == "P": buf = True
        hm.step(lst)
    proper = len(lst) >= 3 and hm.head(lst[-1]) == P and S3.proper(lst[-3])
    st[("buffer" if buf else "nobuf", "C2@p'" if two else "-", "PROPER" if proper else "no")] += 1
    if proper and (buf or two): ex.setdefault((buf, two), hm.show(Wt))
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("COUNTEREXAMPLE", k, v)
