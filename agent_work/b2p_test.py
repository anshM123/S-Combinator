"""General single-level phase-3-shaped data W.p'.  (B2') after a sigma_C step (C-front opened while the only
P'-element is glued onto the bare y), if the C-region then has >= 2 elements, is a proper position-3 transfer
still possible?  Also record the C-count right after the first sigma_C for runs that DO transfer properly."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg, p3shape_pos3 as S3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); Wn = int(sys.argv[3]); pc = float(sys.argv[4])
st = collections.Counter(); ex = {}; M0 = hm.mark()
for it in range(N):
    Wt = S3.rand_term(random.randint(2, Wn), pc)
    if C not in tg.atoms(Wt) or hm.head(Wt) != 0 or not pg.ordered(Wt): hm.truncate(M0); continue
    lst = [Rr, Y, X, hm.app(Wt, P)]
    sig = None; pending = False
    for t in range(3000):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        a, b, c = lst[-1], lst[-2], lst[-3]
        L = list(reversed(lst)); cls = [E.cls(e) for e in L]
        if pending and sig is None:
            sig = cls.count("C"); pending = False
        if sig is None and cls[0] == "C" and cls[1] == "P" and cls.count("P") == 1 and c == Y: pending = True
        hm.step(lst)
    if pending and sig is None:
        L = list(reversed(lst)); sig = [E.cls(e) for e in L].count("C")
    proper = len(lst) >= 3 and hm.head(lst[-1]) == P and S3.proper(lst[-3])
    key = ("no sigma_C" if sig is None else "sigma_C, C after=%d" % min(sig, 3), "PROPER" if proper else "no")
    st[key] += 1
    if proper: ex.setdefault(key[0], hm.show(Wt))
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("example", k, v)
