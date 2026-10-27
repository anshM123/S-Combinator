"""Single-level phase-3-shaped data W.p' with w = W[c:=p] GOOD.  Classify by: w in Lv (right comb over p, i.e. W a
c-comb) or not, and by the number of C-arguments of W.  Count proper position-3 transfers per class."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg, p3shape_pos3 as S3, msl_inv as MI
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); Wn = int(sys.argv[3]); pc = float(sys.argv[4])
M0 = hm.mark(); st = collections.Counter(); ex = {}
for it in range(N):
    Wt = S3.rand_term(random.randint(2, Wn), pc)
    if C not in tg.atoms(Wt) or hm.head(Wt) != 0 or not pg.ordered(Wt): hm.truncate(M0); continue
    w = tg.subst(Wt, C, P)
    if not MI.good(w): hm.truncate(M0); MI.MEMO.clear(); continue
    args, _ = hm.spine(w)
    nC = sum(1 for a in args if MI.cls(a) == 1)
    key = ("comb" if MI.lv(w) else ("LP" if MI.lp(w) else "SLP"), "nC=%d" % min(nC, 3))
    st[key] += 1
    lst = [Rr, Y, X, hm.app(Wt, P)]
    s, k = hm.run(lst, 3000)
    if s == "stuck" and hm.head(lst[-1]) == P and len(lst) >= 3 and S3.proper(lst[-3]):
        st[key + ("PROPER",)] += 1
        ex.setdefault(key, hm.show(Wt))
    hm.truncate(M0); MI.MEMO.clear()
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("example", k, v)
