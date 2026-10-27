"""Phase-3-shaped single-level data D3 = W.p' that make a PROPER transfer at position 3, restricted to W whose
phase-2 preimage w = W[c:=p] is GOOD (generous Lv: level-prefixed or all P-args level-prefixed).  For each hit,
print the level chains needed (the Lv-prefixes of w / of its P-args), i.e. the datum tails a phase-2 run would
need for w to be good in the STRICT sense."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg, p3shape_pos3 as S3, msl_inv as MI
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def lvprefix(e):
    t = e
    while True:
        if MI.lv(t): return t
        if t <= 0: return None
        t = hm.L[t]
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); Wn = int(sys.argv[3])
M0 = hm.mark(); st = collections.Counter(); hits = {}
for it in range(N):
    Wt = S3.rand_term(random.randint(2, Wn), 0.15)
    if C not in tg.atoms(Wt) or hm.head(Wt) != 0 or not pg.ordered(Wt): hm.truncate(M0); continue
    w = tg.subst(Wt, C, P)
    if not MI.good(w): st["not good"] += 1; hm.truncate(M0); MI.MEMO.clear(); continue
    st["good"] += 1
    lst = [Rr, Y, X, hm.app(Wt, P)]
    s, k = hm.run(lst, 3000)
    if s == "stuck" and hm.head(lst[-1]) == P and len(lst) >= 3 and S3.proper(lst[-3]):
        args, _ = hm.spine(w)
        if MI.lp(w): chains = [hm.show(lvprefix(w))]
        else: chains = [hm.show(lvprefix(a)) for a in args if MI.cls(a) == 1]
        key = hm.show(Wt)
        if key not in hits: hits[key] = (chains, hm.show_list(lst, maxn=5)[:120])
        st["PROPER"] += 1
    hm.truncate(M0); MI.MEMO.clear()
print(st)
for k, v in hits.items(): print(k, v)
