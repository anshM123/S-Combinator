"""Innermost wrapper w of real phase-2 proper (position-3) transfers, classified against the datum's own levels
(strict): PH (p-headed), LEV (w = L_j exactly), LPU (w = L_j.u1..un, n >= 1), SLP (not LP, all P-args strictly LP),
OTHER.  Phase-3 outcome per class."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, ml_wrappers as MW
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def cls(t):
    a = tg.atoms(t)
    if a.get(X) or a.get(Y) or a.get(Rr): return 2
    if a.get(P): return 1
    return 0
def form(w, Ls):
    if hm.head(w) == P: return "PH"
    if w in Ls[1:]: return "LEV"
    t = w; n = 0
    while t > 0:
        t = hm.L[t]; n += 1
        if t in Ls[1:]: return "LPU%d" % min(n, 3)
    args, _ = hm.spine(w)
    if all(MW.is_LP(a, Ls) for a in args if cls(a) == 1): return "SLP"
    return "OTHER"
mode = sys.argv[1]
if mode == "ex":
    data = [D for D in c3.rcombs(int(sys.argv[2])) if hm.head(D) == 0]
else:
    NK, WK, NT = map(int, sys.argv[2:5])
    Ks = [t for n in range(1, NK + 1) for t in hm.trees(n) if hm.head(t) == 0]
    wr = [t for n in range(1, WK + 1) for t in hm.trees(n)]
    tails = [P]; fr = [(P, 1)]
    while fr:
        nf = []
        for t, sz in fr:
            for d in wr:
                if sz + hm.size(d) <= NT:
                    u = hm.app(d, t); tails.append(u); nf.append((u, sz + hm.size(d)))
        fr = nf
    data = [hm.app(K, T) for T in tails if T != P for K in Ks]
M0 = hm.mark(); st = collections.Counter(); ex = {}
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 == "proper3":
        Ls = MW.levels(D2)
        inner = V
        while hm.R[inner] != Y: inner = hm.R[inner]
        w = hm.L[inner]
        f = form(w, Ls)
        nw = 0; t = V
        while t != Y: nw += 1; t = hm.R[t]
        D3 = tg.subst(tg.subst(V, P, C), Y, P)
        o3, _, _ = T3.phase(D3, 1500)
        st[(f, "nwrap=%d" % min(nw, 3), o3)] += 1
        ex.setdefault((f, min(nw, 3)), (hm.show(D2), hm.show(V)))
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
for k in sorted(ex): print(k, ex[k])
