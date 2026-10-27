"""R3 agent: Church chains from all S-headed data D = G[p] (G a 1-hole context, <= N leaves; mode 'one') or with
two occurrences of p (mode 'two', <= N leaves).  For every LATER datum D_j (j >= 2; a right comb over p with
closed wrappers, frozen atoms allowed) that makes a proper position-3 transfer, classify that transfer with the
R3-agent theorem classes of cover.py (FH, YD, IGEN, ALPHA, PAF, PAX, LN0, PAM-F, PAM-F', open) - these are the
transfers whose next phase R3 must stop for the bound '<= 2'.  Also counts chain lengths.
usage: chain_cover.py one N | chain_cover.py two N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover, classify as CL, r3census as RC
hm, tg, c3, T3, pg = CL.hm, CL.tg, CL.c3, CL.T3, RC.pg
P, Y = CL.P, CL.Y
def chain(D, st):
    ln = 0
    for ph in range(5):
        o, V, _ = T3.phase(D, 2000)
        if o != "proper3": break
        ln += 1
        if ph >= 1:
            r = cover.classify(D)
            st[("transfer of D_%d" % (ph + 1), r[0] if r else "?")] += 1
        D = tg.subst(tg.subst(V, P, c3.FROZ[ph]), Y, P)
    return ln
if __name__ == "__main__":
    mode, N = sys.argv[1], int(sys.argv[2])
    st = collections.Counter()
    if mode == "one":
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) != 0: hm.truncate(M0); continue
                ln = chain(D, st)
                st[("chain length %d" % ln, "ordered start" if pg.ordered(D) else "non-ordered start")] += 1
                hm.truncate(M0)
    else:
        for n in range(3, N + 1):
            for (t, a, b) in RC.two_hole(n):
                M0 = hm.mark()
                D = RC.place(t, {a, b})
                if hm.head(D) != 0: hm.truncate(M0); continue
                ln = chain(D, st)
                st[("chain length %d" % ln, "ordered start" if pg.ordered(D) else "non-ordered start")] += 1
                hm.truncate(M0)
    for k in sorted(st, key=str): print(k, st[k])
