"""R3 agent: random Church chains (random S-headed data with one or two occurrences of p, 4..N leaves, as in
chain_len_rand.py); classify every transfer made by a LATER datum D_j (j >= 2) with the R3-agent theorem classes
(cover.py).  usage: chain_cover_rand.py SEED NMAX COUNT"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover, classify as CL, r3search as RS
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y = CL.P, CL.Y
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); M = int(sys.argv[3])
    st = collections.Counter(); M0 = hm.mark(); ex = []
    for it in range(M):
        n = random.randint(4, N)
        D = RS.rtree(n, random.choice([1, 1, 1, 2]))
        if hm.head(D) != 0: hm.truncate(M0); continue
        ordered = RS.pg.ordered(D); ln = 0; D0 = D
        for ph in range(5):
            o, V, _ = T3.phase(D, 2000)
            if o != "proper3": break
            ln += 1
            if ph >= 1:
                r = cover.classify(D)
                k = r[0] if r else "?"
                st[("transfer of D_%d" % (ph + 1), k)] += 1
                if k not in ("FH", "ALPHA", "IGEN") and len(ex) < 8: ex.append((hm.show(D0), hm.show(D), k))
            D = tg.subst(tg.subst(V, P, c3.FROZ[ph]), Y, P)
        st[("chain length %d" % ln, "ordered start" if ordered else "non-ordered start")] += 1
        hm.truncate(M0)
    for k in sorted(st, key=str): print(k, st[k])
    for e in ex: print("later transfer not FH/ALPHA/IGEN:", e)
