"""S1 agent: targeted search for H1-RESIDUAL single-wrapper beta transfers with F(b0) = k1 (b0 calls its first
hole): data D = S K B C with K, B closed (<= NK, NB leaves) and C a P-term from a list of residual-type c0 codes
(and generic P-terms <= NC leaves with one p).  Reports the classification of every single-wrapper beta-P transfer
with H1 residual: F(b0), e3, next-phase outcome.  usage: residtarget.py NK NB NC"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import resid as RD
hm, tg, pg, P = RD.hm, RD.tg, RD.pg, RD.P
if __name__ == "__main__":
    NK, NB, NC = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    closedK = [t for n in range(1, NK + 1) for t in hm.trees(n)]
    closedB = [t for n in range(1, NB + 1) for t in hm.trees(n)]
    Cs = []
    for n in range(2, NC + 1):
        for G in tg.contexts(n):
            C = tg.subst(G, tg.HOLE, P)
            if hm.head(C) == 0 and pg.ordered(C): Cs.append(C)
    st = collections.Counter(); ex = {}
    M0 = hm.mark()
    for C in Cs:
        for K in closedK:
            for B in closedB:
                D = hm.apps(0, K, B, C)
                if pg.ordered(D):
                    r = RD.info(D)
                    if r is not None:
                        st[r] += 1
                        if r not in ex: ex[r] = hm.show(D)
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
