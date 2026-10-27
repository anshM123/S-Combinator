"""Single-level data D2 = K.p (K closed): does every proper transfer have a p-HEADED wrapper?  (If so, Lemma FH blocks
phase 3 for the canonical chain F-type -> K-wrap counter.)  Exhaustive over closed K <= N leaves."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y = c3.P, c3.Y
if __name__ == "__main__":
    N = int(sys.argv[1]); stats = collections.Counter(); bad = []
    KS = [K for n in range(1, N + 1) for K in hm.trees(n)]
    M0 = hm.mark()
    for K in KS:
        if True:
            D = hm.app(K, P)
            r, Vs = c3.phase(D, 4000)
            stats[r] += 1
            if r == "proper":
                for V in Vs:
                    ws = []; t = V
                    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
                    has_ph = any(hm.head(w) == P for w in ws)
                    stats["V with p-headed wrapper" if has_ph else "V WITHOUT p-headed wrapper"] += 1
                    if not has_ph and len(bad) < 10: bad.append((hm.show(K), hm.show(V)))
            hm.truncate(M0)
    print(stats)
    for b in bad: print(b)
