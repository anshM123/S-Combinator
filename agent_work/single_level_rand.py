"""Robustness check of the single-level claim on larger random closed K (up to W leaves, frozen atoms allowed):
every proper transfer of K.p has a p-headed innermost wrapper."""
import sys, random, collections
import hm, chain3 as c3, invq_fast as F
P, Y = c3.P, c3.Y
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); W = int(sys.argv[3])
    M0 = hm.mark(); st = collections.Counter(); bad = []
    for it in range(N):
        K = F.rand_term(random.randint(1, W), frozen=(it % 3 == 0))
        if hm.head(K) != 0: hm.truncate(M0); F._cls.clear(); continue
        r, Vs = c3.phase(hm.app(K, P), 5000)
        st[r] += 1
        for V in Vs:
            ws = []; t = V
            while t != Y: ws.append(hm.L[t]); t = hm.R[t]
            ok = hm.head(ws[-1]) == P
            st["inner p-headed" if ok else "INNER NOT p-headed"] += 1
            if not ok and len(bad) < 5: bad.append((hm.show(K), hm.show(V)))
        hm.truncate(M0); F._cls.clear()
    print(st); print(bad)
