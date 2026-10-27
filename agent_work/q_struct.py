"""Single-level runs: for every Q-element (S-headed P-element) in the P-region at every step, record whether it has
a Q-arg (non-p-headed P spine arg), and its position in P (from the bottom: 0 = bottom, 1 = second from bottom, ...),
and whether a p-headed element lies above it / a p-headed P-element below it."""
import sys, random, collections
import hm, invq_fast as F
def acls(t):
    c = F.cls(t)
    if c == "P": return "PH" if hm.head(t) == F.P else "Q"
    return c
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2])
    M0 = hm.mark(); stats = collections.Counter(); ex = {}
    for it in range(N):
        K = F.rand_term(random.randint(1, 16), frozen=(it % 2 == 1))
        if hm.head(K) != 0: hm.truncate(M0); F._cls.clear(); continue
        a, _ = hm.spine(K)
        st = list(reversed(a + [F.P, F.Y, hm.app(F.X, F.Y), F.Rr]))
        for s in range(300):
            if len(st) < 3: break
            L = list(reversed(st))
            Pidx = [i for i, e in enumerate(L) if F.cls(e) == "P"]
            for rank, i in enumerate(reversed(Pidx)):
                e = L[i]
                if hm.head(e) != 0: continue
                args, _ = hm.spine(e)
                hasQ = any(acls(x) == "Q" for x in args)
                above = any(hm.head(L[j]) == F.P for j in range(i))
                below = any(F.cls(L[j]) == "P" and hm.head(L[j]) == F.P for j in range(i + 1, len(L)))
                key = (min(rank, 2), "hasQarg" if hasQ else "noQarg", "above" if above else "", "below" if below else "")
                stats[key] += 1
                ex.setdefault(key, (hm.show(K), s, hm.show(e)[:60]))
            if hm.step(st) < 0: break
        hm.truncate(M0); F._cls.clear()
    for k, v in sorted(stats.items()): print(v, k, ex[k])
