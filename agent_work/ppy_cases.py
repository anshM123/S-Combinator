"""In single-level runs, inspect every (P,P,Y) step: front a (S-headed P-element), b (P), c (Y).
Record: is b p-headed; the classes of a's spine args (CL / PH = p-headed P / Q = other P); whether a's last arg is
p-headed."""
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
        for s in range(400):
            if len(st) < 3: break
            A, B, Cc = st[-1], st[-2], st[-3]
            if hm.head(A) == 0 and F.cls(A) == "P" and F.cls(B) == "P" and F.cls(Cc) == "Y":
                args, _ = hm.spine(A)
                sig = ("b:" + acls(B), "args:" + ",".join(acls(x) for x in args))
                stats[sig] += 1
                ex.setdefault(sig, (hm.show(K), hm.show(A)[:60], hm.show(B)[:40]))
            if hm.step(st) < 0: break
        hm.truncate(M0); F._cls.clear()
    for k, v in stats.most_common(40): print(v, k, ex[k])
