"""Phase-3 stress test.  Build phase-3 data D3 = W'.(K0.p') or W'.p' where W' instantiates a dirty-wrapper skeleton
with p -> c (frozen) and K -> random closed terms (1..KMAX leaves); run generically and look for proper transfers
(p'-headed stuck front, proper right comb over y at position 2 or 3)."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
C = c3.FROZ[0]
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return hm.app(rand_term(k), rand_term(n - k))
KMAX = 10
def K(): return rand_term(random.randint(1, KMAX))
def rcomb_c(depth):
    t = C
    for _ in range(depth): t = hm.app(K(), t)
    return t
SKELS = {
 "K(Kc)": lambda: rcomb_c(2), "K(K(Kc))": lambda: rcomb_c(3), "Kc": lambda: rcomb_c(1),
 "c(Kc)": lambda: hm.app(C, rcomb_c(1)), "Kc(K(Kc))": lambda: hm.app(rcomb_c(1), rcomb_c(2)),
 "K(Kc)(K(K(Kc)))": lambda: hm.app(rcomb_c(2), rcomb_c(3)),
 "c": lambda: C, "c(K(Kc))": lambda: hm.app(C, rcomb_c(2)),
 "rc_a.rc_b": lambda: hm.app(rcomb_c(random.randint(1, 3)), rcomb_c(random.randint(1, 3))),
 "rc.rc.rc": lambda: hm.apps(rcomb_c(random.randint(1, 3)), rcomb_c(random.randint(1, 3)), rcomb_c(random.randint(1, 3))),
}
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); KMAX = int(sys.argv[3])
    M0 = hm.mark(); stats = collections.Counter(); hits = []
    for it in range(N):
        name = random.choice(list(SKELS))
        # 1-3 levels: each level a skeleton instance or a closed wrapper
        nlev = random.randint(1, 3)
        D = P
        for _ in range(nlev):
            w = SKELS[name]() if random.random() < 0.7 else K()
            D = hm.app(w, D)
        if C not in tg.atoms(D): hm.truncate(M0); continue
        if hm.head(D) != 0: stats[(name, "headless")] += 1; hm.truncate(M0); continue
        r, Vs = c3.phase(D, 4000)
        stats[(name, r)] += 1
        if r == "proper" and len(hits) < 10: hits.append((name, hm.show(D)[:120], [hm.show(v)[:80] for v in Vs]))
        hm.truncate(M0)
    for k, v in sorted(stats.items()): print(v, k)
    print("PROPER phase-3 hits:", len(hits))
    for h in hits: print(h)
