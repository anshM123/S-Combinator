"""Task 4 probe: re-execution rounds with comb parity.  Run [C_n, J, K, Z] (C_n = S^n.S left comb) and record the
depths of NEW left combs (depth >= 2, not a descent step) appearing at the front; summarise the first new depth as a
function of n = 2..11.  Report (J, K, Z) whose first-new-depth map is not affine in n (e.g. parity-dependent)."""
import sys, collections
import hm
def comb(n):
    t = 0
    for _ in range(n): t = hm.app(0, t)
    return t
def depth(t):
    d = 0
    while t > 0 and hm.L[t] == 0: d += 1; t = hm.R[t]
    return d
def new_combs(lst, steps, want=3):
    st = list(reversed(lst)); prev = -5; out = []
    for i in range(steps):
        if len(st) < 3: break
        d = depth(st[-1])
        if i > 0 and d >= 2 and d != prev - 1: out.append(d)
        if len(out) >= want: break
        prev = d
        if hm.step(st) < 0: break
    return out
if __name__ == "__main__":
    smax = int(sys.argv[1]); steps = int(sys.argv[2])
    terms = [t for n in range(1, smax + 1) for t in hm.trees(n)]
    combs = {n: comb(n) for n in range(2, 12)}
    M0 = hm.mark(); hits = []
    for J in terms:
        for K in terms:
            for Z in terms[:5]:
                f = {}
                for n in range(2, 12):
                    r = new_combs([combs[n], J, K, Z], steps)
                    hm.truncate(M0)
                    f[n] = tuple(r)
                firsts = [f[n][0] if f[n] else None for n in range(2, 12)]
                if None in firsts: continue
                diffs = [firsts[i + 1] - firsts[i] for i in range(len(firsts) - 1)]
                if len(set(diffs)) > 1 and len(set(firsts)) > 3:
                    hits.append((hm.show(J), hm.show(K), hm.show(Z), firsts))
    print("non-affine first-new-comb maps:", len(hits))
    for h in hits[:25]: print(h)
