"""Agent U round 4: search for a REVERSE pass (supply n -> layer counter k) inside one head run.
Template [P..., X_k, S^n, SS, SS, r, w] with X_k = ctx^k[B0] (symbolic k, case splits), P = short list of closed
constants, n concrete.  A hit = a later configuration P ++ [X_{k+d}] ++ S^{n-e} ++ [SS, SS] with d >= 1, e >= 1
(for every k-branch that is not a failure).  Usage: python agent_u_reverse.py MAXCTX NMAX"""
import sys, collections, itertools
from agent_u_ctxnest import run, isC, spine
from symb import trees, show
def contexts(maxn):
    out = []
    def holes(t):
        if t == "S": yield "#"; return
        for l in holes(t[0]): yield (l, t[1])
        for r in holes(t[1]): yield (t[0], r)
    for n in range(2, maxn + 1):
        for t in trees(n): out.extend(holes(t))
    return out
SS = ("S", "S")
B0 = (("S", SS), SS)
small = [t for n in range(1, 4) for t in trees(n)]
prefixes = [[c] for c in small] + [[c, d] for c in small for d in small]
def test(ctx, P, n, maxsteps=120):
    fams = [(ctx, B0)]
    start = list(P) + [("C", 0, "k", 0)] + ["S"] * n + [SS, SS, "r", "w"]
    def stop(K, br, steps):
        L = len(P)
        if len(K) < L + 3 or K[:L] != list(P) or not (isC(K[L]) and K[L][1] == 0): return None
        m = 0
        while L + 1 + m < len(K) and K[L + 1 + m] == "S": m += 1
        if L + 2 + m < len(K) and K[L + 1 + m] == SS and K[L + 2 + m] == SS:
            return (K[L][2:], m)
        return None
    return run(start, fams, stop, maxsteps=maxsteps, cap=5)
if __name__ == "__main__":
    MAXCTX, NMAX = int(sys.argv[1]), int(sys.argv[2])
    cs = contexts(MAXCTX)
    cnt = collections.Counter(); hits = []
    for ctx in cs:
        for P in prefixes:
            res = {}
            for n in range(1, NMAX + 1):
                out = test(ctx, P, n)
                good = [o for o in out if isinstance(o[1], tuple)]
                bad = [o for o in out if not isinstance(o[1], tuple)]
                for o in good:
                    (v, d), m = o[1]
                    cnt[(d, m - n)] += 1
                res[n] = (good, bad)
            ok = all(res[n][0] and not res[n][1] and all(o[1][0][1] >= 1 and o[1][1] < n for o in res[n][0]) for n in res)
            if ok: hits.append((ctx, P, {n: [(o[0], o[1], o[2]) for o in res[n][0]] for n in res}))
    print("contexts", len(cs), "prefixes", len(prefixes))
    print("transition types (d_k, d_n):", cnt.most_common(12))
    print("reverse hits:", len(hits))
    for h in hits[:10]: print(h)
