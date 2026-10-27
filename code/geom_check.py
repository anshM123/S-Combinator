"""Random exact checks of two elementary 'geometry' facts of the head machine [a,b,c]++R -> ch(a)++[c, b.c]++R.

(Access) An element that sits at position >= 3 before a step can be at position 1 or 2 after the step only as the copy
of c (when |ch(a)| <= 1), and then b.c (which contains another copy of it) sits directly below it.
(G1) For a tag y: while the lowest list element containing y is not at the front, the elements strictly below it change
only by losing their top element (which is absorbed into the lowest y-element; its copy goes above).
Elements are tracked by identity (unique ids), terms are random S-terms with a marked y-occurrence.
Usage: python geom_check.py TRIALS STEPS SEED
"""
import sys, random
sys.setrecursionlimit(100000)

def spine(t):
    args = []
    while isinstance(t, tuple):
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

def has_y(t, memo):
    if t == "y": return True
    if t == "S": return False
    k = id(t)
    if k not in memo: memo[k] = has_y(t[0], memo) or has_y(t[1], memo)
    return memo[k]

def rand_term(n, rng, py):
    if n == 1: return "y" if rng.random() < py else "S"
    k = rng.randint(1, n - 1)
    return (rand_term(k, rng, py), rand_term(n - k, rng, py))

if __name__ == "__main__":
    trials, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    acc_viol = g1_viol = g1_checks = acc_checks = 0
    for tr in range(trials):
        uid = [0]
        def new(t):
            uid[0] += 1; return (uid[0], t)
        K = [new(rand_term(rng.randint(1, 10), rng, rng.choice([0.0, 0.1]))) for _ in range(rng.randint(3, 8))]
        for n in range(steps):
            if len(K) < 3: break
            (ia, a), (ib, b), (ic, c) = K[0], K[1], K[2]
            ha, aa = spine(a)
            if ha != "S": break
            memo = {}
            ys = [i for i, (_, e) in enumerate(K) if has_y(e, memo)]
            low = ys[-1] if ys else None
            below_before = [u for (u, _) in K[low + 1:]] if low is not None else None
            newK = [new(x) for x in aa] + [(ic, c), new((b, c))] + K[3:]
            # Access: old elements at positions >= 3 (index >= 2) now at index 0 or 1
            old_ids = {u for (u, _) in K[2:]}
            for idx in (0, 1):
                if idx < len(newK) and newK[idx][0] in old_ids:
                    acc_checks += 1
                    ok = newK[idx][0] == ic and len(aa) <= 1 and idx + 1 < len(newK) and newK[idx + 1][1] == (b, c)
                    if not ok: acc_viol += 1
            # G1
            if low is not None and low != 0:
                memo = {}
                ys2 = [i for i, (_, e) in enumerate(newK) if has_y(e, memo)]
                low2 = ys2[-1]
                below_after = [u for (u, _) in newK[low2 + 1:]]
                g1_checks += 1
                if not (below_after == below_before or below_after == below_before[1:]): g1_viol += 1
            K = newK
    print({"access_checks": acc_checks, "access_viol": acc_viol, "G1_checks": g1_checks, "G1_viol": g1_viol})
