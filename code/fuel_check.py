"""Disprover: is the number of 'writes behind a live control' bounded by the initial fuel?

Tags x (control, above) and y (target); marked closed occurrences ('M', tag, term) as in corw_check.py (zero tests
allowed). A W-event is a clean write b.c (b closed at position 2, c containing y at position 3) while some list element
contains x but not y. Initial fuel F0 = (closed list elements lying below some data element) + (closed spine arguments
that follow a data argument in the same spine, summed over all subterm occurrences, tree count).
Random initial lists satisfying J1/J2 (x above y) but NOT F1/F2. Reports runs with #W > F0 (fuel regeneration).
Usage: python fuel_check.py TRIALS STEPS SEED
"""
import sys, random
from corw_check import is_mark, spine, tags, open_top, j1j2, rand_term, rand_marked
sys.setrecursionlimit(100000)

def fuel(K):
    memo = {}
    d = [bool(tags(e, memo)) for e in K]
    f = sum(1 for i in range(len(K)) if not d[i] and any(d[:i]))
    stack = list(K)
    while stack:
        t = stack.pop()
        if t == "S": continue
        if is_mark(t): stack.append(t[2]); continue
        h, args = spine(t)
        seen_data = False
        for a in args:
            ad = bool(tags(a, memo))
            if not ad and seen_data: f += 1
            seen_data = seen_data or ad
        stack.extend(args)
        if is_mark(h): stack.append(h[2])
    return f

def show(t):
    if t == "S": return "S"
    if is_mark(t): return "[" + t[1] + ":" + show(t[2]) + "]"
    h, args = spine(t)
    s = show(h)
    for a in args:
        s += show(a) if a == "S" else "(" + show(a) + ")"
    return s

if __name__ == "__main__":
    trials, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    runs = 0; worst = []; tot_w = 0
    tries = 0
    while runs < trials and tries < 300 * trials:
        tries += 1
        K = [rand_marked(rng.randint(1, 12), rng, ["x", "y"]) for _ in range(rng.randint(3, 7))]
        memo = {}
        tg = set().union(*[tags(e, memo) for e in K])
        if tg != {"x", "y"} or not j1j2(K, memo): continue
        runs += 1
        K0 = list(K); F0 = fuel(K); W = 0
        for n in range(steps):
            if len(K) < 3: break
            memo = {}
            a, b, c = K[0], K[1], K[2]
            if not tags(b, memo) and "y" in tags(c, memo) and \
                    any("x" in tags(e, memo) and "y" not in tags(e, memo) for e in K):
                W += 1
            K = open_top(a) + [c, (b, c)] + K[3:]
        tot_w += W
        if W > F0:
            worst.append((W - F0, W, F0, [show(e) for e in K0]))
    worst.sort(reverse=True)
    print(f"runs {runs}, total W-events {tot_w}, runs with W > F0: {len(worst)}")
    for w in worst[:6]:
        print("  excess", w[0], "W", w[1], "F0", w[2], " K0 =", " , ".join(w[3]))
