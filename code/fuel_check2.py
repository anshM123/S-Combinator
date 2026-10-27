"""fuel_check refined: a W-event counts only if the front element is x-only, b closed, c contains y, AND after the step some
list element still contains x but not y (the control survives the write). Prints the best excess example with a trace of
its first W-events. Usage: python fuel_check2.py TRIALS STEPS SEED"""
import sys, random
from corw_check import is_mark, spine, tags, open_top, j1j2, rand_marked
from fuel_check import fuel, show
sys.setrecursionlimit(100000)

def xonly(e, memo):
    t = tags(e, memo); return "x" in t and "y" not in t

def runW(K, steps, trace=False):
    W = 0; out = []
    for n in range(steps):
        if len(K) < 3: break
        memo = {}
        a, b, c = K[0], K[1], K[2]
        cand = xonly(a, memo) and not tags(b, memo) and "y" in tags(c, memo)
        K2 = open_top(a) + [c, (b, c)] + K[3:]
        memo = {}
        if cand and any(xonly(e, memo) for e in K2):
            W += 1
            if trace and len(out) < 8: out.append((n, show(a), show(b), show(c)))
        K = K2
    return W, out

if __name__ == "__main__":
    trials, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    runs = 0; res = []; tries = 0
    while runs < trials and tries < 300 * trials:
        tries += 1
        K = [rand_marked(rng.randint(1, 12), rng, ["x", "y"]) for _ in range(rng.randint(3, 7))]
        memo = {}
        tg = set().union(*[tags(e, memo) for e in K])
        if tg != {"x", "y"} or not j1j2(K, memo): continue
        runs += 1
        F0 = fuel(K); W, _ = runW(list(K), steps)
        res.append((W - F0, W, F0, K))
    res.sort(key=lambda r: -r[0])
    print("runs", runs, " runs with W > F0:", sum(1 for r in res if r[0] > 0), " max W:", max(r[1] for r in res))
    for ex, W, F0, K in res[:3]:
        print(f"excess {ex} W {W} F0 {F0}  K0 = " + " , ".join(show(e) for e in K))
        _, tr = runW(list(K), steps, trace=True)
        for row in tr: print("     step", row[0], " front", row[1], "| b", row[2], "| c", row[3][:80])
