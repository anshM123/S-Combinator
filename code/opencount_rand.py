"""Random test of the bounded-reopening observation (opencount.py) on large terms.

Uniform random binary trees with N leaves (Lukasiewicz word + cycle lemma). For every sampled term whose M35 class
is in F, run the provenance head machine; report the largest number of openings of one application / leaf
occurrence and the step count. A run that does not halt within the budget is reported (it would contradict
BEKW Question 10 or the step bound).
Usage: python opencount_rand.py N COUNT SEED [BUDGET]
"""
import sys, random, collections
from opencount import cl, F, run
from symb import show

def random_tree(n, rng):
    word = [2] * (n - 1) + [0] * n
    rng.shuffle(word)
    # cycle lemma: rotate so that every proper prefix has (#2s) >= (#0s), i.e. the word parses
    bal, low, cut = 1, 1, 0
    for i, x in enumerate(word):
        bal += 1 if x == 2 else -1
        if bal < low:
            low, cut = bal, i + 1
    word = word[cut:] + word[:cut]
    pos = 0
    def parse():
        nonlocal pos
        x = word[pos]; pos += 1
        if x == 0:
            return "S"
        l = parse(); r = parse()
        return (l, r)
    t = parse()
    assert pos == len(word)
    return t

if __name__ == "__main__":
    N, COUNT, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    BUDGET = int(sys.argv[4]) if len(sys.argv) > 4 else 20 * N + 200
    rng = random.Random(SEED)
    dl, da, steps_hist = collections.Counter(), collections.Counter(), collections.Counter()
    nf = nb = 0; worst = None
    for _ in range(COUNT):
        t = random_tree(N, rng)
        if not F[cl(t)]:
            nb += 1; continue
        halted, steps, ml, ma, _, _ = run(t, BUDGET)
        if not halted:
            print("NOT HALTED within budget (F class):", show(t), flush=True); continue
        nf += 1; dl[ml] += 1; da[ma] += 1; steps_hist[min(steps // 10 * 10, 1000)] += 1
        if worst is None or (ma, ml, steps) > worst[0]:
            worst = ((ma, ml, steps), show(t))
    print(f"N={N}: sampled {COUNT}, F-class {nf}, bottom {nb}")
    print(f"  max opens of one leaf occ: {dict(sorted(dl.items()))}")
    print(f"  max opens of one app occ:  {dict(sorted(da.items()))}")
    print(f"  steps (binned by 10): {dict(sorted(steps_hist.items()))}")
    print(f"  worst (app, leaf, steps): {worst}")
