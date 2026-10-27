"""Random sample of larger hnf-free S-terms: is every head run still a counter? (main agent, R' evidence)

Draw random S-terms with NMIN..NMAX leaves, keep those with M35 class bottom (no hnf, Theorem Q10), run STEPS head steps
and classify (lo_census.classify: bounded/linear factor complexity, one affine counter by blocks or gaps, or OTHER).
Prints the OTHER cases for inspection.
Usage: python random_cx.py SAMPLES NMIN NMAX STEPS SEED
"""
import sys, random, collections
sys.setrecursionlimit(1000000)
from symb import show
from lo_bt import cls, MF
from lo_census import classify
from sm_check import rand_term

if __name__ == "__main__":
    N, NMIN, NMAX, STEPS, SEED = (int(x) for x in sys.argv[1:6])
    rng = random.Random(SEED)
    kinds = collections.Counter(); others = []; seen = set(); tries = 0
    while sum(kinds.values()) < N and tries < 200 * N:
        tries += 1
        t = rand_term(rng.randint(NMIN, NMAX), rng)
        if MF[cls(t)] or t in seen: continue
        seen.add(t)
        c = classify(t, STEPS)
        kinds[c] += 1
        if c == "OTHER" and len(others) < 20: others.append(show(t))
    print("hnf-free sample:", dict(kinds))
    for o in others: print("   OTHER:", o)
