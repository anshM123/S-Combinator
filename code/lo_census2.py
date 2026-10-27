"""LO census with the sharper classifier; saves every endpoint with its class (main agent).
Usage: python lo_census2.py NMAX DEPTH STEPS OUTFILE"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import trees, show
from lo_bt import normalises
from lo_census import endpoint
from classify2 import classify
if __name__ == "__main__":
    NMAX, DEPTH, STEPS, OUT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    kinds = collections.Counter(); ends = {}
    for n in range(1, NMAX + 1):
        for t in trees(n):
            if normalises(t): kinds["normalises"] += 1; continue
            how, u, lvl = endpoint(t, DEPTH)
            kinds[how] += 1
            if how == "bottom": ends.setdefault(u, show(t))
    ck = collections.Counter()
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(f"terms: {dict(kinds)} | distinct hnf-free endpoints: {len(ends)}\n")
        for u, origin in ends.items():
            c = classify(u, STEPS)
            ck[c] += 1
            if c in ("binary counter", "nested counter", "OTHER"):
                f.write(f"{c}\t{show(u)}\tfrom {origin}\n")
        f.write(f"endpoint classes: {dict(ck)}\n")
    print(dict(ck))
