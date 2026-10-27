"""Regenerate every distinct hnf-free endpoint of the census (terms <= NMAX leaves), without classification (main agent).
Output: one endpoint per line (show form), in data/endpoints_NMAX.txt."""
import sys
sys.setrecursionlimit(1000000)
from symb import trees, show
from lo_bt import normalises
from lo_census import endpoint
NMAX, DEPTH, OUT = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
seen = set(); n_terms = 0
with open(OUT, "w", encoding="utf-8") as f:
    for n in range(1, NMAX + 1):
        for t in trees(n):
            n_terms += 1
            if normalises(t): continue
            how, u, lvl = endpoint(t, DEPTH)
            if how == "bottom" and u not in seen:
                seen.add(u); f.write(show(u) + "\n")
        f.flush(); print(f"n <= {n}: {n_terms} terms, {len(seen)} distinct endpoints", flush=True)
