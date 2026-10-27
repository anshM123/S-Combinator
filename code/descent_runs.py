"""Unique-redex evolutions with descents (main agent, 2026-10-26).
The list-level condition (all elements normal, second element of spine <= 1 at every step) misses one way a term can
keep exactly one redex: when the list is exactly [S, b, c] with b = S p q (all normal), the head step gives
S c (S p q c), a head normal form whose only redex is the argument S p q c. The evolution then continues inside that
argument, the outer part frozen (a "descent"). This simulates the term-level evolution with exactly one redex at every
step, descents included, and reports the terms (up to NMAX leaves) that survive N steps, with their descent counts.
Usage: python descent_runs.py NMAX N [NMIN]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import has_redex, terms

def evolve(t, N):
    """returns (steps survived, steps at which descents happened, verdict 'alive' / 'normal' / 'multi')"""
    args, h = hc.spine(t)
    L = list(args); desc = []
    for n in range(N):
        while len(L) < 3:                       # head normal form: the one redex must sit in exactly one argument
            red = [e for e in L if has_redex(e)]
            if not red: return n, desc, "normal"
            if len(red) > 1: return n, desc, "multi"
            L = list(hc.spine(red[0])[0]); desc.append(n)
        if any(has_redex(e) for e in L): return n, desc, "multi"
        a, b, c = L[0], L[1], L[2]
        L = list(hc.spine(a)[0]) + [c, hc.app(b, c)] + L[3:]
    return N, desc, "alive"

if __name__ == "__main__":
    NMAX, N = int(sys.argv[1]), int(sys.argv[2])
    NMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    for n in range(NMIN, NMAX + 1):
        alive = collections.Counter(); examples = {}
        for t in terms(n):
            steps, desc, v = evolve(t, N)
            if v == "alive":
                mid = sum(1 for s in desc if s > 0)          # descents after at least one head step
                key = (len(desc) - mid, mid)
                alive[key] += 1
                if key not in examples: examples[key] = (hc.show(t), desc[:12])
        print(f"{n} leaves: alive after {N} steps by (initial descents, mid-run descents): "
              f"{dict(sorted(alive.items()))}", flush=True)
        for key in sorted(examples):
            if key[1] > 0: print(f"   e.g. {key}: {examples[key][0]}  descents at steps {examples[key][1]}", flush=True)
