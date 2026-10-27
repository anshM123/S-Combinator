"""Delay terms under parallel evaluation (main agent): for every S-term <= NMAX leaves that normalises, D = number of
ReplaceAll passes to its normal form; for each D, the smallest term, and whether the head spine length before the last
pass differs from the normal form's (so an opening reader can tell 'finished' from 'not yet')."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import trees, show
import hc
from parallel_eval import step_fn
NMAX, CAP = int(sys.argv[1]), int(sys.argv[2])
P = step_fn()
best = {}
for n in range(1, NMAX + 1):
    for tt in trees(n):
        t = hc.from_tuple(tt); hist = [t]
        start = len(hc.L); grew = False
        for k in range(CAP):
            u = P(t)
            if u == t: break
            t = u; hist.append(t)
            if len(hc.L) - start > 200000: grew = True; break
        else: continue
        if grew: continue
        D = len(hist) - 1
        if D == 0: continue
        nf_sp = len(hc.spine(hist[-1])[0])
        prev_sp = [len(hc.spine(h)[0]) for h in hist[:-1]]
        distinct = all(sp != nf_sp for sp in prev_sp)      # every unfinished stage has a different head spine
        if D not in best or (distinct and not best[D][2]) or (distinct == best[D][2] and n < best[D][1]):
            best[D] = (show(tt), n, distinct, prev_sp, nf_sp)
for D in sorted(best):
    src, n, distinct, prev, nf = best[D]
    print(f"D={D:3d}: {src} ({n} leaves); head spines before the end {prev[:12]}{'…' if len(prev) > 12 else ''}, at the end {nf}; "
          f"'finished' always distinguishable: {distinct}")
