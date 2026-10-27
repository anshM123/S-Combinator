"""Clocks under parallel evaluation (main agent): S-terms (<= NMAX leaves) whose ReplaceAll size sequence is eventually
linear (constant difference d > 0 over passes 20..N) — elements that keep a steady count while they wait."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import trees, show
import hc
from parallel_eval import step_fn, size
NMAX, N = int(sys.argv[1]), int(sys.argv[2])
P = step_fn()      # one pass is a pure function of the node: one memo for everything
found = collections.defaultdict(list)
for n in range(1, NMAX + 1):
    for tt in trees(n):
        t = hc.from_tuple(tt); s = [size(t)]; nf = False
        for k in range(N):
            u = P(t)
            if u == t: nf = True; break
            t = u; s.append(size(t))
            if s[-1] > 10 ** 7: break
        if nf or len(s) < N + 1: continue
        d = [b - a for a, b in zip(s[20:], s[21:])]
        if len(set(d)) == 1 and d[0] > 0: found[d[0]].append(show(tt))
        elif len(set(d)) <= 3 and max(d) < 20 and min(d) > 0:
            p = next((p for p in (2, 3, 4, 6) if all(d[i] == d[i + p] for i in range(len(d) - p))), None)
            if p: found[f"periodic diffs p={p} {d[:p]}"].append(show(tt))
for k, v in sorted(found.items(), key=lambda kv: str(kv[0])):
    print(f"{k}: {len(v)} terms, e.g. {v[:5]}")
