"""RM census: all terms of N leaves; classify by status and number of outputs; print terms with many outputs."""
import sys, collections
from dm import *
from rm import rm_run
N, BUD, NFB = map(int, sys.argv[1:4])
hist = collections.Counter(); best = []
for t in trees(N):
    args, h = spine(t)
    m = mark()
    st = list(reversed(args))
    status, steps, outs = rm_run(st, BUD, NFB)
    k = len(outs)
    hist[(status, min(k, 50))] += 1
    if status == "budget" and k >= 20:
        szs = [size(c) for _, c in outs[:40]]
        best.append((show(t), k, szs))
    truncate(m)
for k, v in sorted(hist.items(), key=lambda kv: -kv[1])[:25]: print(k, v)
print("long-runners:", len(best))
for b in best[:25]: print(b)
