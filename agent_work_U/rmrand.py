"""Random RM runs: report terms with many emitted outputs and print their output-size sequences."""
import sys, random, collections
from dm import *
from rm import rm_run
SEED, N, LMIN, LMAX, BUD, NFB = map(int, sys.argv[1:7])
random.seed(SEED)
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rand_term(k), rand_term(n - k))
hist = collections.Counter(); keep = []
for it in range(N):
    m = mark()
    t = rand_term(random.randint(LMIN, LMAX))
    args, h = spine(t)
    status, steps, outs = rm_run(list(reversed(args)), BUD, NFB)
    k = len(outs)
    hist[(status, min(k // 10 * 10, 100))] += 1
    if k >= 40:
        szs = [size(c) for _, c in outs[:80]]
        keep.append((show(t), status, k, szs))
    truncate(m)
print(dict(sorted(hist.items())))
for kk in keep[:20]: print(kk[0], kk[1], kk[2], kk[3][:50])
