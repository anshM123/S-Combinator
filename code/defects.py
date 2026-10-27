"""Defects of a locally periodic opcode word (main agent): dominant local period p0; clusters of positions i with
ops[i] != ops[i - p0]; gaps between cluster starts and their differences."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc
N = int(sys.argv[1])
for src in sys.argv[2:]:
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []
    for n in range(N):
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    best = max(range(1, 40), key=lambda p: sum(ops[i] == ops[i - p] for i in range(p, len(ops))))
    bad = [i for i in range(best, len(ops)) if ops[i] != ops[i - best]]
    clusters = []
    for i in bad:
        if clusters and i - clusters[-1][-1] <= 2 * best: clusters[-1].append(i)
        else: clusters.append([i])
    starts = [c[0] for c in clusters]
    g = [y - x for x, y in zip(starts, starts[1:])]
    d = [y - x for x, y in zip(g, g[1:])]
    print(f"{src}: local period {best}; {len(clusters)} defect clusters; gaps {g[:10]} … {g[-5:]}; gap differences (last 8) {d[-8:]}")
