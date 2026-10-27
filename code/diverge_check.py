"""First divergence between the leftmost-outermost run and the parallel head machine (main agent)."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
from waiting_nf import is_nf
P = step_fn()
src, N = sys.argv[1], int(sys.argv[2])
args, h = hc.spine(hc.from_tuple(parse(src))); lo = list(args); par = list(args)
for n in range(N):
    if len(lo) != len(par) or lo[0] != par[0]:
        print(f"first divergence before step {n}: LO length {len(lo)}, parallel length {len(par)}; "
              f"fronts equal: {lo[0] == par[0]}; LO front NF: {is_nf(lo[0])}")
        diff = [i for i, (u, v) in enumerate(zip(lo, par)) if u != v]
        print("  positions that differ:", diff[:10])
        break
    a, b, c = lo[0], lo[1], lo[2]; ch, _ = hc.spine(a); lo = ch + [c, hc.app(b, c)] + lo[3:]
    a, b, c = par[0], par[1], par[2]; ch2, _ = hc.spine(a); par = ch2 + [c, hc.app(b, c)] + [P(e) for e in par[3:]]
else:
    print(f"no divergence in {N} steps (front and list length agree)")
lo_len = []; args, h = hc.spine(hc.from_tuple(parse(src))); L2 = list(args)
for n in range(12): lo_len.append(len(L2)); a, b, c = L2[0], L2[1], L2[2]; ch, _ = hc.spine(a); L2 = ch + [c, hc.app(b, c)] + L2[3:]
print("LO list lengths, steps 0-11:", lo_len)
