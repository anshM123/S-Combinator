"""Long robustness check and counter type for parallel-robust candidates (main agent)."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
from rand_radix import radix
STEPS = int(sys.argv[1]); P = step_fn()
for src in sys.argv[2:]:
    args, h = hc.spine(hc.from_tuple(parse(src))); lo = list(args); par = list(args); ops = []; agree = True; n = 0
    for n in range(STEPS):
        a, b, c = lo[0], lo[1], lo[2]; ch, _ = hc.spine(a); ops.append(len(ch)); lo = ch + [c, hc.app(b, c)] + lo[3:]
        a, b, c = par[0], par[1], par[2]; ch2, _ = hc.spine(a); par = ch2 + [c, hc.app(b, c)] + [P(e) for e in par[3:]]
        if len(lo) != len(par) or lo[0] != par[0]: agree = False; break
    r = radix(ops)
    print(f"{src}: parallel == LO for {'all ' + str(STEPS) if agree else 'only ' + str(n)} steps; list length {len(lo)}; "
          f"radix law: {('base %d' % r[0]) if r else 'none'}; DAG {len(hc.L)}", flush=True)
