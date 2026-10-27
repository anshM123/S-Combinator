"""Head-spine length per parallel pass (main agent), for N passes, using the parallel head machine of Lemma PH on the
list of head arguments (each pass: one head step + one pass inside every deeper element). Saves the sequence."""
import sys, json, time
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
src, N, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
P = step_fn()
args, h = hc.spine(hc.from_tuple(parse(src))); lst = list(args); seq = [len(lst)]; t0 = time.time()
for n in range(N):
    if len(lst) < 3: break
    a, b, c, rest = lst[0], lst[1], lst[2], lst[3:]
    ch, hh = hc.spine(a)
    lst = ch + [c, hc.app(b, c)] + [P(e) for e in rest]
    seq.append(len(lst))
    if n % 50 == 0: print(f"  pass {n}: spine {len(lst)}, DAG nodes {len(hc.L)}, {time.time() - t0:.0f}s", flush=True)
json.dump(seq, open(out, "w"))
print(f"{src}: {len(seq)} spine lengths saved; last 20: {seq[-20:]}")
