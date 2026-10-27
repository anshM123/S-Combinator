"""Is the opcode word eventually periodic? (main agent) Smallest period p <= PMAX of the last half of the word."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
N, PMAX = int(sys.argv[1]), int(sys.argv[2])
for src in sys.argv[3:]:
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []
    for n in range(N):
        if len(stk) < 3: break
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    t = ops[len(ops) // 2:]
    p = next((p for p in range(1, PMAX + 1) if all(t[i] == t[i + p] for i in range(len(t) - p))), None)
    start = None
    if p:
        start = next(i for i in range(len(ops)) if all(ops[j] == ops[j + p] for j in range(i, len(ops) - p)))
    print(f"{src}: opcode word {'eventually periodic, period %d from step %d' % (p, start) if p else 'not periodic (p <= %d)' % PMAX}; word sample {''.join(map(str, ops[2000:2040]))}")
