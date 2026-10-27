"""Factor complexity of capped opcode words (main agent): opcodes capped at CAPV, last 3/4 of STEPS steps; p(n) for
n = 8..512 and ratios p(2n)/p(n) (morphic words have p(n) = O(n^2), ratio <= ~4 asymptotically)."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
src, STEPS, CAPV = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []
for n in range(STEPS):
    if len(stk) < 3: break
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
    ops.append(min(len(ch), CAPV)); stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
s = ops[len(ops) // 4:]
p = {}
for m in (8, 16, 32, 64, 128, 256, 512):
    p[m] = len({tuple(s[i:i + m]) for i in range(len(s) - m + 1)})
print(src, f"({len(ops)} steps, cap {CAPV}):", p, "ratios:", [round(p[2 * m] / p[m], 2) for m in (8, 16, 32, 64, 128, 256)])
