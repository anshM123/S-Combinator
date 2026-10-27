"""Profile of a head run (main agent): opcode factor complexity p(n), run-length structure of the most informative
opcode gaps, and growth of the list length. Usage: python run_profile.py TERM STEPS"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc
src = sys.argv[1]; STEPS = int(sys.argv[2])
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
ops = []; lens = []
for n in range(STEPS):
    if len(stk) < 3: print("hnf at", n); break
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
    ops.append(len(ch)); stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    if n % (STEPS // 8) == 0: lens.append((n, len(stk)))
s = ops[len(ops) // 4:]
pc = {m: len({tuple(s[i:i + m]) for i in range(len(s) - m + 1)}) for m in (8, 16, 32, 64, 128)}
print(f"{src}: factor complexity p(n) on the last 3/4:", pc, " list length:", lens)
for op in sorted(set(s)):
    pos = [i for i, x in enumerate(ops) if x == op]
    g = [b - a for a, b in zip(pos, pos[1:])]
    cnt = collections.Counter(g[len(g) // 4:])
    big = sorted(cnt.items(), key=lambda kv: -kv[1])[:10]
    print(f"  op {op}: {len(pos)} occurrences; most common gaps {big}")
