"""Front elements at the steps where the opcode first reaches a new maximum (main agent)."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
def bshow(i, budget=60):
    out = []
    def go(i):
        if len(out) > budget: return
        if i == 0: out.append("S"); return
        if i < 0: out.append("a"); return
        go(hc.L[i])
        r = hc.R[i]
        if r > 0: out.append("("); go(r); out.append(")")
        else: go(r)
    go(i); s = "".join(out)
    return s[:budget] + ("…" if len(s) > budget else "")
src, STEPS = sys.argv[1], int(sys.argv[2])
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; mx = -1; rows = []
for n in range(STEPS):
    a = stk[-1]; ch, _ = hc.spine(a)
    if len(ch) > mx:
        mx = len(ch); rows.append((n, mx, bshow(a, 70), hc.size(a)))
    stk.pop(); bb = stk.pop(); cc = stk.pop()
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
for r in rows[:14]: print(r)
d = [b[0] - a[0] for a, b in zip(rows, rows[1:])]
print("steps between new maxima:", d[:30])
print("second differences:", [b - a for a, b in zip(d, d[1:])][:30])
