"""Profile runs with no level family (main agent): list length growth, max spine length growth, and the front elements
at new-maximum spine events, to see what grows."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
def bshow(i, budget=60):
    out = []
    def go(i):
        if len(out) > budget: return
        if i == 0: out.append("S"); return
        go(hc.L[i]); r = hc.R[i]
        if r > 0: out.append("("); go(r); out.append(")")
        else: go(r)
    go(i); s = "".join(out); return s[:budget] + ("…" if len(s) > budget else "")
for src in sys.argv[1:]:
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; mx = 0; rec = []; lens = []
    for n in range(20000):
        if len(stk) < 3: print(src, "hnf at", n); break
        a = stk[-1]; ch, _ = hc.spine(a)
        if len(ch) > mx: mx = len(ch); rec.append((n, mx, bshow(a, 50)))
        if n % 4000 == 0: lens.append(len(stk))
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    print(f"{src}: list length every 4000 steps {lens}; max spine records {[(n, m) for n, m, _ in rec][:12]}")
    print(f"   front at last record: {rec[-1][2] if rec else None}")
