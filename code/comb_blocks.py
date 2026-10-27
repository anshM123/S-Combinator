"""Configurations at the starts of consecutive B blocks of a comb run (main agent): top four elements (bounded print, with
repeated subterms named) at block starts inside one long cycle."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
src, B, N = sys.argv[1], sys.argv[2], int(sys.argv[3])
names = {}
def nm(i, budget=50):
    out = []
    def go(i, d):
        if len(out) > budget: return
        if i == 0: out.append("S"); return
        if i in names: out.append(names[i]); return
        go(hc.L[i], d + 1); r = hc.R[i]
        if r > 0: out.append("("); go(r, d + 1); out.append(")")
        else: go(r, d + 1)
    go(i, 0); s = "".join(out); return s[:budget] + ("…" if len(s) > budget else "")
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []; snaps = {}
for n in range(N):
    snaps[n] = (stk[-1], stk[-2], stk[-3], stk[-4], len(stk))
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(str(len(ch)))
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
w = "".join(ops)
# a long run of B near the end
i = w.rfind(B * 40)
starts = [i + k * len(B) for k in range(6)]
for s_ in starts:
    t = snaps[s_]
    for e in t[:4]:
        if hc.size(e) > 8 and e not in names: names[e] = f"E{len(names)}"
for s_ in starts:
    t = snaps[s_]
    print(f"step {s_}: len {t[4]}: " + " | ".join(nm(e, 40) for e in t[:4]))
print("named:", {v: nm(k, 80) for k, v in list(names.items())[:6]})
