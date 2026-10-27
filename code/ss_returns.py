"""Return stacks of gadget levels over the base SS (main agent): L_0 = SS, L_{m+1} = S(S S X L_m); generic run of
[L_m, x, y, r1, r2, r3]; print the elements below x·y when it reaches the front (atoms x, y, r named)."""
import sys
sys.setrecursionlimit(100000)
from symb import parse
import hc
NAMES = {-1: "x", -2: "y", -3: "r1", -4: "r2", -5: "r3"}
def bshow(i, budget=70):
    out = []
    def go(i):
        if len(out) > budget: return
        if i in NAMES: out.append(NAMES[i]); return
        if i == 0: out.append("S"); return
        if i == hc.app(-1, -2): out.append("Z"); return
        go(hc.L[i]); r = hc.R[i]
        if r > 0 and r != hc.app(-1, -2): out.append("("); go(r); out.append(")")
        else: go(r)
    go(i); s = "".join(out); return s[:budget] + ("…" if len(s) > budget else "")
for gs in ("SSS(SS)", "SS(SSS(SS))"):
    X = hc.from_tuple(parse(gs)); L = hc.app(0, 0)
    print(f"gadget {gs}, base SS:")
    for m in range(4):
        stk = [-5, -4, -3, -2, -1, L]; XY = hc.app(-1, -2)
        for t in range(10 ** 6):
            if stk[-1] == XY: break
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
            if h != 0: print("  stuck on atom"); break
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
        print(f"  m={m} T={t}: below x·y: {[bshow(e) for e in reversed(stk[-5:-1])]}")
        L = hc.app(0, hc.app(hc.app(hc.app(0, 0), X), L))
