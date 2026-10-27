"""Return stacks of the ternary counter's level calls L_m (main agent): generic run of [L_m, x, y, r1..r4]; print the
elements just below x·y at the moment it reaches the front (as terms in x, y)."""
import sys
sys.setrecursionlimit(100000)
from symb import parse
import hc
G = hc.from_tuple(parse("SSS(SS)")); L = [hc.from_tuple(parse("S(SS(S(SS)(SS(SS)(SS)))(S(S(SS)S)(SS(SSS(SS)))))"))]
for m in range(6): L.append(hc.app(0, hc.app(hc.app(hc.app(0, 0), G), L[-1])))
def nm(i):
    names = {-1: "x", -2: "y", -3: "r1", -4: "r2", -5: "r3", -6: "r4", hc.app(-1, -2): "Z"}
    if i in names: return names[i]
    if i == 0: return "S"
    l, r = hc.L[i], hc.R[i]
    return nm(l) + (("(" + nm(r) + ")") if (r > 0 and r not in names) or r == hc.app(-1, -2) and False else nm(r) if r <= 0 or r in names else "(" + nm(r) + ")")
for m, Lm in enumerate(L):
    stk = [-6, -5, -4, -3, -2, -1, Lm]; XY = hc.app(-1, -2)
    for t in range(10 ** 6):
        if stk[-1] == XY: break
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    below = [nm(e)[:60] for e in reversed(stk[-6:-1])]
    print(f"m={m} T={t}: below x·y: {below}")
