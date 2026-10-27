"""Configurations of the ternary counter when a level call L_m is at the front (main agent)."""
import sys
sys.setrecursionlimit(100000)
from symb import parse
import hc
G = hc.from_tuple(parse("SSS(SS)")); L = [hc.from_tuple(parse("S(SS(S(SS)(SS(SS)(SS)))(S(S(SS)S)(SS(SSS(SS)))))"))]
for m in range(10): L.append(hc.app(0, hc.app(hc.app(hc.app(0, 0), G), L[-1])))
lev = {x: m for m, x in enumerate(L)}
def nm(i, k):
    """name relative to level k: L(d) for L_{k+d}"""
    if i in lev: return f"L{lev[i] - k:+d}" if lev[i] != k else "L"
    if i == 0: return "S"
    if i == G: return "G"
    l, r = hc.L[i], hc.R[i]
    return nm(l, k) + "(" + nm(r, k) + ")" if r > 0 else nm(l, k) + nm(r, k)
src = "S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS))))"
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
seen = {}
for n in range(200000):
    a = stk[-1]
    if a in lev and lev[a] >= 1:
        k = lev[a]
        top = tuple(stk[-1:-4:-1])
        key = tuple(nm(e, k) for e in top)
        seen.setdefault(key, []).append((n, k))
    stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
for key, occ in sorted(seen.items(), key=lambda kv: -len(kv[1]))[:12]:
    print(f"{len(occ):6d}x  levels {sorted(set(k for _, k in occ))[:8]}  first {occ[:3]}  top3 = {[s[:60] for s in key]}")
