"""Probe a linear-scheme run (main agent): levels and return form from auto_prover, then the top three at the first time
each level appears at the front, written with level names."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
import auto_prover as AP
src = sys.argv[1]
fams = AP.find_family(src)
key, chain = fams[0]
levels = [m[2] for m in chain]; lev = {L: k for k, L in enumerate(levels)}
F, i0 = AP.infer_scheme(chain)
print("scheme F:", F, "| return form:", AP.return_form(key), "| T:", [m[1] for m in chain])
def nm(i, depth=0):
    if i in lev: return f"L{lev[i]}"
    if i == 0: return "S"
    if depth > 8: return "…"
    l, r = hc.L[i], hc.R[i]; sr = nm(r, depth + 1)
    return nm(l, depth + 1) + (("(" + sr + ")") if r > 0 and len(sr) > 1 else sr)
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; seen = set()
for n in range(20000):
    a = stk[-1]
    if a in lev and lev[a] not in seen:
        seen.add(lev[a]); print(f"step {n}: front L{lev[a]}; top three: {[nm(e)[:50] for e in stk[-1:-4:-1]]}")
    stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
