"""K0's driver configuration (main agent): top three list elements at the opcode-3 event steps, written with level
tokens L_k (L_{k+1} = S((S L_k)(L_k (S L_k))), L_0 = S(S(S(S(SSS)))S)) relative to the level k of the front."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
L = [hc.from_tuple(parse("S(S(S(S(SSS)))S)"))]
for k in range(14): Lk = L[-1]; L.append(hc.app(0, hc.app(hc.app(0, Lk), hc.app(Lk, hc.app(0, Lk)))))
lev = {x: k for k, x in enumerate(L)}
def nm(i, k, depth=0):
    if i in lev: d = lev[i] - k; return "L" if d == 0 else f"L{d:+d}"
    if i == 0: return "S"
    if depth > 12: return "…"
    l, r = hc.L[i], hc.R[i]
    sr = nm(r, k, depth + 1)
    return nm(l, k, depth + 1) + (("(" + sr + ")") if r > 0 and len(sr) > 1 else sr)
args, h = hc.spine(hc.from_tuple(parse("S(SS)S(S(S(SSS)))S"))); stk = args[::-1]; ev = 0
for n in range(20000):
    a = stk[-1]; ch, _ = hc.spine(a)
    if len(ch) == 3:
        ev += 1
        # find the largest level occurring among the top three as a subterm: use the front's level if it is a level
        top = [stk[-1], stk[-2], stk[-3]]
        kk = max((lev[x] for x in L if any(x == e for e in top)), default=None)
        if kk is None:
            # search inside: level of the largest L_k contained in the front
            def maxlev(i, memo={}):
                if i in lev: return lev[i]
                if i <= 0: return -1
                if i in memo: return memo[i]
                r = max(maxlev(hc.L[i]), maxlev(hc.R[i])); memo[i] = r; return r
            kk = maxlev(top[0])
        print(f"event {ev} at step {n}: level {kk}: " + " | ".join(nm(e, kk)[:60] for e in top))
        if ev >= 8: break
    stk.pop(); bb = stk.pop(); cc = stk.pop()
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
