"""Generic behaviour of K0's levels L_{k+1} = S((S L_k)(L_k (S L_k))) (main agent): verify the scheme against the real
fronts, then run [L_k, x, y, r1..r4] with atoms until an atom-headed element is at the front; report the time and that
element (and the two below), as terms in x, y."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
NAMES = {-1: "x", -2: "y", -3: "r1", -4: "r2", -5: "r3", -6: "r4"}
def bshow(i, budget=70):
    out = []
    def go(i):
        if len(out) > budget: return
        if i in NAMES: out.append(NAMES[i]); return
        if i == 0: out.append("S"); return
        go(hc.L[i]); r = hc.R[i]
        if r > 0: out.append("("); go(r); out.append(")")
        else: go(r)
    go(i); s = "".join(out); return s[:budget] + ("…" if len(s) > budget else "")
L = [hc.from_tuple(parse("S(S(S(S(SSS)))S)"))]
for k in range(7): Lk = L[-1]; L.append(hc.app(0, hc.app(hc.app(0, Lk), hc.app(Lk, hc.app(0, Lk)))))
print("sizes:", [hc.size(l) for l in L])
for k in range(6):
    stk = [-6, -5, -4, -3, -2, -1, L[k]]; T = None
    for t in range(10 ** 6):
        a = stk[-1]; ch, h = hc.spine(a)
        if h != 0: T = t; break
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    print(f"L_{k}: after {T} steps front = {bshow(stk[-1])} ; below: {bshow(stk[-2], 40)} | {bshow(stk[-3], 40)}")
