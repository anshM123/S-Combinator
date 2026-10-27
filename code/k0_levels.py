"""Configuration-level structure of K0 (main agent): front element (and the next two) at the start of the first b_k block
of W_k, for k = 0..6; sizes and whether L_{k+1} contains L_k."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
def bshow(i, budget=90):
    out = []
    def go(i):
        if len(out) > budget: return
        if i == 0: out.append("S"); return
        go(hc.L[i]); r = hc.R[i]
        if r > 0: out.append("("); go(r); out.append(")")
        else: go(r)
    go(i); s = "".join(out); return s[:budget] + ("…" if len(s) > budget else "")
def contains(big, small, memo=None):
    if memo is None: memo = {}
    if big == small: return True
    if big <= 0: return False
    if big in memo: return memo[big]
    r = contains(hc.L[big], small, memo) or contains(hc.R[big], small, memo); memo[big] = r; return r
args, h = hc.spine(hc.from_tuple(parse("S(SS)S(S(S(SSS)))S"))); stk = args[::-1]
starts = {}; t = 23; blen = 12
for k in range(7):
    starts[t] = k; t += 2 * blen + 2 + 1; blen = 2 * blen + 4
fronts = {}
for n in range(max(starts) + 1):
    if n in starts: fronts[starts[n]] = (stk[-1], stk[-2], stk[-3])
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
for k in range(7):
    L, x, y = fronts[k]
    print(f"k={k}: front size {hc.size(L)}, spine {len(hc.spine(L)[0])}: {bshow(L, 70)}")
    print(f"       x: {bshow(x, 50)} | y: {bshow(y, 50)}")
    if k: print(f"       contains previous level front: {contains(L, fronts[k - 1][0])}")
