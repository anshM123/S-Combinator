"""Configurations of the flat binary counter K0 = S(SS)S(S(S(SSS)))S at its opcode-3 events (main agent): list length and
the distinct element shapes in the list (named by first appearance), to identify digit elements."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
def bshow(i, budget=40):
    out = []
    def go(i):
        if len(out) > budget: return
        if i == 0: out.append("S"); return
        go(hc.L[i]); r = hc.R[i]
        if r > 0: out.append("("); go(r); out.append(")")
        else: go(r)
    go(i); s = "".join(out); return s[:budget] + ("…" if len(s) > budget else "")
args, h = hc.spine(hc.from_tuple(parse("S(SS)S(S(S(SSS)))S"))); stk = args[::-1]
names = {}; events = 0
for n in range(70000):
    a = stk[-1]; ch, _ = hc.spine(a)
    if len(ch) == 3:
        events += 1
        lst = stk[::-1]
        word = []
        for e in lst:
            if e not in names: names[e] = chr(65 + len(names)) if len(names) < 26 else "?"
            word.append(names[e])
        if events <= 9:
            print(f"step {n}: list length {len(lst)}; word (front first): {''.join(word[:70])}{'…' if len(word) > 70 else ''}")
    stk.pop(); bb = stk.pop(); cc = stk.pop()
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
print("element names:", {v: bshow(k) for k, v in list(names.items())[:12]})
