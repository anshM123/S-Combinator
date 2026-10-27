"""Trace steps 16..20 of SSS(SS)S(SS(SS)) under LO and the parallel head machine (main agent)."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
from waiting_nf import is_nf
def bshow(i, budget=22):
    out = []
    def go(i):
        if len(out) > budget: return
        if i == 0: out.append("S"); return
        go(hc.L[i]); r = hc.R[i]
        if r > 0: out.append("("); go(r); out.append(")")
        else: go(r)
    go(i); s = "".join(out); return s[:budget] + ("…" if len(s) > budget else "")
P = step_fn()
args, h = hc.spine(hc.from_tuple(parse("SSS(SS)S(SS(SS))"))); lo = list(args); par = list(args)
for n in range(21):
    if n >= 16:
        print(f"step {n}: LO  {[bshow(e, 22) for e in lo[:6]]}")
        print(f"         PAR {[bshow(e, 22) for e in par[:6]]}   equal positions: {[i for i, (u, v) in enumerate(zip(lo, par)) if u == v][:8]}")
        print(f"         LO positions>=3 non-NF: {[i for i, e in enumerate(lo) if i >= 3 and not is_nf(e)][:8]}")
    a, b, c = lo[0], lo[1], lo[2]; ch, _ = hc.spine(a); lo = ch + [c, hc.app(b, c)] + lo[3:]
    a, b, c = par[0], par[1], par[2]; ch2, _ = hc.spine(a); par = ch2 + [c, hc.app(b, c)] + [P(e) for e in par[3:]]
