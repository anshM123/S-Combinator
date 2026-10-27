"""Check of the hand proof of Theorem UR for t0 = S(SSS)S(S(SSS)S) (main agent, 2026-10-26).
A = SSS, B = S A S; family C: SB in C, and S p (S q) in C for p, q in C. Claims of the proof, tested on the run:
(1) every step's second list element is S or S·z (so every created element b·c is a normal form);
(2) the states of the form Phi(c) = [c, Sc, Sc] ++ R occur with c = B first and then c in C, in an endless sequence;
(3) every list element is a normal form (redex-free) at the checked states.
Usage: python unique_redex_t0.py STEPS"""
import sys
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from li_explore import has_redex
A = hc.from_tuple(parse("SSS")); B = hc.from_tuple(parse("S(SSS)S")); SB = hc.app(0, B)
_C = {}
def in_C(t):
    if t == SB: return True
    if t in _C: return _C[t]
    a, h = hc.spine(t)
    r = h == 0 and len(a) == 2 and in_C(a[0]) and hc.spine(a[1])[1] == 0 and len(hc.spine(a[1])[0]) == 1 and in_C(hc.spine(a[1])[0][0])
    _C[t] = r; return r
if __name__ == "__main__":
    N = int(sys.argv[1])
    t = hc.from_tuple(parse("S(SSS)S(S(SSS)S)")); args, h = hc.spine(t); stk = args[::-1]
    phis = []; ok1 = True; ok3 = True
    for n in range(N):
        L3 = stk[-3:]
        if len(stk) >= 3 and stk[-2] == hc.app(0, stk[-1]) and stk[-3] == stk[-2]:
            c = stk[-1]; phis.append(c)
            if len(phis) % 50 == 1: ok3 &= not any(has_redex(e) for e in stk)
        if len(hc.spine(stk[-2])[0]) > 1: ok1 = False; break
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    print(f"(1) second element S or S·z at all {N} steps: {ok1}")
    print(f"(2) Phi states: {len(phis)}; first is c = B: {phis[0] == B}; all later c in C: {all(in_C(c) for c in phis[1:])}")
    print(f"(3) all list elements redex-free at every 50th Phi state: {ok3}")
