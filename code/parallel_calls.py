"""Do tree calls stay calls under parallel evaluation? (main agent) Parallel head machine (Lemma PH): pop a, b, c;
list := spine(a) ++ [c, b·c] ++ [P(e) for the rest], P = one ReplaceAll pass (atoms are inert). Report the pass at which
x·y is at the front, versus the head-machine time T."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
from kary_check import N as Nk
def to_hc(t):
    if t == "S": return 0
    return hc.app(to_hc(t[0]), to_hc(t[1]))
def par_call(C, cap=200000):
    X, Y = -1, -2; XY = hc.app(X, Y)
    lst = [C, X, Y, -3, -4, -5, -6]
    for n in range(cap):
        if lst[0] == XY: return n, True
        a, b, c, rest = lst[0], lst[1], lst[2], lst[3:]
        args, h = hc.spine(a)
        if h != 0: return n, False
        P = step_fn()
        lst = args + [c, hc.app(b, c)] + [P(e) for e in rest]
    return None, False
def head_call(C, cap=10 ** 6):
    T = hc.call_time(C, cap); return T
for k in (2, 3):
    Pm = hc.app(0, 0)
    for m in range(5):
        T = head_call(Pm); n, ok = par_call(Pm)
        print(f"k={k} level {m}: head-machine T = {T}; parallel: x·y at front after {n} passes ({'clean' if ok else 'stuck/other'})")
        Pm = to_hc(("S", Nk(k, "PLACE")) ) if False else hc.app(0, (lambda P: (lambda t: t)(P))(0)) if False else Pm
        # build next level seq(Pm,...,Pm)
        t = hc.app(Pm, 0)
        for _ in range(k - 1): t = hc.app(hc.app(0, Pm), t)
        Pm = hc.app(0, t)
