"""Time-to-data channel (main agent): put a clock element W just below the arguments of a call P_m (k-ary scheme, atomic
x, y) and run until x·y reaches the front, (a) with the leftmost-outermost head machine, (b) with the parallel head
machine of Lemma PH. Report W's state (spine length and size) at that moment for m = 0..5."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn, size
P = step_fn()
def level(k, m):
    L = hc.app(0, 0)
    for _ in range(m):
        t = hc.app(L, 0)
        for _ in range(k - 1): t = hc.app(hc.app(0, L), t)
        L = hc.app(0, t)
    return L
for wsrc in ("SSS(SS)S(SS(SS))", "S(SS)SSSS"):
    W = hc.from_tuple(parse(wsrc))
    print(f"clock W = {wsrc}")
    for m in range(6):
        C = level(2, m); X, Y = -1, -2; XY = hc.app(X, Y)
        res = {}
        for mode in ("LO", "parallel"):
            lst = [C, X, Y, W, -5, -6]
            for n in range(10 ** 5):
                if lst[0] == XY: break
                a, b, c, rest = lst[0], lst[1], lst[2], lst[3:]
                args, h = hc.spine(a)
                if h != 0: break
                lst = args + [c, hc.app(b, c)] + ([P(e) for e in rest] if mode == "parallel" else rest)
            w = next(e for e in lst if e == W or (e > 0 and mode == "parallel" and e not in (XY,)) and False) if False else None
            # the clock is the element that started as W: in LO it is W itself; in parallel it is P^n(W)
            Wn = W
            if mode == "parallel":
                for _ in range(n): Wn = P(Wn)
            present = Wn in lst
            res[mode] = (n, len(hc.spine(Wn)[0]), size(Wn), present)
        print(f"  m={m}: LO: x·y after {res['LO'][0]} steps, clock spine {res['LO'][1]}, size {res['LO'][2]} | "
              f"parallel: after {res['parallel'][0]} passes, clock spine {res['parallel'][1]}, size {res['parallel'][2]}, "
              f"clock in list: {res['parallel'][3]}")
