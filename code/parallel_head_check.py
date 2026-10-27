"""Check (main agent): for a term with head S and >= 3 head arguments, one ReplaceAll pass equals
spine(e1) ++ [e3, e2·e3, P(e4), P(e5), ...] with P = one pass on each deeper element (and no reduction inside e1, e2, e3).
Tested along the parallel evolution of several terms."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
def rebuild(head, args):
    t = head
    for a in args: t = hc.app(t, a)
    return t
ok = bad = 0
for src in ("SSS(SS)S(SS(SS))", "S(SS)SSSS", "S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS))))", "SSS(SSS)(S(SS))SS"):
    t = hc.from_tuple(parse(src))
    for n in range(40):
        args, h = hc.spine(t)
        if h != 0 or len(args) < 3: break
        step = step_fn()
        actual = step(t)
        e1, e2, e3, rest = args[0], args[1], args[2], args[3:]
        P = step_fn()
        predicted = rebuild(0, hc.spine(e1)[0] + [e3, hc.app(e2, e3)] + [P(e) for e in rest]) if hc.spine(e1)[1] == 0 else None
        if predicted == actual: ok += 1
        else: bad += 1
        t = actual
print(f"parallel pass = head step + one pass inside each deeper element: {ok} agree, {bad} differ")
