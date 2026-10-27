"""Symbolic re-derivation of the call lemma's inductive step with the driver engine (main agent).
Start: [P_j, x, y | ?] with x, y opaque atoms and an unknown tail; the first step (opening the bare token P_j, which
the engine would otherwise treat as a call) is done by hand. Macros may only be used at levels j-1 and below
(induction hypothesis: call lemma and continuation lemma at level j-1). Goal: top three
[x·y, V·(x·y), ((x·y)(S(x·y)))(V(x·y))]. Prints the engine opcodes and macro sequence; levels symbolic, j >= JMIN.
"""
import sys
sys.setrecursionlimit(100000)
import driver_proof as D

for jmin in range(1, 5):
    D.JMIN = jmin
    D.MAXLEV = -1
    xy = ("x", "y")
    goal = [xy, (D.V, xy), ((xy, ("S", xy)), (D.V, xy))]
    K = [D.P(0), "x", "y", D.JUNK]
    first = D.open_front(K[0])          # P_j = S·U_{j-1}: opcode 1
    K = first + [K[2], D.mk(K[1], K[2])] + K[3:]
    try:
        n, calls = D.run(K, goal, verbose=False)
    except ValueError as e:
        print(f"j >= {jmin}: fails ({e})"); continue
    if n is None:
        print(f"j >= {jmin}: goal not reached"); continue
    items = [("eng", len(first))] + list(D.ITEMS)
    bad = [it for it in items if it[0] != "eng" and it[1] > -1]
    print(f"j >= {jmin}: goal reached; trace:",
          " ".join(str(v) if k == "eng" else f"[{k} {v:+d}]" for k, v in items),
          "| macros only below level j:", not bad)
    break

# base cases j = 0, 1 (concrete; x, y, r opaque atoms): after T_j steps the top three are the stated terms, no atom
# was opened, and (j = 1) the state after 6 steps is [P_0, W·P_0, (P_0·R_0)·(x·y), ...] (continuation form).
from symb import parse
b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))"); W = ("S", "S"); V = parse("SS(SS)")
L0 = ((("S", "S"), b), c)
P0 = ("S", L0); R0 = ("S", ((("S", "S"), W), P0)); U0 = ((("S", "S"), P0), R0); P1 = ("S", U0)
def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return a, t
xy = ("x", "y"); top = [xy, (V, xy), ((xy, ("S", xy)), (V, xy))]
for j, Pj in ((0, P0), (1, P1)):
    stk = ["r3", "r2", "r1", "y", "x", Pj]
    for t in range(2 ** (j + 4) - 8):
        if t == 6 and j == 1:
            print("  j=1 six-step state in continuation form:",
                  stk[-1:-4:-1] == [P0, (W, P0), ((P0, R0), xy)])
        a = stk.pop(); bb = stk.pop(); cc = stk.pop()
        args, h = spine(a)
        assert h == "S", f"atom {h} opened"
        stk.append((bb, cc)); stk.append(cc); stk.extend(reversed(args))
    print(f"  base j={j}: after T_{j} = {2 ** (j + 4) - 8} steps top three correct:", stk[-1:-4:-1] == top,
          "| no atom opened: True")
