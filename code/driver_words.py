"""The binary counter's opcode sequence, exactly (main agent).
1. Call words: w_m = opcode word of the call [P_m, x, y | r] (x, y, r atoms; T_m steps, no atom opened). Check
   w_m = A·u_m with A = w_m[:6] constant (m >= 1) and u_m = w_{m-1}·B·u_{m-1} with B constant (m >= 2).
2. Cycle template from driver_proof.ITEMS (engine opcodes, CALL m -> w_{k+m}, RESUME m -> u_{k+m}); predicted word =
   transient (first 376 opcodes) · D_2 · D_3 · ...; compared with the real opcode sequence of SSS(SS)S(SS(SS)).
"""
import sys
sys.setrecursionlimit(1000000)
import driver_proof as D
from symb import parse

def T(m): return 2 ** (m + 4) - 8
b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))"); W = ("S", "S")
L0 = ((("S", "S"), b), c)
MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
Pk = [("S", L0)]
for m in range(MMAX + 2):
    Rm = ("S", ((("S", "S"), W), Pk[m])); Um = ((("S", "S"), Pk[m]), Rm); Pk.append(("S", Um))

def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return a, t

def opword(stk, nsteps):
    ops = []
    for _ in range(nsteps):
        a = stk.pop(); bb = stk.pop(); cc = stk.pop()
        args, h = spine(a)
        if h != "S": raise ValueError(f"atom {h} opened")
        ops.append(len(args))
        stk.append((bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return ops

w = []
for m in range(MMAX + 1):
    w.append(opword(["r3", "r2", "r1", "y", "x", Pk[m]], T(m)))
A = w[1][:6]
ok_A = all(w[m][:6] == A for m in range(1, MMAX + 1))
u = [x[6:] for x in w]
B = w[2][6 + T(1): 6 + T(1) + 8]
ok_B = all(u[m] == w[m - 1] + B + u[m - 1] for m in range(2, MMAX + 1))
print("A =", A, " constant for m>=1:", ok_A, "| B =", B, " u_m = w_{m-1} B u_{m-1} for 2<=m<=%d:" % MMAX, ok_B)
print("w_0 =", w[0], "| u_1 =", u[1])

D.JMIN = 1
start = [D.P(0), D.Q(0), ((D.P(0), ("S", D.P(0))), D.Q(0)), D.JUNK]
goal = [D.P(1), D.Q(1), ((D.P(1), ("S", D.P(1))), D.Q(1))]
n, calls = D.run(start, goal, verbose=False)
items = list(D.ITEMS)
print("cycle template:", " ".join(f"{x[1]}" if x[0] == "eng" else f"[{x[0]} {x[1]:+d}]" for x in items))

def cycle(k):
    out = []
    for kind, v in items:
        if kind == "eng": out.append(v)
        elif kind == "call": out += w[k + v]
        else: out += u[k + v]
    return out

KMAX = MMAX - 1
t2 = 376
real_len = 144 * 2 ** (KMAX + 1) - 48 * (KMAX + 1) - 104
stk = list(reversed(spine(parse("SSS(SS)S(SS(SS))"))[0]))
real = opword(stk, real_len)
pred = real[:t2]
for k in range(2, KMAX + 1): pred += cycle(k)
print(f"predicted length {len(pred)} = t_{KMAX + 1} = {real_len}:", len(pred) == real_len)
first_bad = next((i for i, (p_, r_) in enumerate(zip(pred, real)) if p_ != r_), None)
print("predicted opcode word == real opcode word on the first", real_len, "steps:", first_bad is None,
      "" if first_bad is None else f"(first mismatch at {first_bad})")
