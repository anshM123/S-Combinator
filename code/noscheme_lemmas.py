"""Call lemma for the 'no scheme' counter SSS(S(S(SS)(SS)(SS)))S (main agent, 2026-10-26) — Lemma NS (partial result).
Tops T_g (T_0 = Q_1), layers [Y|C] = S S (S Y) C, D = SS, base members B_g = S S (S S D)(S T_{g−1}), family return forms
R_g(Y) = [Y, S T_{g−1} Y, U(Ch_g(Y))] with U(C) = S S (S C)(S S (S S D)(S C)) and Ch_g(Y) = [Q_2|[Q_1|[T_1|⋯[T_{g−1}|Y]⋯]]].
Checked here symbolically (opaque atoms, junk below): C1 [S S D (S T) Q, b, c] →³ [T, Q, [T|Q], …]; C2 [[T|Q], b, c] →²
[Q, S T Q, c, …]; TC (tail call) [[Y_j|L], X, Y] →² [L, S Y_j L, Y, X Y]; BASE0 [Q_1, P, Q] →^30 [Q, *, U([Q_2|Q])]. With W and Wb
(checked in the session: one chain layer in 2 steps; a base member B in 4 steps to [T, P, S S D (S T) P, …]) they give,
by induction on k, Enter(k, P, Q) := [T_k, P, Q] →* R_k(Q), and every family call [L, X, Y] →* R_g(Y). The driver (how the
run moves from top T_g to T_{g+1}) is not proved yet.
"""
import sys
sys.setrecursionlimit(1000000)
sys.argv = ["x"]
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
import auto_prover as apv, hc
from countdown_proof import step, run_steps, run_until, JUNK, ap, S, Stuck
src = "SSS(S(S(SS)(SS)(SS)))S"
fams = apv.find_family(src)
chains = sorted([c for k, c in fams], key=lambda c: hc.size(c[0][2]))
tops = [c[-1][2] for c in chains]
def lay(t):
    a, h = hc.spine(t)
    if len(a) == 3 and a[0] == 0:
        b, hb = hc.spine(a[1])
        if len(b) == 1: return b[0], a[2]
    return None
q2, _ = lay(tops[1]); q1, _ = lay(lay(tops[1])[1])
D = hc.app(0, 0)
def layer(y, c): return ap(S, S, ap(S, y), c)
def U(C): return ap(S, S, ap(S, C), ap(S, S, ap(S, S, D), ap(S, C)))
T_, P, Q, B1, B2, Yj, Lm, X = -11, -12, -13, -14, -15, -16, -17, -18
# C1: [S S D (S T) Q, b, c] ->3 [T, Q, [T|Q], ...]
L, ops = run_steps([ap(S, S, D, ap(S, T_), Q), B1, B2] + JUNK, 3)
print("C1:", L[:3] == [T_, Q, layer(T_, Q)], "opcodes", "".join(map(str, ops)))
# C2: [[T|Q], b, c] ->2 [Q, S T Q, c, ...]
L, ops = run_steps([layer(T_, Q), B1, B2] + JUNK, 2)
print("C2:", L[:3] == [Q, ap(S, T_, Q), B2], "opcodes", "".join(map(str, ops)))
# TC (tail call of a family member): [[Yj|Lm], X, Y] ->2 [Lm, S Yj Lm, Y, X Y]
L, ops = run_steps([layer(Yj, Lm), X, -19] + JUNK, 2)
print("TC:", L[:4] == [Lm, ap(S, Yj, Lm), -19, hc.app(X, -19)], "opcodes", "".join(map(str, ops)))
# base: Enter(0, P, Q) = [Q1, P, Q] ->* [Q, *, U([Q2|Q])]
L = [q1, P, Q] + JUNK; ops = []
while L[0] != Q:
    L, op = step(L); ops.append(op)
target = U(layer(q2, Q))
print("BASE0: [Q1, P, Q] ->", len(ops), "steps; front Q; third element = U([Q2|Q]):", L[2] == target, "| rest untouched:", L[-len(JUNK):] == JUNK, "| opcodes", "".join(map(str, ops)))
print("Q1 =", hc.show(q1)); print("Q2 =", hc.show(q2))
