"""Exact structure of the 'no scheme' counter SSS(S(S(SS)(SS)(SS)))S (main agent, 2026-10-26) — Theorem NS.
D = SS, layers [Y|C] = S S (S Y) C, U(C) = S S (S C)(S S (S S D)(S C)); fixed terms Q_1, Q_2 (read off the run);
T_0 = Q_1, B_{g} = S S (S S D)(S T_{g−1}), T_g = Ch_g(B_g) with Ch_g(Z) = [Q_2|[Q_1|[T_1|⋯[T_{g−1}|Z]⋯]]];
return forms R_g(Y) = [Y, S T_{g−1} Y, U(Ch_g(Y))]; driver states Δ_g = R_g(B_g) = [B_g, S T_{g−1} B_g, [T_g|B_{g+1}]].
Local lemmas (symbolic, opaque atoms, junk below never read):
  E   [B, X, Y] →³ [T, Y, S S D (S T) Y, X Y]                    (B = S S (S S D)(S T); opcodes 301)
  W   [S, S Y, [Y′|C], P] →² [S, S Y′, C, P, (S Y [Y′|C]) P]        (opcodes 03)
  Wb  [S, S Y, B, P] →⁴ [T, P, S S D (S T) P, (S Y B) P]           (opcodes 0301)
  C1  [S S D (S T) Q, b, c] →³ [T, Q, [T|Q], …]                    (opcodes 401)
  C2  [[T|Q], b, c] →² [Q, S T Q, c, …]                            (opcodes 30)
  B0  [Q_1, P, Q] →^30 [Q, *, U([Q_2|Q])]
Composition (PROOF.md): Enter(k, P, Q) := [T_k, P, Q] →^{e_k} R_k(Q) by induction (open T_k, W k times, Wb, Enter(k−1), C1,
Enter(k−1), C2; e_0 = 30, e_k = 2e_{k−1} + 2k + 10 = 44·2^k − 2k − 14); a base call [B_g, X, Y] →^{2e_{g−1}+8} R_g(Y);
the driver Δ_g →^{d_g} Δ_{g+1} (base call with Y = [T_g|B_{g+1}], then C2), d_g = 44·2^g − 4g − 14.
Usage: python noscheme_proof.py [G]"""
import sys
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from countdown_proof import step, run_steps, run_until, JUNK, ap, S

D = hc.app(0, 0)
def layer(y, c): return ap(S, S, ap(S, y), c)
def U(C): return ap(S, S, ap(S, C), ap(S, S, ap(S, S, D), ap(S, C)))
def Bm(T): return ap(S, S, ap(S, S, D), ap(S, T))
SRC = "SSS(S(S(SS)(SS)(SS)))S"
Q2 = hc.from_tuple(parse("SS(SS(SS))(S(S(S(SS)(SS)(SS)))S)"))
Q1 = hc.from_tuple(parse("SS(S(SS(SS(SS))(S(S(S(SS)(SS)(SS)))S)))(SS(SS(SS))(S(SS(SS(SS))(S(S(S(SS)(SS)(SS)))S))))"))

if __name__ == "__main__":
    G = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    ok = True
    Tq, P, Q, X, Y, Y1, Y2, C, b1, b2 = -11, -12, -13, -14, -15, -16, -17, -18, -19, -20
    checks = []
    L, o = run_steps([Bm(Tq), X, Y] + JUNK, 3); checks.append(("E", L[:4] == [Tq, Y, ap(S, S, D, ap(S, Tq), Y), hc.app(X, Y)], o))
    L, o = run_steps([S, ap(S, Y1), layer(Y2, C), P] + JUNK, 2)
    checks.append(("W", L[:5] == [S, ap(S, Y2), C, P, ap(S, Y1, layer(Y2, C), P)] and L[5:] == JUNK, o))
    L, o = run_steps([S, ap(S, Y1), Bm(Tq), P] + JUNK, 4)
    checks.append(("Wb", L[:4] == [Tq, P, ap(S, S, D, ap(S, Tq), P), ap(S, Y1, Bm(Tq), P)] and L[4:] == JUNK, o))
    L, o = run_steps([ap(S, S, D, ap(S, Tq), Q), b1, b2] + JUNK, 3); checks.append(("C1", L[:3] == [Tq, Q, layer(Tq, Q)], o))
    L, o = run_steps([layer(Tq, Q), b1, b2] + JUNK, 2); checks.append(("C2", L[:3] == [Q, ap(S, Tq, Q), b2], o))
    L = [Q1, P, Q] + JUNK; o = []
    while L[0] != Q: L, op = step(L); o.append(op)
    checks.append(("B0", L[2] == U(layer(Q2, Q)) and L[-len(JUNK):] == JUNK and len(o) == 30, o))
    OPS = {}
    for name, good, o in checks:
        OPS[name] = "".join(map(str, o)); print(f"{name}: {good} (opcodes {OPS[name]})"); ok &= good
    # tops and driver states
    T = [Q1]
    def Ch(k, Z):
        cur = Z
        for y in reversed([Q2, Q1] + T[1:k]): cur = layer(y, cur)
        return cur
    for g in range(1, G + 3): T.append(Ch(g, Bm(T[g - 1])))
    def R(g, Yv): return [Yv, ap(S, T[g - 1], Yv), U(Ch(g, Yv))]
    def Delta(g): return R(g, Bm(T[g - 1]))
    ident = all(U(T[g]) == layer(T[g], Bm(T[g])) and Delta(g)[2] == layer(T[g], Bm(T[g])) for g in range(1, G + 1))
    print(f"identity U(T_g) = [T_g|B_(g+1)] and Δ_g = [B_g, S T_(g−1) B_g, [T_g|B_(g+1)]] for g = 1..{G}: {ident}"); ok &= ident
    # composed opcode words
    def enter(k):
        if k == 0: return OPS["B0"]
        return "3" + OPS["W"] * k + OPS["Wb"] + enter(k - 1) + OPS["C1"] + enter(k - 1) + OPS["C2"]
    def driver(g): return OPS["E"] + enter(g - 1) + OPS["C1"] + enter(g - 1) + OPS["C2"] + OPS["C2"]
    lens = all(len(driver(g)) == 44 * 2 ** g - 4 * g - 14 for g in range(1, G))
    print(f"driver lengths 44·2^g − 4g − 14 match the composed words: {lens}"); ok &= lens
    # concrete run
    t = hc.from_tuple(parse(SRC)); args, h = hc.spine(t); stk = args[::-1]; ops = []; at = {}; snaps = {}
    need = 60 + sum(len(driver(g)) for g in range(1, G)) + 100
    for n in range(need):
        top = stk[::-1][:3]
        for g in range(1, G + 1):
            if g not in at and top == Delta(g): at[g] = n; snaps[g] = stk[::-1][:40]
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); chh, _ = hc.spine(a); ops.append(len(chh))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(chh))
    reached = sorted(at)
    print(f"the concrete run reaches Δ_g for g = {reached[0]}..{reached[-1]} (Δ_1 at step {at.get(1)})")
    word = "".join(chr(48 + x) for x in ops)
    pred = "".join(driver(g) for g in range(1, G)); real = word[at[1]:at[G]]
    wok = pred == real and all(at[g + 1] - at[g] == 44 * 2 ** g - 4 * g - 14 for g in range(1, G))
    print(f"composed opcode word from Δ_1 to Δ_{G} ({len(real)} steps) equals the concrete run: {wok}"); ok &= wok
    below = snaps[1][3:]; passed = tot = 0
    for g in range(1, G):
        L, _ = run_until(Delta(g) + JUNK, Delta(g + 1), cap=10 ** 7)
        below = L[3:L.index(JUNK[0])] + below
        pl = Delta(g + 1) + below; k = min(30, len(snaps[g + 1]))
        tot += 1; passed += pl[:k] == snaps[g + 1][:k]
    print(f"whole list: first 30 entries predicted at {passed}/{tot} driver states"); ok &= passed == tot and tot > 0
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILS")
