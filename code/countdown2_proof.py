"""Exact structure of the growing-opcode countdown S(SS)S(S(S(SS(SS))S))S (main agent, 2026-10-26) — Theorem CD2.
Notation as in countdown2_call.py: levels a_0 (concrete), a_{k+1} = F(a_k) = S S (S a_k)(S (S a_k)), c_k = S a_k,
b_k = S c_k, R(Z) = [Z, S (S Z), S S (S Z)(S (S Z))]; frame lists Y ⟨k⟩ := Y f_{k−1} ⋯ f_0 with f_j = S a_j b_j (Y f_{k−1} ⋯ f_{j+1});
E(i, m) := (S a_i b_i a_{m+1}) ⟨m+1⟩ (so E_m := E(m−1, m) is the widest element of epoch m).
Lemmas (symbolic: generic parts opaque, junk below):
  CALL [a_k, X, Y] ++ r →^(4k+20) R(Y⟨k⟩) ++ … ++ r                         (countdown2_call.py: DL + BASE, induction)
  TA   R(Z) with Z = S P Q W_1 ⋯ W_p: one step gives [P, Q, W_1, …, W_p, u_2, u_3] ++ r     (a head step)
  TB   R(a_{k+1} W_1 ⋯ W_p), p ≥ 1 →^4 [a_k, X, W_1 X, W_2, …, W_p, u_2, u_3] ++ r with X = S a_k b_k W_1   (opcodes (3+p)011)
  TB0  R(a_{k+1}) →^4 [a_k, X, a_{k+2} X, …] ++ r with X = S a_k b_k a_{k+2}                     (opcodes 3011)
Composition (PROOF.md): R(E(i, m)) →TA→ call a_i (X = b_i, Y = a_{m+1}) →CALL→ R(a_{m+1}⟨i⟩) →TB→ call a_m with
X = S a_m b_m g, Y = g X (g = S a_{i−1} b_{i−1} a_{m+1}, the first frame) →CALL→ R((S a_{i−1} b_{i−1} a_{m+1})⟨m+1⟩) = R(E(i−1, m)),
in 4i + 4m + 45 steps (1 ≤ i ≤ m−1); and R(E(0, m)) →TA, CALL(a_0)→ R(a_{m+1}) →TB0, CALL(a_m)→ R(a_{m+2}⟨m+1⟩) →TB, CALL(a_{m+1})→
R(E(m, m+1)) = R(E_{m+1}) in 8m + 73 steps. Epoch m: 6m² + 47m + 28 steps (B = 20; in general 6m² + (2B + 7)m + B + 8 for a base of B steps).
Checks here: TB, TB0 symbolically; the concrete run reaches R(E_3); predicted opcode word = concrete run over many epochs;
whole list (30 entries) at every epoch start.
Usage: python countdown2_proof.py [EPOCHS] [TERM]   (TERM defaults to S(SS)S(S(S(SS(SS))S))S; for another term of the same
kind a_0 is read off the run (first component of the last frame of a widest element) and BASE is recomputed)"""
import sys
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from countdown_proof import run_steps, run_until, JUNK, ap, S, Stuck
from countdown2_call import F, b, R

def c(x): return ap(S, x)
def framed(Y, A, k):
    cur = Y
    for j in range(k - 1, -1, -1): cur = hc.app(cur, ap(S, A[j], b(A[j]), cur))
    return cur

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    src = sys.argv[2] if len(sys.argv) > 2 else "S(SS)S(S(S(SS(SS))S))S"
    ok = True
    from countdown_proof import step
    # a_0 from the run (widest element's last frame) and the BASE word: [a_0, X, Y] ++ r until Y is at the front
    t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]; mx = 3; Ew = None
    for n in range(3000):
        aa = stk[-1]; chh, _ = hc.spine(aa)
        if len(chh) > mx: mx = len(chh); Ew = aa
        aa = stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(chh))
    a0 = hc.spine(hc.spine(Ew)[0][-1])[0][0]
    Lb = [a0, -1, -2] + JUNK; bops = []
    while Lb[0] != -2:
        Lb, op = step(Lb); bops.append(op)
    base_ok = Lb[:3] == R(-2) and Lb[-len(JUNK):] == JUNK
    BASE_OPS = "".join(map(str, bops))
    print(f"term {src}: a_0 = {hc.show(a0)}; BASE [a_0, X, Y] →^{len(bops)} R(Y), rest untouched: {base_ok} (opcodes {BASE_OPS})")
    ok &= base_ok
    # TB (p = 2) and TB0, with a_k = A opaque (so a_{k+1} = F(A), a_{k+2} = F(F(A)))
    A_, W1, W2 = -11, -21, -22
    Z = ap(F(A_), W1, W2)
    L, ops = run_steps(R(Z) + JUNK, 4)
    X = ap(S, A_, b(A_), W1)
    u2 = R(Z)[2]; u3 = hc.app(R(Z)[1], R(Z)[2])
    tb = L[:6] == [A_, X, hc.app(W1, X), W2, u2, u3] and L[6:] == JUNK
    print(f"TB (p = 2): {tb} (opcodes after the open: {''.join(map(str, ops[1:]))}, open = {ops[0]})"); ok &= tb
    Z0 = F(A_)
    L, ops = run_steps(R(Z0) + JUNK, 4)
    X0 = ap(S, A_, b(A_), F(F(A_)))
    tb0 = L[:3] == [A_, X0, hc.app(F(F(A_)), X0)] and L[-len(JUNK):] == JUNK
    print(f"TB0: {tb0} (opcodes {''.join(map(str, ops))})"); ok &= tb0
    # levels
    A = [a0]
    for k in range(M + 6): A.append(F(A[-1]))
    def E(i, m): return framed(ap(S, A[i], b(A[i]), A[m + 1]), A, m + 1)
    # predicted opcode word of epoch m (from R(E_m) to R(E_{m+1}))
    def ch(x): return chr(48 + x)
    def call(k): return "3011" * k + BASE_OPS
    def epoch(m):
        w = ""
        for i in range(m - 1, 0, -1):
            w += ch(m + 4) + call(i) + ch(3 + i) + "011" + call(m)
        w += ch(m + 4) + call(0) + "3011" + call(m) + ch(3 + m + 1) + "011" + call(m + 1)
        return w
    B = len(BASE_OPS)
    lens_ok = all(len(epoch(m)) == 6 * m * m + (2 * B + 7) * m + B + 8 for m in range(3, M))
    print(f"epoch lengths 6m² + (2B + 7)m + B + 8 (B = {B}) match the composed word: {lens_ok}"); ok &= lens_ok
    # concrete run
    t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]
    starts = {}; ops = []; snaps = {}
    total = 0; m3 = None
    need = sum(len(epoch(m)) for m in range(3, M)) + 4000
    for n in range(need):
        top = stk[::-1][:3]
        for m in range(3, M + 1):
            if m not in starts and top == R(E(m - 1, m)):
                starts[m] = n; snaps[m] = stk[::-1][:40]
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); chh, _ = hc.spine(a); ops.append(chh.__len__())
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(chh))
    reached = sorted(starts)
    print(f"the concrete run reaches R(E_m) for m = {reached[0]}..{reached[-1]} (first at step {starts[reached[0]]})")
    word = "".join(chr(48 + o) for o in ops)
    pred = "".join(epoch(m) for m in range(3, M))
    real = word[starts[3]:starts[M]]
    wok = pred == real and all(starts[m + 1] - starts[m] == len(epoch(m)) for m in range(3, M))
    print(f"predicted opcode word from R(E_3) to R(E_{M}) ({len(real)} steps) equals the concrete run: {wok}"); ok &= wok
    # whole list: epoch m from R(E_m) with junk below never reads the junk; its pushes are explicit
    below = snaps[3][3:]; passed = tot = 0
    for m in range(3, M):
        L, _ = run_until(R(E(m - 1, m)) + JUNK, R(E(m, m + 1)), cap=10 ** 6)
        pushes = L[3:L.index(JUNK[0])]
        below = pushes + below
        pred_list = R(E(m, m + 1)) + below
        k = min(30, len(snaps[m + 1]))
        tot += 1; passed += pred_list[:k] == snaps[m + 1][:k]
    print(f"whole list: first 30 entries predicted at {passed}/{tot} epoch starts"); ok &= passed == tot and tot > 0
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILS")
