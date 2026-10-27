"""Exact structure of the countdown S(SS)S(S(S(S(SSS))S))S (main agent, 2026-10-26) — Theorem CD3.
Same architecture as Theorem CD2 (countdown2_proof.py) with another level context and return form:
  levels L_0 = n20 (read off the run), L_{k+1} = G(L_k) = S (S (S L_k)) (S L_k (S (S L_k))), d_k = S (S L_k);
  return form R′(Z) = [Z, G(Z), S Z (S (S Z)) G(Z)]; frame lists Y⟨k⟩ = Y f_{k−1} ⋯ f_0, f_j = S L_j d_j (Y f_{k−1} ⋯ f_{j+1});
  E(i, m) = (S L_i d_i L_{m+1})⟨m+1⟩, E_m = E(m−1, m).
Lemmas (symbolic, generic parts opaque, junk below):
  DL′  [L_k, X, Y] →^3 [L_{k−1}, X′, Y X′, …] with X′ = S L_{k−1} d_{k−1} Y (opcodes 211)   → CALL [L_k, X, Y] →^{3k+B} R′(Y⟨k⟩)
  BASE [L_0, X, Y] →^B R′(Y) (B = 17)
  TB′  R′(L_{k+1} W_1 ⋯ W_p), p ≥ 1 →^3 [L_k, X, W_1 X, W_2, …] with X = S L_k d_k W_1 (opcodes (2+p)11)
  TB0′ R′(L_{k+1}) →^3 [L_k, X, W X, …] with W = S L_{k+1} d_{k+1} L_{k+2}, X = S L_k d_k W (opcodes 211)
Composition: phases i = m−1..1 as in CD2: R′(E(i, m)) → R′(E(i−1, m)) in 3i + 3m + 2B + 4 steps; final phase
R′(E(0, m)) →TA, CALL(L_0)→ R′(L_{m+1}) →TB0′, CALL(L_m)→ R′(W⟨m+1⟩) →TA, CALL(L_{m+1})→ R′(L_{m+2}⟨m+1⟩) →TB′, CALL(L_{m+1})→
R′(E(m, m+1)) = R′(E_{m+1}). Epoch m: 4.5m² + 42.5m + 44 steps (B = 17).
Usage: python countdown3_proof.py [EPOCHS]"""
import sys
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from countdown_proof import step, run_steps, run_until, JUNK, ap, S, Stuck

def G(y):
    d = ap(S, ap(S, y)); return ap(S, d, ap(S, y, d))
def dd(y): return ap(S, ap(S, y))
def Rp(Z): return [Z, G(Z), ap(S, Z, dd(Z), G(Z))]
def framed(Y, Ls, k):
    cur = Y
    for j in range(k - 1, -1, -1): cur = hc.app(cur, ap(S, Ls[j], dd(Ls[j]), cur))
    return cur

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    src = "S(SS)S(S(S(S(SSS))S))S"
    ok = True
    A, X, Y, W1, W2 = -11, -1, -2, -21, -22
    L, ops = run_steps([G(A), X, Y] + JUNK, 3)
    Xp = ap(S, A, dd(A), Y)
    dl = L[:4] == [A, Xp, hc.app(Y, Xp), hc.app(X, Y)] and L[4:] == JUNK
    print(f"DL′: {dl} (opcodes {''.join(map(str, ops))})"); ok &= dl
    L, ops = run_steps(Rp(ap(G(A), W1, W2)) + JUNK, 3)
    Xb = ap(S, A, dd(A), W1)
    tb = L[:4] == [A, Xb, hc.app(W1, Xb), W2] and L[-len(JUNK):] == JUNK
    print(f"TB′ (p = 2): {tb} (opcodes {''.join(map(str, ops))})"); ok &= tb
    L, ops = run_steps(Rp(G(A)) + JUNK, 3)
    Wt = ap(S, G(A), dd(G(A)), G(G(A))); X0 = ap(S, A, dd(A), Wt)
    tb0 = L[:3] == [A, X0, hc.app(Wt, X0)] and L[-len(JUNK):] == JUNK
    print(f"TB0′: {tb0} (opcodes {''.join(map(str, ops))})"); ok &= tb0
    # L_0 from the run: the first argument of the second widest element; BASE
    t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]; mx = 3; Ews = []
    for n in range(2000):
        aa = stk[-1]; chh, _ = hc.spine(aa)
        if len(chh) > mx: mx = len(chh); Ews.append(aa)
        aa = stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(chh))
    L0 = hc.spine(Ews[1])[0][0]
    Lb = [L0, X, Y] + JUNK; bops = []
    while Lb[0] != Y: Lb, op = step(Lb); bops.append(op)
    BASE = "".join(map(str, bops)); B = len(bops)
    bok = Lb[:3] == Rp(Y) and Lb[-len(JUNK):] == JUNK
    print(f"BASE [L_0, X, Y] →^{B} R′(Y), rest untouched: {bok} (L_0 = {hc.show(L0)}, opcodes {BASE})"); ok &= bok
    Ls = [L0]
    for k in range(M + 6): Ls.append(G(Ls[-1]))
    def E(i, m): return framed(ap(S, Ls[i], dd(Ls[i]), Ls[m + 1]), Ls, m + 1)
    def ch(x): return chr(48 + x)
    def call(k): return "211" * k + BASE
    def epoch(m):
        w = ""
        for i in range(m - 1, 0, -1):
            w += ch(m + 4) + call(i) + ch(2 + i) + "11" + call(m)
        w += ch(m + 4) + call(0) + "211" + call(m) + ch(m + 4) + call(m + 1) + ch(2 + m + 1) + "11" + call(m + 1)
        return w
    lens = all(len(epoch(m)) * 2 == 9 * m * m + 85 * m + 88 for m in range(3, M))
    print(f"epoch lengths 4.5m² + 42.5m + 44 match the composed word: {lens}"); ok &= lens
    t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]
    starts = {}; ops = []; snaps = {}
    need = sum(len(epoch(m)) for m in range(3, M)) + 4000
    for n in range(need):
        top = stk[::-1][:3]
        for m in range(3, M + 1):
            if m not in starts and top == Rp(E(m - 1, m)):
                starts[m] = n; snaps[m] = stk[::-1][:40]
        aa = stk.pop(); bb = stk.pop(); cc = stk.pop(); chh, _ = hc.spine(aa); ops.append(len(chh))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(chh))
    reached = sorted(starts)
    print(f"the concrete run reaches R′(E_m) for m = {reached[0]}..{reached[-1]} (first at step {starts[reached[0]]})")
    word = "".join(chr(48 + o) for o in ops)
    pred = "".join(epoch(m) for m in range(3, M)); real = word[starts[3]:starts[M]]
    wok = pred == real
    print(f"predicted opcode word from R′(E_3) to R′(E_{M}) ({len(real)} steps) equals the concrete run: {wok}"); ok &= wok
    below = snaps[3][3:]; passed = tot = 0
    for m in range(3, M):
        L, _ = run_until(Rp(E(m - 1, m)) + JUNK, Rp(E(m, m + 1)), cap=10 ** 6)
        below = L[3:L.index(JUNK[0])] + below
        pred_list = Rp(E(m, m + 1)) + below
        k = min(30, len(snaps[m + 1]))
        tot += 1; passed += pred_list[:k] == snaps[m + 1][:k]
    print(f"whole list: first 30 entries predicted at {passed}/{tot} epoch starts"); ok &= passed == tot and tot > 0
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILS")
