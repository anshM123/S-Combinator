"""Level-call lemma for the growing-opcode countdown S(SS)S(S(S(SS(SS))S))S (main agent, 2026-10-26).
Levels: a_0 = S(S(SS(SS))S)(S(S(S(SS(SS))S)))S, a_{k+1} = S S (S a_k) (S (S a_k)), b_k = S (S a_k); R(Z) := [Z, S (S Z), S S (S Z) (S (S Z))].
  DL   [a_k, X, Y] ++ r →^4 [a_{k−1}, X′, Y X′, X Y] ++ r with X′ = S a_{k−1} b_{k−1} Y            (k ≥ 1; opcodes 3011)
  BASE [a_0, X, Y] ++ r →^20 R(Y) ++ Q_0(X, Y) ++ r                                               (opcodes 32200104010210312201)
  CALL [a_k, X, Y] ++ r →^(4k+20) R(Y f_{k−1} ⋯ f_0) ++ … ++ r,  f_j = S a_j b_j (Y f_{k−1} ⋯ f_{j+1})   (induction on k)
DL and BASE are checked symbolically (X, Y, a_{k−1} opaque, junk below). CALL is then tested on the concrete run: at every
epoch, after the widest element E_m = S a_{m−1} b_{m−1} a_{m+1} f_m ⋯ f_0 is opened, the front is a_{m−1} with X = b_{m−1},
Y = a_{m+1}, and 4(m−1) + 20 steps later the state must be R(a_{m+1} g_{m−2} ⋯ g_0) with the predicted frames g_j and the
predicted opcodes (3011)^(m−1) 32200104010210312201.
Usage: python countdown2_call.py STEPS"""
import sys
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from countdown_proof import step, run_steps, JUNK, ap, S, Stuck

a0 = hc.from_tuple(parse("S(S(SS(SS))S)(S(S(S(SS(SS))S)))S"))
def F(x): return ap(S, S, ap(S, x), ap(S, ap(S, x)))
def b(x): return ap(S, ap(S, x))
def R(Z): return [Z, ap(S, ap(S, Z)), ap(S, S, ap(S, Z), ap(S, ap(S, Z)))]
BASE_OPS = "32200104010210312201"

def frames_on(Y, A, k):
    """Y f_{k−1} ⋯ f_0 with f_j = S a_j b_j (prefix)"""
    cur = Y
    for j in range(k - 1, -1, -1): cur = hc.app(cur, ap(S, A[j], b(A[j]), cur))
    return cur

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
    ok = True
    A1, X, Y = -11, -1, -2
    L, ops = run_steps([F(A1), X, Y] + JUNK, 4)
    Xp = ap(S, A1, b(A1), Y)
    dl = L[:4] == [A1, Xp, hc.app(Y, Xp), hc.app(X, Y)] and L[4:] == JUNK
    print(f"DL: {dl} (opcodes {''.join(map(str, ops))})"); ok &= dl
    L, ops = run_steps([a0, X, Y] + JUNK, 20)
    base = L[:3] == R(Y) and "".join(map(str, ops)) == BASE_OPS and JUNK[0] in L
    print(f"BASE: {base} (opcodes {''.join(map(str, ops))})"); ok &= base
    A = [a0]
    for k in range(40): A.append(F(A[-1]))
    src = "S(SS)S(S(S(SS(SS))S))S"
    t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]; ops = []; states = {}
    widest = []; mx = 3
    for n in range(N):
        a = stk[-1]; ch, _ = hc.spine(a)
        if len(ch) > mx: mx = len(ch); widest.append(n)
        states[n] = stk[::-1][:3] if (n in widest or (widest and n - widest[-1] < 300)) else None
        ops.append(len(ch))
        a = stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    passed = total = 0
    for n in widest:
        E = states[n][0]; sp = hc.spine(E)[0]; m = len(sp) - 4
        if m < 2: continue
        total += 1
        # after opening E_m (1 step): front a_{m−1}, X = b_{m−1}, Y = a_{m+1}
        good = sp[0] == A[m - 1] and sp[1] == b(A[m - 1]) and sp[2] == A[m + 1]
        k = m - 1; T = 4 * k + 20
        st = states.get(n + 1 + T)
        word = "".join(chr(48 + o) for o in ops[n + 1:n + 1 + T])
        good = good and st is not None and st == R(frames_on(A[m + 1], A, k)) and word == "3011" * k + BASE_OPS
        passed += good
    print(f"CALL on the concrete run (k = m−1 after opening E_m): {passed}/{total} epochs")
    ok &= passed == total and total > 0
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILS")
