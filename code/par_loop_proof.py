"""Exact parallel (ReplaceAll) run of the loop term S(S(S(S(SSS)(SSS))))SS (main agent, 2026-10-26) — Theorem PL.
D = S(SS), L = S D, right combs C_1 = L, C_{i+1} = L C_i (normal forms). Cycle starts and loop states:
  Σ_j = [D, L, C_j, C_{j−1} (C_2 C_j)],   Λ_i = [D, C_i, C_{j+1}, C_j (C_{i+1} C_{j+1})]   (inside cycle j; Λ_1 = Σ_{j+1}).
Lemmas, checked on the lazy parallel machine (lazy_par.py) with symbolic atoms — U, V, W normal forms (no pass changes
them), the rest r arbitrary terms (general atoms; they age but must never reach the first three positions):
  (I)  Σ_j ++ r  →^12  Λ_{j−2} ++ r′    with C_{j−2} = W  (j ≥ 3; opcodes 110311031104)
  (II) Λ_i ++ r  →^8   Λ_{i−1} ++ r′    with C_{i−1} = U, C_j = V  (i ≥ 2; opcodes 11031104)
Composition: Σ_j → Λ_{j−2} → Λ_{j−3} → ⋯ → Λ_1 = Σ_{j+1} in 12 + 8(j − 3) passes. The concrete run reaches Σ_4 at pass 21,
so the parallel opcode word is u ∏_{j ≥ 4} 110311031104 (11031104)^{j−3} with u the first 21 opcodes.
Usage: python par_loop_proof.py [PASSES]"""
import sys
sys.setrecursionlimit(1000000)
import lazy_par as lz
from symb import parse

SRC = "S(S(S(S(SSS)(SSS))))SS"
D = lz.from_tuple(parse("S(SS)")); L = lz.app(0, D)
def Cc(i, base=None):
    """C_i over the concrete L, or L^(i−k) applied to an atom standing for C_k: base = (atom, k)"""
    if base is None:
        c = L; k = 1
    else:
        c, k = base
    for _ in range(i - k): c = lz.app(L, c)
    return c
def Sigma(Cj, Cjm1, C2): return [D, L, Cj, lz.app(Cjm1, lz.app(C2, Cj))]
def Lam(Ci, Cj1, Cj, Ci1): return [D, Ci, Cj1, lz.app(Cj, lz.app(Ci1, Cj1))]

def run_sym(window, nsteps, njunk=4):
    """the lazy machine on window ++ junk; fails if a junk atom reaches the first three positions or an opaque head is
    opened; returns (opcodes, window part of the final list as values)"""
    junk = [-(100 + i) for i in range(njunk)]
    stk = [(e, 0) for e in reversed(window + junk)]; ops = []
    for now in range(nsteps):
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        if any(x in junk for x in (x1, x2, x3)): raise lz.Opaque("the unknown rest was read")
        v1, v2, v3 = lz.delay(x1, now - b1), lz.delay(x2, now - b2), lz.delay(x3, now - b3)
        c = lz.spine(v1); ops.append(len(c))
        stk.append((lz.app(v2, v3), now + 1)); stk.append((v3, now + 1)); stk.extend((e, now + 1) for e in reversed(c))
    vals = [lz.delay(x, nsteps - b) for x, b in reversed(stk)]
    first_junk = next(i for i, (x, b) in enumerate(reversed(stk)) if x in junk)
    return "".join(chr(48 + o) for o in ops), vals[:first_junk]

def same(xs, ys):
    return len(xs) >= len(ys) and all(lz.canon(x) == lz.canon(y) for x, y in zip(xs, ys))

if __name__ == "__main__":
    NP = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    ok = True
    U, V, W = -1, -2, -3
    lz.NORMAL.update({U, V, W})
    # (I): C_{j−2} = W, so C_{j−1} = L W, C_j = L(L W), C_{j+1} = L(L(L W)); C_2 = L L is concrete
    Cjm2 = W; Cjm1 = lz.app(L, W); Cj = lz.app(L, Cjm1); Cj1 = lz.app(L, Cj); C2 = lz.app(L, L)
    o1, fin = run_sym(Sigma(Cj, Cjm1, C2), 12)
    good = o1 == "110311031104" and same(fin, Lam(Cjm2, Cj1, Cj, Cjm1))
    print(f"(I)  Σ_j →^12 Λ_(j−2), nothing below read: {good} (opcodes {o1})"); ok &= good
    # (II): C_{i−1} = U, C_i = L U, C_{i+1} = L(L U); C_j = V, C_{j+1} = L V
    Ci = lz.app(L, U); Ci1 = lz.app(L, Ci); Cj1 = lz.app(L, V)
    o2, fin = run_sym(Lam(Ci, Cj1, V, Ci1), 8)
    good = o2 == "11031104" and same(fin, Lam(U, Cj1, V, Ci))
    print(f"(II) Λ_i →^8 Λ_(i−1), nothing below read: {good} (opcodes {o2})"); ok &= good
    # Λ_1 = Σ_{j+1}: [D, C_1, C_{j+1}, C_j (C_2 C_{j+1})] is Σ_{j+1} by definition (C_1 = L).
    # concrete run: reaches Σ_4 at pass 21; predicted word and Σ_j at the predicted passes
    lz.NORMAL.clear()
    t = lz.from_tuple(parse(SRC)); stk = [(e, 0) for e in reversed(lz.plain_spine(t))]; ops = []
    pred_at = {4: 21}
    for j in range(4, 2000): pred_at[j + 1] = pred_at[j] + 12 + 8 * (j - 3)
    hits = tried = 0; maxj = max(j for j, p in pred_at.items() if p <= NP)
    check_j = set(range(4, min(maxj, 60) + 1)) | {maxj}
    at_pass = {pred_at[j]: j for j in check_j}
    for now in range(NP):
        if now in at_pass:
            j = at_pass[now]; vals = [lz.delay(x, now - b) for x, b in reversed(stk[-4:])]
            tried += 1; hits += same(vals, Sigma(Cc(j), Cc(j - 1), Cc(2)))
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        v1, v2, v3 = lz.delay(x1, now - b1), lz.delay(x2, now - b2), lz.delay(x3, now - b3)
        c = lz.spine(v1); ops.append(len(c))
        stk.append((lz.app(v2, v3), now + 1)); stk.append((v3, now + 1)); stk.extend((e, now + 1) for e in reversed(c))
    print(f"concrete parallel run is at Σ_j at the predicted pass for {hits}/{tried} checked j (4..{min(maxj, 60)} and {maxj})")
    ok &= hits == tried and tried > 0
    word = "".join(chr(48 + o) for o in ops)
    pred = word[:21] + "".join("110311031104" + "11031104" * (j - 3) for j in range(4, maxj + 2))
    wok = word == pred[:len(word)]
    print(f"predicted opcode word u ∏ 110311031104 (11031104)^(j−3) equals the concrete parallel word for {len(word)} passes: {wok}")
    ok &= wok
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILS")
