"""Exact structure of the countdown run S(SS)S(S(S(SSS)(SS)))S (main agent, 2026-10-26).

Epoch heads (the first list element at each epoch start) X_1, X_2, … satisfy, for every e >= 2,
    X_e = Ch(1, e−1),   Ch(k, e) = S S (S X_k) Ch(k+1, e)  (k < e),   Ch(e, e) = T_e := S (S X_e) (S S (S X_e)),
so each head is a chain through all earlier heads. An epoch maps the state [X_{m−1}, S S (S X_{m−1}), T_{m−1}] ++ r to
[X_m, S S (S X_m), T_m] ++ r′. Lemmas (checked here by symbolic head-machine runs; generic parts are opaque atoms, the
unknown rest below is junk that must never reach the first three positions):
  W  [S, S X_k, Ch(k+1, e), R] ++ r  →²  [S, S X_{k+1}, Ch(k+2, e), R, S X_k Ch(k+1, e) R] ++ r          (k+1 < e)
  E  [S, S X_{e−1}, T_e, R] ++ r     →³  [X_e, R, S S (S X_e) R, S X_{e−1} T_e R] ++ r
  O  [S S (S X_1) C, R′, R″] ++ r    →¹  [S, S X_1, C, R″, R′ R″] ++ r          (X_e = S S (S X_1) Ch(2, e−1), e >= 3)
  B  base: [X_2, R, S S (S X_2) R, S X_1 T_2 R] ++ r →^b [X_m, S S (S X_m), T_m] ++ r′ with X_m = S S (S X_1)(S S (S X_2) R)
     for an opaque R (R = Ch(3, m−1)); X_1, X_2 = T_1 concrete.
Composition (paper proof, PROOF.md): from the epoch start, O gives Φ(m−2, T_{m−1}) with Φ(e, R) := [S, S X_1, Ch(2, e), R];
W (e−2 times), E and O give Φ(e, R) →^{2e} Φ(e−1, S S (S X_e) R) for e >= 3, so the carried element runs through
R_e = Ch(e+1, m−1); at e = 2, E then B close the epoch with X_m = S S (S X_1) Ch(2, m−1) = Ch(1, m−1).
Transient: the concrete run reaches an epoch start whose head and all earlier heads satisfy the identities (checked).
Usage: python countdown_proof.py"""
import sys
sys.setrecursionlimit(1000000)
import hc
from symb import parse

S = 0
JUNK = [-91, -92, -93, -94, -95, -96]
def ap(*xs):
    r = xs[0]
    for x in xs[1:]: r = hc.app(r, x)
    return r

class Stuck(Exception):
    pass

def step(L):
    """one head step on a list (first element first); atoms (< 0) must never be opened, junk never among the first three"""
    if len(L) < 3: raise Stuck("hnf")
    if any(x in JUNK for x in L[:3]): raise Stuck("unknown rest read")
    a, b, c = L[0], L[1], L[2]
    args, h = hc.spine(a)
    if h != 0: raise Stuck("opaque atom opened")
    return list(args) + [c, hc.app(b, c)] + L[3:], len(args)

def run_steps(L, n):
    ops = []
    for _ in range(n): L, op = step(L); ops.append(op)
    return L, ops

def run_until(L, goal, cap=5000):
    ops = []
    for _ in range(cap):
        if L[:len(goal)] == goal: return L, ops
        L, op = step(L); ops.append(op)
    raise Stuck("goal not reached")

def T(X): return ap(S, ap(S, X), ap(S, S, ap(S, X)))

def heads_of_run(src, N, marker="2201"):
    t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]; w = ""; out = []
    for n in range(N):
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        w += chr(48 + len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        if w.endswith(marker): out.append((n + 1, stk[::-1][:3], len(stk)))
    return out, w

if __name__ == "__main__":
    src = "S(SS)S(S(S(SSS)(SS)))S"
    ok = True
    # W
    Xk, Xk1, C2, R = -1, -2, -3, -4
    Chk1 = ap(S, S, ap(S, Xk1), C2)
    L, ops = run_steps([S, ap(S, Xk), Chk1, R] + JUNK, 2)
    w_ok = L[:5] == [S, ap(S, Xk1), C2, R, ap(S, Xk, Chk1, R)]
    print(f"W: {w_ok} (opcodes {''.join(map(str, ops))})"); ok &= w_ok
    # E
    Xe1, Xe = -1, -2
    L, ops = run_steps([S, ap(S, Xe1), T(Xe), R] + JUNK, 3)
    e_ok = L[:4] == [Xe, R, ap(S, S, ap(S, Xe), R), ap(S, Xe1, T(Xe), R)]
    print(f"E: {e_ok} (opcodes {''.join(map(str, ops))})"); ok &= e_ok
    # O
    X1a, C, R1, R2 = -1, -3, -4, -5
    L, ops = run_steps([ap(S, S, ap(S, X1a), C), R1, R2] + JUNK, 1)
    o_ok = L[:5] == [S, ap(S, X1a), C, R2, hc.app(R1, R2)]
    print(f"O: {o_ok} (opcodes {''.join(map(str, ops))})"); ok &= o_ok
    # concrete heads, identities, base part
    eps, word = heads_of_run(src, 6000)
    H = [top[0] for _, top, _ in eps]                     # H[0] is the first epoch head (transient), X_1 = H[1], …
    X = {k: H[k] for k in range(1, len(H))}
    def Ch(k, e): return T(X[e]) if k == e else ap(S, S, ap(S, X[k]), Ch(k + 1, e))
    ident = all(X[e] == Ch(1, e - 1) for e in range(2, len(H)))
    starts = all(top == [X[k], ap(S, S, ap(S, X[k])), T(X[k])] for k, (_, top, _) in enumerate(eps) if k >= 2)
    print(f"identities X_e = Ch(1, e−1) for e = 2..{len(H) - 1}: {ident}; epoch starts [X_k, SS(SX_k), T_k] for k >= 2: {starts}")
    ok &= ident and starts
    Rb = -7
    X1, X2 = X[1], X[2]
    Ch2 = ap(S, S, ap(S, X2), Rb); Xm = ap(S, S, ap(S, X1), Ch2)
    start = [X2, Rb, Ch2, ap(S, X1, T(X2), Rb)] + JUNK
    try:
        L, bops = run_until(start, [Xm, ap(S, S, ap(S, Xm)), T(Xm)])
        b_ok = True
    except Stuck as e:
        b_ok = False; bops = []; print("B fails:", e)
    print(f"B: {b_ok} ({len(bops)} steps, opcodes {''.join(map(str, bops))})"); ok &= b_ok
    # epoch length and opcode word predicted by the composition, compared with the concrete run
    def epoch_word(m):
        """opcodes of the epoch from the start with head X_{m−1} to the start with head X_m"""
        out = "3"                                            # O on X_{m−1}
        for e in range(m - 2, 2, -1):                        # Φ(e, R) → Φ(e−1, …): W^(e−2), E, O
            out += "03" * (e - 2) + "021" + "3"
        out += "021"                                         # Φ(2, R): no W, then E
        return out + "".join(map(str, bops))                 # base part
    k0 = 3
    pred = "".join(epoch_word(m) for m in range(k0 + 1, len(H)))
    real = word[eps[k0][0]:eps[len(H) - 1][0]]
    print(f"predicted opcode word from the epoch start with head X_{k0} to the one with head X_{len(H) - 1} "
          f"({len(real)} steps) equals the concrete run: {pred == real}")
    ok &= pred == real
    # whole list: one epoch from [X_{m−1}, SS(SX_{m−1}), T_{m−1}] with junk below never reads the junk (that is what the
    # lemmas say); the items it leaves above the junk are [X_m, SS(SX_m), T_m] ++ P(m) with P(m) explicit, so the list at
    # epoch m is top(m) ++ P(m) ++ P(m−1) ++ … ++ P(k0+1) ++ (concrete list below the top three at epoch k0)
    t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]; snaps = {}
    want = {eps[k][0]: k for k in range(len(eps))}
    for n in range(eps[-1][0] + 1):
        if n in want: snaps[want[n]] = stk[::-1][:40]
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    def top(k): return [X[k], ap(S, S, ap(S, X[k])), T(X[k])]
    pushes = {}
    for m in range(k0 + 1, len(H)):
        L, _ = run_until(top(m - 1) + JUNK, top(m))
        pushes[m] = L[3:L.index(JUNK[0])]
    below = snaps[k0][3:]; passed = total = 0
    for m in range(k0 + 1, len(H)):
        below = pushes[m] + below
        pred_list = top(m) + below
        k = min(30, len(snaps[m]))
        total += 1; passed += pred_list[:k] == snaps[m][:k]
    print(f"whole list: first 30 entries predicted at {passed}/{total} epoch starts (pushes per epoch: "
          f"{[len(pushes[m]) for m in range(k0 + 1, min(k0 + 6, len(H)))]} …)")
    ok &= passed == total and total > 0
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILS")
