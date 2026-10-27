"""Agent U: an hnf-free S-term family whose single infinite head run moves a counter value twice
(P -> M -> Y), counts Y down, and then loops forever (Omega).  Exact symbolic rules + concrete checks.

Head machine on lists (top first):  [a, b, c] ++ R  ->  ch(a) ++ [c, b.c] ++ R.

Gadgets (all closed S-terms):
  Om  = S(SSS)S(SSS)                         (no hnf; its spine [SSS, S, SSS] runs forever, Lemma 2(c))
  q   = SS                                   (phase-3 layer code: APPLY then OPEN)
  V2.x = S x,  V1.x = S S q x                (the two layers written into M per unit)
  M_0 = D = S S S,  M_{m+1} = V1.(V2.M_m) = S S q (S M_m)          (M = wrapper nest, 2 layers per unit)
  P_0 = B1 = S (S S S) Om,  P_k = S (S (S (S P_{k-1}) V1)) V2       ("head-style" nest: predecessor FIRST)
  family:  Phi(k, m) = S P_k S M_m       (initial list [P_k, S, M_m])

Exact rules (proved symbolically below with opaque predecessors / tape elements):
  R1  (k>=1)  [P_k, x, M]        ->^4  [P_{k-1}, V2.M, V1.(V2.M), M.(V2.M), x.M]          (M -> M+1)
  R1z (k=0)   [B1, x, M]         ->^3  [M, S.M, Om.M, x.M]
  R2  (j>=1)  [M_j, t1, t2]      ->^3  [M_{j-1}, t2, L_j.t2, t1.t2],  L_j = q.(S M_{j-1})    (Y -> Y+1)
  R2z (j=0)   [D, t1, t2]        ->^2  [t2, S.t2, t1.t2]
  R3  (Y = L.Y')  [Y, d, F]      ->^2  [Y', (S M').Y', F, d.F]      (L = q.(S M'); F stays at position 3)
  R3z         [Om.Z, d, F]       ->^1  [SSS, S, SSS, Z, F, d.F]   then Omega's spine runs forever.
Zero tests are data driven: P_k / M_j / Y opened at the front expose different spines for 0 and >= 1.
Usage: python agent_u_transfer.py
"""
import sys
sys.setrecursionlimit(100000)
import symb
from symb import spine as sspine, show as sshow
from agent_u_sim import app, apps, parse, spine, run, size, show
from verify_model import load

# ---------------------------------------------------------------- symbolic (tuple) terms, opaque variables
def A(*xs):
    return symb.app(*xs)
sS = "S"
sOm = symb.parse("S(SSS)S(SSS)")
sq = symb.parse("SS")
sD = symb.parse("SSS")
sB1 = A("S", symb.parse("SSS"), sOm)

def steps(lst, n):
    """exactly n symbolic head steps; fails if a variable-headed element would be opened or hnf reached"""
    K = list(lst)
    for i in range(n):
        assert len(K) >= 3, ("hnf", i)
        h, aa = sspine(K[0])
        assert h == "S", ("opened opaque element", h, i)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
    return K

def check_symbolic():
    ok = True
    # R1: P_k = S(S(S(S p) V1) ) V2 with V1 = SSq (as a wrapper constant), V2 = S;  p, x, m opaque
    V1c = A("S", "S", sq)               # V1 as a constant: V1.x = S S q x
    V2c = "S"                           # V2.x = S x
    Pk = A("S", A("S", A("S", A("S", "p"), V1c)), V2c)
    got = steps([Pk, "x", "m"], 4)
    want = ["p", (V2c, "m"), (V1c, (V2c, "m")), ("m", (V2c, "m")), ("x", "m")]
    print("R1 ", got == want); ok &= got == want
    got = steps([sB1, "x", "m"], 3)
    want = ["m", ("S", "m"), (sOm, "m"), ("x", "m")]
    print("R1z", got == want); ok &= got == want
    Mj = A("S", "S", sq, A("S", "u"))   # M_j = S S q (S u), u = M_{j-1} opaque
    got = steps([Mj, "t", "w"], 3)
    want = ["u", "w", ((sq, ("S", "u")), "w"), ("t", "w")]
    print("R2 ", got == want); ok &= got == want
    got = steps([sD, "t", "w"], 2)
    want = ["w", ("S", "w"), ("t", "w")]
    print("R2z", got == want); ok &= got == want
    Y = ((sq, ("S", "e")), "y")          # Y = L.Y', L = q.(S e), e = stale M, y = Y' opaque
    got = steps([Y, "d", "F"], 2)
    want = ["y", (("S", "e"), "y"), "F", ("d", "F")]
    print("R3 ", got == want); ok &= got == want
    got = steps([(sOm, "z"), "d", "F"], 1)
    want = list(sspine(sOm)[1]) + ["z", "F", ("d", "F")]
    print("R3z", got == want); ok &= got == want
    return ok

# ---------------------------------------------------------------- concrete (hash-consed) terms
S = 0
Om = parse("S(SSS)S(SSS)")
q = parse("SS")
V1c = apps(S, S, q)
D = parse("SSS")
B1 = apps(S, parse("SSS"), Om)
def Mterm(m):
    t = D
    for _ in range(m): t = app(V1c, app(S, t))
    return t
def Pterm(k):
    t = B1
    for _ in range(k): t = apps(S, app(S, apps(S, app(S, t), V1c)), S)
    return t

def concrete(k, m0, extra=300):
    """simulate Phi(k, m0) and check every predicted checkpoint; return (ok, total predicted steps)"""
    K = [Pterm(k), S, Mterm(m0)]
    st = list(K); t = 0; ok = True
    def adv(n):
        nonlocal st, t
        st2, done, status = run(st, n)
        assert done == n and status == "running"
        st = st2; t += n
    # phase 1
    for i in range(k):
        x_before = st[1]; Mcur = st[2]
        adv(4)
        ok &= st[0] == Pterm(k - i - 1) and st[1] == app(S, Mcur) and st[2] == app(V1c, app(S, Mcur))
        ok &= st[2] == Mterm(m0 + i + 1)
    m = m0 + k
    Mfull = st[2]
    adv(3)                                            # R1z
    ok &= st[0] == Mfull and st[2] == app(Om, Mfull)
    # phase 2: M_m opened with (S.Mfull, Om.Mfull); Y_0 = Om.Mfull
    Y = app(Om, Mfull); Ys = [Y]
    for j in range(m, 0, -1):
        adv(3)
        ok &= st[0] == Mterm(j - 1) and st[1] == Ys[-1]
        L = app(q, app(S, Mterm(j - 1)))
        ok &= st[2] == app(L, Ys[-1])
        Ys.append(st[2])
    adv(2)                                            # R2z
    ok &= st[0] == Ys[-1]
    F = st[2]
    # phase 3: count Y down, F fixed at position 3
    for i in range(m, 0, -1):
        adv(2)
        ok &= st[0] == Ys[i - 1] and st[2] == F
    adv(1)                                            # R3z: Om.Mfull opened
    ok &= st[:4] == spine(Om) + [Mfull]
    total = t
    tail = st[3:]                                    # Mfull, F, ... must never be touched again
    adv(extra)
    ok &= st[-len(tail):] == tail
    return ok, total, len(st)

if __name__ == "__main__":
    print("symbolic rules:", check_symbolic())
    Mr, MF, MT = load("../data/model35_hn.txt"); sM = Mr.index("S")
    memo = {}
    def cls(t):
        if t == 0: return sM
        if t in memo: return memo[t]
        from agent_u_sim import L as LL, R as RR
        r = int(MT[cls(LL[t]), cls(RR[t])]); memo[t] = r; return r
    allok = True
    for k in range(0, 9):
        for m0 in range(0, 6):
            ok, total, ln = concrete(k, m0)
            phi = apps(S, Pterm(k), S, Mterm(m0))
            c = cls(phi)
            allok &= ok and c == 33
            if k in (0, 1, 3, 8) and m0 in (0, 2, 5):
                print(f"k={k} m0={m0}: checkpoints ok={ok}, predicted steps to Omega loop={total} "
                      f"(= 4k+3+3m+2+2m+1, m=k+m0: {4*k+3+5*(k+m0)+3}), |Phi|={size(phi)}, M35 class={c}")
    print("all (k <= 8, m0 <= 5) checkpoints and M35-bottom:", allok)
    print("smallest member Phi(0,0) =", show(apps(S, Pterm(0), S, Mterm(0))))
    print("Phi(1,0) =", show(apps(S, Pterm(1), S, Mterm(0))))
