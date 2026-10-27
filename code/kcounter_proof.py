"""Symbolic proofs for the gadget counters (main agent), for X_mu = (SS·)^(mu-3) SSS(SS), mu = 3..MU.
Levels L_{m+1} = S·(S S X L_m) over any base whose level calls return [Z, (SSX)Z, (Z(SZ))((SSX)Z)]; the engine of
tern_proof.py with G := X. For each mu: (1) call-lemma inductive step for every j >= JMIN (macros only at level j-1);
(2) driver C1_X(k) -> C1_X(k+1) for every k >= JMIN; (3) concrete base cases j = 0, 1 (base S(SS(S(SS))(S(S(SS)S)(SSX))),
return top and 3-step form) and concrete cycles for k < JMIN."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import tern_proof as TP
import hc
MU = int(sys.argv[1])
def gadget(mu):
    g = parse("SSS(SS)")
    for _ in range(mu - 3): g = (("S", "S"), g)
    return g
def show_t(t):
    return t if isinstance(t, str) else (show_t(t[0]) + ("(" + show_t(t[1]) + ")" if isinstance(t[1], tuple) else show_t(t[1])))
for mu in range(3, MU + 1):
    X = gadget(mu)
    TP.G = X; TP.V = (("S", "S"), X)
    res = []
    for jmin in range(1, 6):
        E = TP.Engine(jmin, maxlev=-1); Z = ("x", "y")
        K = [TP.L(0), "x", "y", TP.JUNK]; first = E.open_front(K[0]); E.items.append(("eng", len(first)))
        K = first + [K[2], TP.mk(K[1], K[2])] + K[3:]
        try: n = E.run(K, [Z, TP.mk(TP.V, Z), TP.mk(TP.mk(Z, TP.mk("S", Z)), TP.mk(TP.V, Z))])
        except ValueError: continue
        if n is not None: res.append(("call step", jmin, TP.trace(E.items))); break
    for jmin in range(1, 6):
        E = TP.Engine(jmin)
        def C1(d):
            Q = TP.mk(TP.mk(("S", "S"), X), TP.L(d)); return [TP.L(d), Q, TP.mk(TP.mk(TP.L(d), TP.mk("S", TP.L(d))), Q)]
        try: n = E.run(C1(0) + [TP.JUNK], C1(1))
        except ValueError: continue
        if n is not None: res.append(("driver", jmin, TP.trace(E.items))); break
    # concrete base checks with base B = S(SS(S(SS))(S(S(SS)S)(SSX)))
    SS = hc.app(0, 0); Xi = hc.from_tuple(X); VX = hc.app(SS, Xi)
    B = hc.app(0, hc.app(hc.app(SS, hc.from_tuple(parse("S(SS)"))), hc.app(hc.from_tuple(parse("S(S(SS)S)")), VX)))
    Lv = [B]
    for m in range(4): Lv.append(hc.app(0, hc.app(hc.app(SS, Xi), Lv[-1])))
    XY = hc.app(-1, -2); base_ok = True; T = []
    for m in range(2):
        stk = [-6, -5, -4, -3, -2, -1, Lv[m]]; st3 = None
        for t in range(10 ** 6):
            if stk[-1] == XY: break
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
            assert h == 0 and len(stk) >= 4
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
            if t == 2: st3 = stk[-1:-4:-1]
        T.append(t)
        base_ok &= stk[-2] == hc.app(VX, XY) and stk[-3] == hc.app(hc.app(XY, hc.app(0, XY)), hc.app(VX, XY))
        if m == 1: base_ok &= st3 == [Lv[0], hc.app(Xi, Lv[0]), XY]
    print(f"mu={mu} X={show_t(X)}: base cases ok={base_ok} (T_0, T_1 = {T})")
    for kind, jmin, tr in res: print(f"   {kind} valid for all levels >= {jmin}: {tr}")
