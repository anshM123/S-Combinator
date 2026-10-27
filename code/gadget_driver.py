"""Gadget drivers (main agent): for a gadget X and base B, levels L_0 = B, L_{m+1} = S(S S X L_m); check
(1) the levels are calls returning the top [Z, (SSX)Z, (Z(SZ))((SSX)Z)], with T_m;
(2) the configuration C1_X(k) = [L_k, SSX·L_k, L_k(S L_k)(SSX·L_k)] (atoms below) reaches C1_X(k+1) on top, for k = 0..K."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
K = int(sys.argv[1])
SS = hc.app(0, 0)
gadgets = {"SS (x1? W)": "SS", "SSSS": "SSSS", "SSS(SS)": "SSS(SS)", "SS(SS(SS))": "SS(SS(SS))", "SS(SSS(SS))": "SS(SSS(SS))",
           "SS(S(SS)SS)": "SS(S(SS)SS)", "SS(SS(SS(SS)))": "SS(SS(SS(SS)))"}
bases = {"BC base": "S(SS(S(SS(SS)))(S(S(SS)S)(SS(SS))))", "tern base": "S(SS(S(SS)(SS(SS)(SS)))(S(S(SS)S)(SS(SSS(SS)))))"}
for gn, gs in gadgets.items():
    for bn, bs in bases.items():
        X = hc.from_tuple(parse(gs)); Lv = [hc.from_tuple(parse(bs))]
        for m in range(K + 3): Lv.append(hc.app(0, hc.app(hc.app(SS, X), Lv[-1])))
        VX = hc.app(SS, X); Ts = []; tops = True
        for m in range(K + 2):
            stk = [-6, -5, -4, -3, -2, -1, Lv[m]]; XY = hc.app(-1, -2); T = None
            for t in range(4_000_000):
                if stk[-1] == XY: T = t; break
                a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
                if h != 0 or len(stk) < 4: break
                stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
            Ts.append(T)
            if T is None: tops = False; break
            Z = XY; tops &= stk[-2] == hc.app(VX, Z) and stk[-3] == hc.app(hc.app(Z, hc.app(0, Z)), hc.app(VX, Z))
        def C1(k):
            Q = hc.app(VX, Lv[k]); return [Lv[k], Q, hc.app(hc.app(Lv[k], hc.app(0, Lv[k])), Q)]
        reached = []
        if tops:
            for k in range(K):
                stk = [-9, -8, -7] + C1(k)[::-1]; goal = C1(k + 1); r = None
                for t in range(6_000_000):
                    if stk[-1:-4:-1] == goal: r = t; break
                    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
                    if h != 0 or len(stk) < 3: break
                    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
                reached.append(r)
        ratio = [round(b / a, 3) for a, b in zip(Ts, Ts[1:]) if a and b]
        print(f"X={gn:16s} {bn:10s} T={Ts} ratios={ratio} return-top ok={tops} cycles C1(k)->C1(k+1): {reached}", flush=True)
