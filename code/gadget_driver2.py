"""Gadget drivers with adapted bases (main agent): base L0_X = S(S S b c_X), c_X = S(S(SS)S)(S S X), b from a small list."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
K = int(sys.argv[1])
SS = hc.app(0, 0)
gadgets = ["SS", "SSSS", "SS(SS)", "SSS(SS)", "SS(SS(SS))", "SS(SSS(SS))", "SS(S(SS)SS)", "SS(SS(SS(SS)))", "SS(SS(SSS(SS)))",
           "SS(SS(SS(SS(SS))))", "SSSSSS", "SS(SSSS)"]
def run_to(stk, pred, cap):
    for t in range(cap):
        if pred(stk): return t
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
        if h != 0 or len(stk) < 3: return None
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return None
for gs in gadgets:
    X = hc.from_tuple(parse(gs)); VX = hc.app(SS, X)
    cX = hc.app(hc.from_tuple(parse("S(S(SS)S)")), VX)
    for bs in ["S(SS)(SS(SS)(SS))", "S(SS(SS))", "S(" + "SS(" + gs + "))", "S(SS)(SS(SS))", "S(SS)"]:
        b = hc.from_tuple(parse(bs))
        Lv = [hc.app(0, hc.app(hc.app(SS, b), cX))]
        for m in range(K + 3): Lv.append(hc.app(0, hc.app(hc.app(SS, X), Lv[-1])))
        XY = hc.app(-1, -2); Ts = []; tops = True
        for m in range(K + 2):
            stk = [-6, -5, -4, -3, -2, -1, Lv[m]]
            T = run_to(stk, lambda s: s[-1] == XY, 5_000_000)
            Ts.append(T)
            if T is None: tops = False; break
            tops &= stk[-2] == hc.app(VX, XY) and stk[-3] == hc.app(hc.app(XY, hc.app(0, XY)), hc.app(VX, XY))
        if not tops: continue
        def C1(k):
            Q = hc.app(VX, Lv[k]); return [Lv[k], Q, hc.app(hc.app(Lv[k], hc.app(0, Lv[k])), Q)]
        cyc = []
        for k in range(K):
            goal = C1(k + 1); stk = [-9, -8, -7] + C1(k)[::-1]
            cyc.append(run_to(stk, lambda s: s[-1:-4:-1] == goal, 8_000_000))
        ratio = [round(b2 / a2, 3) for a2, b2 in zip(Ts, Ts[1:]) if a2 and b2]
        print(f"X={gs:18s} b={bs:22s} T={Ts} ratios={ratio[-2:]} cycles={cyc}", flush=True)
