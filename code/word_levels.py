"""Words of gadgets in the levels (main agent): L_0 = S(SS(S(SS))(S(S(SS)S)(SS X_b))), L_{m+1} = S(S S X_{a_m} L_m) with
letters a_m in {3,4,5}; test the call property, the return top [Z, V_b Z, (Z(SZ))(V_b Z)] (V_b from the base) and
T_{m+1} = mu(a_m) T_m + 2 mu(a_m) + 4, for random words."""
import sys, random
sys.setrecursionlimit(1000000)
from symb import parse
import hc
SS = hc.app(0, 0)
def gad(mu):
    g = hc.from_tuple(parse("SSS(SS)"))
    for _ in range(mu - 3): g = hc.app(SS, g)
    return g
random.seed(5); ok_call = ok_top = ok_T = 0; n = 0
XY = hc.app(-1, -2)
for trial in range(40):
    b = random.choice([3, 4, 5]); word = [random.choice([3, 4, 5]) for _ in range(5)]
    VB = hc.app(SS, gad(b))
    L = hc.app(0, hc.app(hc.app(SS, hc.from_tuple(parse("S(SS)"))), hc.app(hc.from_tuple(parse("S(S(SS)S)")), VB)))
    Tprev = 8
    for m, a in enumerate(word):
        L = hc.app(0, hc.app(hc.app(SS, gad(a)), L))
        stk = [-6, -5, -4, -3, -2, -1, L]; T = None
        for t in range(3_000_000):
            if stk[-1] == XY: T = t; break
            x = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(x)
            if h != 0 or len(stk) < 4: break
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
        n += 1
        if T is None: continue
        ok_call += 1
        ok_top += stk[-2] == hc.app(VB, XY) and stk[-3] == hc.app(hc.app(XY, hc.app(0, XY)), hc.app(VB, XY))
        ok_T += T == a * Tprev + 2 * a + 4
        Tprev = T
print(f"{n} levels over 40 random words: calls {ok_call}, return top from the base {ok_top}, "
      f"T = mu(a) T_prev + 2mu(a) + 4: {ok_T}")
