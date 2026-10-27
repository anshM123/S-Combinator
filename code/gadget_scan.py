"""Multiplier gadgets (main agent): levels P_{m+1} = S(S S G P_m) for every S-term G up to N leaves, over three bases;
report the growth law of the call times T_0..T_M (call = generic run hands x·y to the front, tape untouched)."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, trees, show
import hc
N = int(sys.argv[1]); M = int(sys.argv[2]); CAP = int(sys.argv[3])
bases = {"SS": parse("SS"), "S(SSbc)": parse("S(SS(S(SS(SS)))(S(S(SS)S)(SS(SS))))"),
         "L0tern": parse("S(SS(S(SS)(SS(SS)(SS)))(S(S(SS)S)(SS(SSS(SS)))))")}
def growth(T):
    d = [b - a for a, b in zip(T, T[1:])]
    if len(set(d)) == 1: return f"linear(+{d[0]})"
    for a in range(2, 12):
        cs = {T[i + 1] - a * T[i] for i in range(len(T) - 1)}
        if len(cs) == 1: c = cs.pop(); return f"x{a}{'+' if c >= 0 else ''}{c}"
    return "other " + str([round(b / a, 2) for a, b in zip(T, T[1:]) if a])
res = collections.defaultdict(list)
for n in range(1, N + 1):
    for G in trees(n):
        for bn, B in bases.items():
            P = hc.from_tuple(B); g = hc.from_tuple(G); T = []
            for m in range(M + 1):
                t = hc.call_time(P, CAP)
                if t is None: break
                T.append(t); P = hc.app(0, hc.app(hc.app(hc.app(0, 0), g), P))
            if len(T) == M + 1 and T[-1] > T[-2]: res[growth(T)].append((show(G), bn, T))
for k in sorted(res, key=lambda k: (not k.startswith("x"), k)):
    L = res[k]
    print(f"{k}: {len(L)}   e.g. " + "; ".join(f"G={g} base {bn} T={T}" for g, bn, T in L[:3]))
