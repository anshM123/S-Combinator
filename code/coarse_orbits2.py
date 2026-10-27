"""Coarse orbits of R(Z) for Z = F[L_0] (contexts F <= NMAX leaves, holes = the base L_0) (main agent).
V and L_0 from the gadget scheme with X = SSS(SS) (ternary) or the binary counter (V = SS(SS), L_0 = S(SSbc))."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
from scheme_search import trees_with_holes, fill
NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
schemes = {"binary": ("SS(SS)", "S(SS(S(SS(SS)))(S(S(SS)S)(SS(SS))))"),
           "ternary": ("SS(SSS(SS))", "S(SS(S(SS))(S(S(SS)S)(SS(SSS(SS)))))")}
def tup_to_hc(t, L0):
    if t == "S": return 0
    if t == "H": return L0
    return hc.app(tup_to_hc(t[0], L0), tup_to_hc(t[1], L0))
for name, (vs, ls) in schemes.items():
    V = hc.from_tuple(parse(vs)); L0 = hc.from_tuple(parse(ls))
    kinds = collections.Counter(); others = []
    for n in range(1, NMAX + 1):
        for F in trees_with_holes(n):
            Z = tup_to_hc(F, L0)
            stk = [-9, -8, -7, hc.app(hc.app(Z, hc.app(0, Z)), hc.app(V, Z)), hc.app(V, Z), Z]
            orbit = [Z]; status = "ran"
            for s in range(STEPS):
                a = stk[-1]
                if s > 0 and len(stk) >= 3 and stk[-2] == hc.app(V, a) and stk[-3] == hc.app(hc.app(a, hc.app(0, a)), hc.app(V, a)):
                    orbit.append(a)
                    if len(orbit) > 30: break
                args, h = hc.spine(a)
                if h != 0: status = "reads below"; break
                if len(stk) < 3: status = "hnf"; break
                stk.pop(); bb = stk.pop(); cc = stk.pop()
                stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
            if len(orbit) < 4: kinds[f"<4 R-states ({status})"] += 1; continue
            succ = [orbit[i + 1] == hc.app(0, hc.app(V, orbit[i])) for i in range(len(orbit) - 1)]
            if all(succ[1:]): kinds["eventually succ"] += 1; continue
            if len(set(orbit)) < len(orbit): kinds["repeats"] += 1; continue
            kinds["other"] += 1
            if len(others) < 15: others.append((show(F), [hc.size(z) for z in orbit[:10]], "".join("s" if x else "." for x in succ[:20])))
    print(f"{name}: {dict(kinds)}")
    for o in others: print("   other:", o)
