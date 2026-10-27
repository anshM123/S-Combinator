"""Coarse orbits of the return form R(Z) = [Z, V·Z, (Z(SZ))(V·Z)] (main agent).
For V in {SS(SS), SS(SSS(SS))} and every S-term Z_0 with <= NMAX leaves: run the head machine from R(Z_0) (atoms below),
record every later state whose top three are R(Z') for some Z', and classify the orbit Z_0, Z_1, ... by the sizes of the
Z_i: 'succ' if each Z_{i+1} = S(V·Z_i), 'periodic' if a Z repeats, else 'other' (printed)."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, trees, show
import hc
NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
for vs in ("SS(SS)", "SS(SSS(SS))"):
    V = hc.from_tuple(parse(vs)); kinds = collections.Counter(); others = []
    for n in range(1, NMAX + 1):
        for t in trees(n):
            Z = hc.from_tuple(t)
            stk = [-9, -8, -7, hc.app(hc.app(Z, hc.app(0, Z)), hc.app(V, Z)), hc.app(V, Z), Z]
            orbit = [Z]; status = "ran"
            for s in range(STEPS):
                a = stk[-1]
                if s > 0 and len(stk) >= 3 and stk[-2] == hc.app(V, a) and stk[-3] == hc.app(hc.app(a, hc.app(0, a)), hc.app(V, a)):
                    orbit.append(a)
                    if len(orbit) > 40: break
                args, h = hc.spine(a)
                if h != 0: status = "reads below"; break
                if len(stk) < 3: status = "hnf"; break
                stk.pop(); bb = stk.pop(); cc = stk.pop()
                stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
            if len(orbit) < 3: kinds[f"<3 R-states ({status})"] += 1; continue
            if all(orbit[i + 1] == hc.app(0, hc.app(V, orbit[i])) for i in range(1, len(orbit) - 1)): kinds["succ"] += 1; continue
            if len(set(orbit)) < len(orbit): kinds["periodic/repeat"] += 1; continue
            kinds["other"] += 1
            if len(others) < 12: others.append((show(t), [hc.size(z) for z in orbit[:12]]))
    print(f"V = {vs}: {dict(kinds)}")
    for o in others: print("   other:", o)
