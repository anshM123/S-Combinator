"""Do the other binary counters of E54 run the same level machine? (main agent)
For each term, run its head run and report every step at which the top three are C1(k) = [P_k, Q_k, P_k(S P_k)Q_k]
for the levels P_k of SSS(SS)S(SS(SS)); also look for the bare level tokens P_k at the front with >= 2 elements behind.
"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))"); W = ("S", "S")
L0 = ((("S", "S"), b), c)
Pk = [("S", L0)]
for m in range(14):
    Rm = ("S", ((("S", "S"), W), Pk[m])); Um = ((("S", "S"), Pk[m]), Rm); Pk.append(("S", Um))
def Qk(k): return ((("S", "S"), W), Pk[k])
C1 = {k: [Pk[k], Qk(k), ((Pk[k], ("S", Pk[k])), Qk(k))] for k in range(14)}
level_of = {id(p): k for k, p in enumerate(Pk)}
Pset = {p: k for k, p in enumerate(Pk)}
def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return a
TERMS = ["SSS(SS)S(SS(SS))", "S(SS)SSS(SS(SS))", "SSS(S(SS)S)(SS(SS))", "SSS(SSS(SS)S(SS(SS)))(S(S(SS)(SS))S)",
         "SS(SS)SS(SS(SSS)(SS)S)(SS(SS))"]
STEPS = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
for src in TERMS:
    stk = spine(parse(src))[::-1]
    hits = []; first_tok = None
    for t in range(STEPS):
        if len(stk) < 3: hits.append(("hnf", t)); break
        top = stk[-1]
        if first_tok is None and top in Pset: first_tok = (t, Pset[top])
        if top in Pset:
            k = Pset[top]
            if stk[-1:-4:-1] == C1[k]: hits.append((t, k))
        a = stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append((bb, cc)); stk.append(cc); stk.extend(reversed(spine(a)))
    print(f"{src}: first bare level token at front (step, level) = {first_tok}; C1(k) hits (step, k): {hits[:8]}",
          flush=True)
