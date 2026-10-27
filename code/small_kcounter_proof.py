"""tau_mu = S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS N)) for all mu >= 4 at once (gadget N opaque) (main agent):
(0) base call B' = S(SS b' c'), b' = S(SS)(SS(SS)(SS)), c' = S(S(SS)S)(SSN): reaches [Z, VZ, (Z(SZ))(VZ)], N never opened;
(1) level-1 call L_1 = S(SSN B'): same, using [call 0] and [unroll 0], 3-step state [B', N·B', Z];
(2) the head run of tau_mu reaches C1(1) = [L_1, SSN·L_1, L_1(S L_1)(SSN·L_1)] with N never opened, using level-0 macros."""
import sys
sys.setrecursionlimit(100000)
from symb import parse
N = "N"; X3 = parse("SSS(SS)"); V = (("S", "S"), N)
bp = parse("S(SS)(SS(SS)(SS))"); cp = (parse("S(S(SS)S)"), V)
B = ("S", ((("S", "S"), bp), cp)); L1 = ("S", (V, B))
def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return t, a
def ret(Z): return [Z, (V, Z), ((Z, ("S", Z)), (V, Z)), "?"]
def run(K, goal, macros=True, cap=5000):
    tr = []
    for n in range(cap):
        if K[:len(goal)] == goal: return n, tr
        if "?" in K[:3]: return None, tr + ["unknown rest reached"]
        f = K[0]
        if macros and f == B: tr.append("[call 0]"); K = ret((K[1], K[2])); continue
        if macros and isinstance(f, tuple) and isinstance(f[0], tuple) and f[0][0] == N and f[0][1] == B:
            tr.append("[unroll 0]"); K = ret(((X3, B), f[1])); continue
        if macros and f == L1 and goal[0] != L1: tr.append("[call 1]"); K = ret((K[1], K[2])); continue
        h, args = spine(f)
        if h != "S": return None, tr + [f"opened {h}"]
        tr.append(len(args)); K = args + [K[2], (K[1], K[2])] + K[3:]
    return None, tr
Z = ("x", "y"); goal = [Z, (V, Z), ((Z, ("S", Z)), (V, Z))]
n, tr = run([B, "x", "y", "?"], goal, macros=False); print("(0) base call:", "ok" if n is not None else "FAILED", tr)
K = [L1, "x", "y", "?"]
for _ in range(3):
    h, a = spine(K[0]); K = a + [K[2], (K[1], K[2])] + K[3:]
print("    level-1 3-step state [B', N·B', Z]:", K[:3] == [B, (N, B), Z])
n, tr = run(K, goal); print("(1) level-1 call:", "ok" if n is not None else "FAILED", tr)
tau = parse("S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SS)))")       # placeholder shape; replace the gadget below
tau = ((((("S", ("S", "S")), "S"), "S"), parse("SS(SS)(SS)")), (parse("S(S(SS)S)"), V))
h, args = spine(tau)
C1 = [L1, (V, L1), ((L1, ("S", L1)), (V, L1))]
n, tr = run(list(args), C1)
print("(2) tau_mu reaches C1(1):", "yes" if n is not None else "NO", f"after {n} trace items" if n is not None else "", tr[-12:])
