"""Base cases of the gadget counters for all mu >= 4 at once (main agent): gadget N opaque, base
B = S(SS(S(SS))(S(S(SS)S)(S S N))). (0) [B, x, y | ?] reaches [Z, V Z, (Z(SZ))(V Z)] without opening N, x, y or the rest;
(1) [S(S S N B), x, y | ?] reaches the same with CALL / UNROLL macros for the level-0 call B only, and its 3-step state
is [B, N·B, Z, ...]."""
import sys
sys.setrecursionlimit(100000)
from symb import parse
import tern_proof as TP
from kcounter_general import E2, N, X3
B = ("S", ((("S", "S"), parse("S(SS)")), (parse("S(S(SS)S)"), (("S", "S"), N))))
V = (("S", "S"), N); Z = ("x", "y")
goal = [Z, (V, Z), ((Z, ("S", Z)), (V, Z))]
def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return t, a
def run_plain(K, cap=200):
    """concrete head steps; level-0 macros: CALL for front B, UNROLL for front (N·B)·Y'"""
    tr = []
    for n in range(cap):
        if K[:3] == goal: return n, tr
        if "?" in K[:3]: return None, tr + ["unknown rest reached"]
        f = K[0]
        if f == B and len(tr) > 0:
            Zp = (K[1], K[2]); tr.append("[call 0]"); K = [Zp, (V, Zp), ((Zp, ("S", Zp)), (V, Zp)), "?"]; continue
        if isinstance(f, tuple) and isinstance(f[0], tuple) and f[0][0] == N and f[0][1] == B:
            Y = ((X3, B), f[1]); tr.append("[unroll 0]"); K = [Y, (V, Y), ((Y, ("S", Y)), (V, Y)), "?"]; continue
        h, args = spine(f)
        if h != "S": return None, tr + [f"opened {h}"]
        tr.append(len(args)); K = args + [K[2], (K[1], K[2])] + K[3:]
    return None, tr
n0, tr0 = run_plain([B, "x", "y", "?"])
print("level 0:", "goal reached" if n0 is not None else "FAILED", "trace:", tr0)
L1 = ("S", ((("S", "S"), N), B))
K = [L1, "x", "y", "?"]
# first three steps by hand to check the continuation form
h, a = spine(K[0]); K = a + [K[2], (K[1], K[2])] + K[3:]
h, a = spine(K[0]); K = a + [K[2], (K[1], K[2])] + K[3:]
h, a = spine(K[0]); K = a + [K[2], (K[1], K[2])] + K[3:]
print("level 1 three-step state in continuation form [B, N·B, Z]:", K[:3] == [B, (N, B), Z])
n1, tr1 = run_plain(K)
print("level 1:", "goal reached" if n1 is not None else "FAILED", "trace after the first 3 steps:", tr1)
