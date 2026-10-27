"""S-numerals iterate calls (main agent). n̄ = (SS·)^{n-1} SS. Claims: for every call P,
(a) [(n̄·P)·Z, v1, v2 | r] brings Z to the front after exactly 2n + (n-1)·T(P) steps (Z, v's atoms; r never popped);
(b) S(S S n̄ P) is a call with T = n·T(P) + 2n + 3."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
def numeral(n):
    g = hc.app(0, 0)
    for _ in range(n - 1): g = hc.app(hc.app(0, 0), g)
    return g
def iter_time(G, P, cap=10 ** 7):
    Z, V1, V2 = -11, -12, -13
    stk = [-8, -7, -6, V2, V1, hc.app(hc.app(G, P), Z)]; floor = 3
    for t in range(cap):
        a = stk[-1]
        if a == Z: return t
        args, h = hc.spine(a)
        if h != 0: return None
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        if len(stk) < floor: return None
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return None
calls = {"SS": hc.from_tuple(parse("SS")), "S(SSbc)": hc.from_tuple(parse("S(SS(S(SS(SS)))(S(S(SS)S)(SS(SS))))"))}
P2 = calls["SS"]
for _ in range(3): P2 = hc.app(0, hc.app(hc.app(0, P2), hc.app(P2, 0)))   # binary tree call, T = 30
calls["seq-level3"] = P2
ok_a = ok_b = 0; tot = 0
for name, P in calls.items():
    TP = hc.call_time(P, 10 ** 6)
    for n in range(1, 11):
        G = numeral(n); tot += 1
        ta = iter_time(G, P); ok_a += ta == 2 * n + (n - 1) * TP
        tb = hc.call_time(hc.app(0, hc.app(hc.app(hc.app(0, 0), G), P)), 10 ** 7); ok_b += tb == n * TP + 2 * n + 3
    print(f"P = {name} (T = {TP}): checked n = 1..10")
print(f"(a) iteration time formula: {ok_a}/{tot}; (b) level call time formula: {ok_b}/{tot}")
