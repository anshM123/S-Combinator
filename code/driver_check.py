"""Driver theorem checks (main agent).
(a) smallest symbolic level j for which the macro derivation C1(j) -> C1(j+1) in driver_proof.py goes through;
(b) step count of one cycle from the derivation (CALL costs T_m = 2^(m+4) - 8, RESUME costs T_m - 6);
(c) concrete check: the head run of SSS(SS)S(SS(SS)) has top three C1(k) = [P_k, Q_k, P_k(S P_k)Q_k] exactly at
    t_k = 144*2^k - 48k - 104, for k = 2..KMAX.
"""
import sys
sys.setrecursionlimit(1000000)
import driver_proof as D
from symb import parse

def T(m): return 2 ** (m + 4) - 8

def derive(jmin):
    D.JMIN = jmin
    start = [D.P(0), D.Q(0), ((D.P(0), ("S", D.P(0))), D.Q(0)), D.JUNK]
    goal = [D.P(1), D.Q(1), ((D.P(1), ("S", D.P(1))), D.Q(1))]
    try:
        n, calls = D.run(start, goal, verbose=False)
    except ValueError as e:
        return None, str(e)
    return n, calls

for jmin in range(0, 7):
    n, calls = derive(jmin)
    if n is None:
        print(f"j >= {jmin}: derivation fails ({calls})", flush=True)
        continue
    eng = n - len(calls)
    print(f"j >= {jmin}: derivation succeeds: {eng} engine steps, {len(calls)} macros")
    break

def cycle_len(k):
    tot = eng
    for cl in calls:
        m = k + cl[0]
        tot += T(m) - 6 if cl[1] == "resume" else T(m)
    return tot
print("cycle length at k = 2..6 from the derivation:", [cycle_len(k) for k in range(2, 7)],
      " formula 144*2^k - 48:", [144 * 2 ** k - 48 for k in range(2, 7)])

# concrete levels
b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))"); W = ("S", "S")
L0 = ((("S", "S"), b), c)
Pk = [("S", L0)]
for m in range(16):
    Rm = ("S", ((("S", "S"), W), Pk[m])); Um = ((("S", "S"), Pk[m]), Rm); Pk.append(("S", Um))
def Qk(k): return ((("S", "S"), W), Pk[k])
def C1(k): return [Pk[k], Qk(k), ((Pk[k], ("S", Pk[k])), Qk(k))]

def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return a
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10
term = parse("SSS(SS)S(SS(SS))")
stk = spine(term)[::-1]            # stack: front of the list at the end
targets = {144 * 2 ** k - 48 * k - 104: k for k in range(2, KMAX + 1)}
last = max(targets)
ok = 0
for t in range(last + 1):
    if t in targets:
        k = targets[t]
        good = stk[-1:-4:-1] == C1(k)
        print(f"step {t}: top three == C1({k})? {good}", flush=True)
        ok += good
    a = stk.pop(); bb = stk.pop(); cc = stk.pop()
    stk.append((bb, cc)); stk.append(cc)
    stk.extend(reversed(spine(a)))
print(f"{ok} of {len(targets)} predicted C1 times confirmed")
