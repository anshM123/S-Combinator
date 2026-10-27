"""Concrete certification of the ternary counter theorem (main agent).
(a) T_m = 13·3^m - 5 and the return top [Z, V'Z, (Z(SZ))(V'Z)] for m <= MM, tape untouched, no atom opened;
(b) the 3-step state of L_1(x, y) is [L_0, G·L_0, Z, ...];
(c) the head run of the 22-leaf term has C1'(k) = [L_k, SSG·L_k, L_k(S L_k)(SSG·L_k)] on top exactly at
    t'_k = (143·3^k - 39)/2 - 28k for k = 1..KMAX;
(d) the opcode word predicted by the symbolic traces (call words via the call-step trace, cycles via the driver trace)
    equals the real opcode word up to t'_KMAX."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc, tern_proof as TP
MM = int(sys.argv[1]); KMAX = int(sys.argv[2])
G = hc.from_tuple(parse("SSS(SS)")); SS = hc.app(0, 0); Vp = hc.app(SS, G)
Lv = [hc.from_tuple(TP.L0)]
for m in range(max(MM, KMAX) + 2): Lv.append(hc.app(0, hc.app(hc.app(SS, G), Lv[-1])))
def gen_run(P, nsteps, stop_xy=True):
    X, Y = -1, -2; XY = hc.app(X, Y); stk = [-6, -5, -4, -3, Y, X, P]; floor = 4; ops = []; states = {}
    for t in range(nsteps):
        if stop_xy and stk[-1] == XY: return t, stk, ops, states
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
        if h != 0: raise ValueError("atom opened")
        if len(stk) < floor: raise ValueError("tape touched")
        ops.append(len(args)); stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
        if t == 2: states[3] = stk[-1:-4:-1]
    return None, stk, ops, states
w = []
okA = True
for m in range(MM + 1):
    T, stk, ops, st = gen_run(Lv[m], 10 ** 8)
    Z = hc.app(-1, -2)
    top = stk[-1:-4:-1] == [Z, hc.app(Vp, Z), hc.app(hc.app(Z, hc.app(0, Z)), hc.app(Vp, Z))]
    okA &= (T == 13 * 3 ** m - 5) and top
    w.append(ops)
    if m == 1: print("(b) 3-step state of L_1 in continuation form:", st[3] == [Lv[0], hc.app(G, Lv[0]), Z])
print(f"(a) T_m = 13·3^m - 5 with the stated return top, tape untouched, for m = 0..{MM}: {okA}")
# predicted call words from the call-step trace: w_m = 1 3 0 · w_{m-1} · B1 · u_{m-1} · B2 · u_{m-1}, u = w[3:]
B1 = [5, 0, 1, 0, 2, 1, 0, 2, 3, 0]; B2 = [3, 3, 0]
okW = all(w[m] == [1, 3, 0] + w[m - 1] + B1 + w[m - 1][3:] + B2 + w[m - 1][3:] for m in range(2, MM + 1))
print(f"    call-word recursion w_m = 130·w_(m-1)·B1·u_(m-1)·B2·u_(m-1) for m = 2..{MM}: {okW}")
# (c), (d)
args, h = hc.spine(hc.from_tuple(parse("S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS))))"))); stk = args[::-1]
def C1(k):
    Q = hc.app(hc.app(SS, G), Lv[k]); return [Lv[k], Q, hc.app(hc.app(Lv[k], hc.app(0, Lv[k])), Q)]
tk = {(143 * 3 ** k - 39) // 2 - 28 * k: k for k in range(1, KMAX + 1)}
last = max(tk); ops = []; hits = 0
for t in range(last + 1):
    if t in tk:
        good = stk[-1:-4:-1] == C1(tk[t]); hits += good
        print(f"(c) step {t}: C1'({tk[t]}) on top: {good}", flush=True)
    if t == last: break
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); a_args, _ = hc.spine(a)
    ops.append(len(a_args)); stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(a_args))
cyc = [("call", 0), ("eng", 4), ("eng", 0), ("resume", 1), ("eng", 3), ("eng", 3), ("eng", 0), ("resume", 0),
       ("eng", 3), ("eng", 0), ("resume", 1), ("eng", 5), ("eng", 0), ("resume", 1)]
def wd(m):
    while len(w) <= m:
        p = w[-1]; w.append([1, 3, 0] + p + B1 + p[3:] + B2 + p[3:])
    return w[m]
t1 = min(tk); pred = ops[:t1]
for k in range(1, KMAX):
    for kind, v in cyc:
        if kind == "eng": pred.append(v)
        elif kind == "call": pred += wd(k + v)
        else: pred += wd(k + v)[3:]
print(f"(d) predicted opcode word == real opcode word on all {len(ops)} steps: {pred == ops} (lengths {len(pred)}, {len(ops)})")
