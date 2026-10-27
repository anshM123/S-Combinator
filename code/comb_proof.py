"""Exact proof for the comb run SS(S(SS))(SS)SS(S(SS)) (main agent).
Combs: C_0 = base (from the run), C_{m+1} = S(SSS)·C_m. Claims:
 (L) block lemma: [SSS, S(SSS)·T, E | r] ->6 [SSS, T, E | r'] for opaque T, E, r (so the loop over C_n takes 6n steps);
 (D) driver: [SSS, C_0, C_{j+2} | ?] reaches [SSS, C_{j+1}, C_{j+3}] (top three) for every j >= JMIN, with comb tokens;
 (T) transient: the concrete run reaches a cycle start [SSS, C_n0, C_{n0+2}].
Then the run is, forever, cycles 'loop of n blocks B, then the defect D' with n increasing by 1: exactly D·B^n·D·B^{n+1}⋯"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
SSS = hc.app(hc.app(0, 0), 0); LAYER = hc.app(0, SSS)
# (L) with E opaque too
T, E = -11, -12
stk = [-16, -15, -14, -13, E, hc.app(LAYER, T), SSS]; ok = True
for step in range(6):
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, hd = hc.spine(a)
    if hd != 0: ok = False; break
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
print("(L) block lemma for opaque T, E, r:", ok and stk[::-1][:3] == [SSS, T, E])
# base comb C_0 from the concrete run
src = "SS(S(SS))(SS)SS(S(SS))"
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; base = None; first_start = None
def peel(t):
    k = 0
    while t > 0 and hc.L[t] == LAYER: t = hc.R[t]; k += 1
    return k, t
for n in range(5000):
    top = stk[-1:-4:-1]
    if top[0] == SSS:
        kx, bx = peel(top[1]); ke, be = peel(top[2])
        if bx == be and ke == kx + 2 and kx >= 1 and first_start is None: first_start = (n, kx); base = bx
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
print("(T) first cycle start (step, n):", first_start)
# (D) symbolic driver with comb tokens ('C', d) = C_{j+d}
JUNK = "?"
def to_t(i):
    if i == 0: return "S"
    return (to_t(hc.L[i]), to_t(hc.R[i]))
BASE = to_t(base); LAY = to_t(LAYER); SSSt = to_t(SSS)
def is_tok(t): return isinstance(t, tuple) and len(t) == 2 and t[0] == "C" and isinstance(t[1], int)
def mk(f, a):
    if f == LAY and is_tok(a): return ("C", a[1] + 1)
    return (f, a)
def spine(t):
    xs = []
    while isinstance(t, tuple) and not is_tok(t): xs.append(t[1]); t = t[0]
    xs.reverse(); return t, xs
def unfold(t, jmin):
    if is_tok(t):
        if jmin + t[1] < 1: raise ValueError("comb level may be 0")
        return (LAY, ("C", t[1] - 1))
    return t
for jmin in range(1, 6):
    try:
        K = [SSSt, BASE, ("C", 2), JUNK]; steps = 0
        goal = [SSSt, ("C", 1), ("C", 3)]
        for it in range(200):
            if K[:3] == goal: break
            if JUNK in K[:3]: raise ValueError("unknown rest reached")
            f = unfold(K[0], jmin)
            h0, xs = spine(f)
            if is_tok(h0): h0, xs2 = spine(unfold(h0, jmin)); xs = xs2 + xs
            if h0 != "S": raise ValueError("opaque head")
            K = xs + [K[2], mk(K[1], K[2])] + K[3:]; steps += 1
        else: raise ValueError("goal not reached")
        print(f"(D) driver, all j >= {jmin}: [SSS, C_0, C_(j+2)] -> [SSS, C_(j+1), C_(j+3)] in {steps} head steps")
        break
    except ValueError as e:
        print(f"(D) j >= {jmin}: fails ({e})")
