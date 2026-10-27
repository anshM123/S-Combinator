"""Inner-loop lemma with full opacity, and the driver hypothesis (main agent), for SS(S(SS))(SS)SS(S(SS))."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
src, B, N = "SS(S(SS))(SS)SS(S(SS))", "202203", 40000
SSS = hc.app(hc.app(0, 0), 0); LAYER = hc.app(0, SSS)
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []; snaps = {}
for n in range(N):
    snaps[n] = list(stk[-4:])[::-1]
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(str(len(ch)))
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
w = "".join(ops); i = w.rfind(B * 40); E1 = snaps[i][2]
# (1) block lemma, everything but SSS, the layer and E1 opaque
XT = -11; stk = [-16, -15, -14, -13, E1, hc.app(LAYER, XT), SSS]; ok = True
for step in range(6):
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, hd = hc.spine(a)
    if hd != 0: ok = False; break
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
top = stk[::-1][:3]
print("block lemma [SSS, S(SSS)·T, E1 | r] ->6 [SSS, T, E1 | r']  for opaque T, r:", ok and top == [SSS, XT, E1])
# (2) is E1 itself a comb S(SSS)^k · base?  peel and find the base
def peel(t):
    k = 0
    while t > 0 and hc.L[t] == LAYER: t = hc.R[t]; k += 1
    return k, t
k1, b1 = peel(E1)
# X at the first block start of the current cycle and of the next cycle
def cycle_starts():
    starts = []; j = 0
    while True:
        j = w.find(B, j)
        if j < 0: break
        starts.append(j); j += len(B)
    return starts
blk = set(cycle_starts())
firsts = [s for s in sorted(blk) if s - len(B) not in blk]
info = []
for s in firsts[-4:]:
    X0 = snaps[s][1]; kx, bx = peel(X0); kE, bE = peel(snaps[s][2])
    info.append((s, kx, kE, bx == bE))
print("cycle starts (step, layers of X, layers of third element E, same base):", info)
