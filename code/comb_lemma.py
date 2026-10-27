"""Inner-loop lemma for the comb run SS(S(SS))(SS)SS(S(SS)) (main agent): check X_m = S(SSS)·X_{m+1} and the analogous
peeling of Y; then run one block (6 head steps) symbolically with the tails as opaque atoms."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
src, B, N = sys.argv[1], sys.argv[2], int(sys.argv[3])
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []; snaps = {}
for n in range(N):
    snaps[n] = list(stk[-6:])[::-1]
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(str(len(ch)))
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
w = "".join(ops); i = w.rfind(B * 40); starts = [i + k * len(B) for k in range(4)]
SSS = hc.app(hc.app(0, 0), 0); LAYER = hc.app(0, SSS)            # S(SSS)
X = [snaps[s][1] for s in starts]; Y = [snaps[s][3] for s in starts]
print("X_m = S(SSS)·X_{m+1}:", all(X[k] == hc.app(LAYER, X[k + 1]) for k in range(3)))
# Y: find the peeled layer
for k in range(3):
    y, y1 = Y[k], Y[k + 1]
    print(f"Y_{k}: left part of Y equals ... L={hc.L[y] == hc.app(0, SSS) and False}; Y_k == app(?, Y_k+1): {hc.R[y] == y1}, "
          f"left = {'S(SSS)' if hc.L[y] == LAYER else hc.size(hc.L[y])}")
print("front at block starts:", [snaps[s][0] == SSS for s in starts], "| third element constant:", len({snaps[s][2] for s in starts}) == 1)
# symbolic block with opaque tails: [SSS, LAYER·xt, E1, LAYER·yt, r...]
E1 = snaps[starts[0]][2]
XT, YT = -11, -12
stk = [-15, -14, -13, hc.app(LAYER, YT), E1, hc.app(LAYER, XT), SSS]
for step in range(6):
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, hd = hc.spine(a)
    if hd != 0: print("opened an opaque element at step", step); break
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
top = stk[::-1][:4]
print("after 6 symbolic steps: front SSS:", top[0] == SSS, "| second = xt:", top[1] == XT, "| third = E1:", top[2] == E1,
      "| fourth = yt:", top[3] == YT, "| list grew by", len(stk) - 7)
