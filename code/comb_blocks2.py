"""How do X_m (second) and Y_m (fourth) evolve between block starts? (main agent) Contexts X_{m+1} = G[X_m] etc."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
from auto_prover import to_tuple, H
src, B, N = sys.argv[1], sys.argv[2], int(sys.argv[3])
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []; snaps = {}
for n in range(N):
    snaps[n] = (stk[-1], stk[-2], stk[-3], stk[-4])
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(str(len(ch)))
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
w = "".join(ops); i = w.rfind(B * 40)
starts = [i + k * len(B) for k in range(5)]
X = [snaps[s][1] for s in starts]; Y = [snaps[s][3] for s in starts]; E1 = snaps[starts[0]][2]
def short(t, depth=0):
    if t == H: return "□"
    if isinstance(t, str): return t
    if depth > 9: return "…"
    return short(t[0], depth + 1) + "(" + short(t[1], depth + 1) + ")"
print("E1 =", short(to_tuple(E1)), "| sizes X:", [hc.size(x) for x in X], "| sizes Y:", [hc.size(y) for y in Y])
for name, seq in (("X", X), ("Y", Y)):
    for j in range(3):
        ctx = to_tuple(seq[j + 1], {seq[j]: H}) if seq[j] != seq[j + 1] else None
        print(f"{name}_{j + 1} in terms of {name}_{j}: {short(ctx)[:160] if ctx else 'equal'}")
    # cross: X_{m+1} in terms of Y_m and vice versa
    print(f"{name}_1 in terms of Y_0: {short(to_tuple(seq[1], {Y[0]: H}))[:160]}")
