"""explore_levels for a driver configuration C1_G(P) given as gadget G and base P (main agent)."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
G = parse(sys.argv[1]); B = parse(sys.argv[2]); STEPS = int(sys.argv[3]); TOP = int(sys.argv[4]); CAP = int(sys.argv[5])
P = hc.from_tuple(B); g = hc.from_tuple(G)
Q = hc.app(hc.app(hc.app(0, 0), g), P); third = hc.app(hc.app(P, hc.app(0, P)), Q)
stk = [-5, -4, -3, third, Q, P]
freq = collections.Counter(); first = {}
for n in range(STEPS):
    a = stk[-1]; args, h = hc.spine(a)
    if h != 0 or len(stk) < 3: print("stopped at", n); break
    freq[a] += 1; first.setdefault(a, n)
    stk.pop(); bb = stk.pop(); cc = stk.pop()
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
cands = [a for a, f in freq.most_common() if hc.size(a) >= 4][:TOP]
calls = sorted((hc.size(a), hc.call_time(a, CAP), freq[a], first[a], a) for a in cands if hc.call_time(a, CAP) is not None)
print(f"{len(freq)} distinct fronts; calls among top {TOP}: {len(calls)}")
for sz, T, f, fs, a in calls[:24]:
    print(f"  size {sz:6d}  T {T:8d}  front {f:6d}x  first {fs:7d}  {hc.show(a)[:90]}")
