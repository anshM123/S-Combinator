"""Find recurring front elements of a head run and test which are calls (main agent).
Usage: python explore_levels.py TERM STEPS [TOP] [CAP]"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc
src = sys.argv[1]; STEPS = int(sys.argv[2]); TOP = int(sys.argv[3]) if len(sys.argv) > 3 else 400
CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 400000
t = hc.from_tuple(parse(src))
args, h = hc.spine(t); stk = args[::-1]
freq = collections.Counter(); first = {}; nbelow = {}
for n in range(STEPS):
    if len(stk) < 3: print("hnf at", n); break
    a = stk[-1]; freq[a] += 1; first.setdefault(a, n)
    stk.pop(); bb = stk.pop(); cc = stk.pop()
    ch, _ = hc.spine(a)
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
cands = [a for a, f in freq.most_common() if hc.size(a) >= 4][:TOP]
calls = []
for a in cands:
    T = hc.call_time(a, CAP)
    if T is not None: calls.append((hc.size(a), T, freq[a], first[a], a))
calls.sort()
print(f"{len(freq)} distinct front elements; tested {len(cands)} most frequent (size >= 4); calls: {len(calls)}")
for sz, T, f, fs, a in calls[:60]:
    print(f"  size {sz:6d}  T {T:8d}  at front {f:6d}x  first at {fs:7d}  {hc.show(a)[:100]}")
