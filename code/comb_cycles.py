"""Cycle structure of a comb run (main agent): split the opcode word at occurrences of a marker element at the front
(the most frequent front element of maximal spine), then test whether consecutive cycle words have the form A·B^c·C."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc
src, N = sys.argv[1], int(sys.argv[2])
args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []; fronts = []
for n in range(N):
    a = stk[-1]; ch, _ = hc.spine(a); ops.append(len(ch)); fronts.append(a)
    stk.pop(); bb = stk.pop(); cc = stk.pop()
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
freq = collections.Counter(fronts[N // 4:])
# marker: a front element that occurs at roughly linearly growing gaps
best = None
for a, f in freq.most_common(30):
    pos = [i for i in range(len(fronts)) if fronts[i] == a]
    g = [y - x for x, y in zip(pos, pos[1:])]
    if len(g) < 8: continue
    d = [y - x for x, y in zip(g, g[1:])]
    tail = d[len(d) // 2:]
    if len(set(tail)) == 1 and tail[0] > 0: best = (a, pos, g); break
if best is None: print(src, ": no marker with linearly growing gaps"); raise SystemExit
a, pos, g = best
print(f"{src}: marker gaps {g[:12]} (second differences constant = {g[-1] - g[-2]})")
W = ["".join(map(str, ops[pos[i]:pos[i + 1]])) for i in range(len(pos) - 1)]
for i in range(len(W) - 3, len(W) - 1):
    w1, w2 = W[i], W[i + 1]
    # common prefix and suffix, then the inserted middle
    p = next((k for k in range(min(len(w1), len(w2))) if w1[k] != w2[k]), min(len(w1), len(w2)))
    q = next((k for k in range(min(len(w1), len(w2)) - p) if w1[-1 - k] != w2[-1 - k]), min(len(w1), len(w2)) - p)
    print(f"  cycle {i}: |w|={len(w1)} -> {len(w2)}; common prefix {p}, common suffix {q}; inserted: {w2[p:len(w2) - q]}")
