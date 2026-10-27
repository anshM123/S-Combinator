"""Generalised level finder (main agent): frequent front elements of a head run, their generic behaviour on
[P, x, y, r1..r4] (time T until an atom-headed front; the top three at that moment as a pattern in x, y with Z = x·y),
grouped by pattern; reports groups with >= 3 members and geometric T growth (candidate level families)."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc
NAMES = {-1: "x", -2: "y", -3: "r1", -4: "r2", -5: "r3", -6: "r4"}
XY = hc.app(-1, -2)
def pat(i, depth=0):
    if i == XY: return "Z"
    if i in NAMES: return NAMES[i]
    if i == 0: return "S"
    if depth > 6: return "…"
    l, r = hc.L[i], hc.R[i]; sr = pat(r, depth + 1)
    return pat(l, depth + 1) + (("(" + sr + ")") if r > 0 and len(sr) > 1 else sr)
def behaviour(P, cap):
    stk = [-6, -5, -4, -3, -2, -1, P]
    for t in range(cap):
        a = stk[-1]; ch, h = hc.spine(a)
        if h != 0: return t, tuple(pat(e) for e in stk[-1:-4:-1])
        if len(stk) < 3: return None
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return None
def find(src, steps=30000, top=400, cap=200000):
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; freq = collections.Counter()
    for n in range(steps):
        if len(stk) < 3: break
        a = stk[-1]; freq[a] += 1
        stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    groups = collections.defaultdict(list)
    for a, f in freq.most_common(top):
        if hc.size(a) < 4: continue
        b = behaviour(a, cap)
        if b: groups[b[1]].append((hc.size(a), b[0], a))
    fams = []
    for p, members in groups.items():
        members.sort()
        Ts = sorted(set(t for _, t, _ in members))
        if len(Ts) >= 3 and Ts[-1] >= 2 * Ts[-2] - 4 and Ts[-1] > 20:
            fams.append((p, [(s, t) for s, t, _ in members][:8]))
    return fams
if __name__ == "__main__":
    for src in sys.argv[1:]:
        fams = find(src)
        print(f"{src}: {len(fams)} candidate level families")
        for p, m in fams[:3]: print(f"   return pattern {p}: (size, T) {m}")
