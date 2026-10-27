"""Counterexample hunt for the leftmost-path finite half: trees over an alphabet of gadget pieces (sizes far beyond the
16-leaf census).  For every term in a flag-0 L36 class whose M35 class has an hnf, walk the leftmost path up to NODES
nodes (per-round head-step budget BUD).  Outcomes: S (ends at the leaf S), bot? (a round exceeded the budget: treated as
unknown/probably bottom), long (NODES nodes without ending: candidate counterexample)."""
import sys, time
from dm import *
from classes import cls, LFl, MFl
NODES, BUD = 400, 20000
ALPHA = {"S": "S", "SS": "SS", "SSS": "SSS", "S(SS)": "S(SS)", "B": "S(SS)(SS)", "M": "S(S(SS))(S(SS))",
         "SS(SS)": "SS(SS)", "S(SSS)": "S(SSS)"}
alpha = [parse(v) for v in ALPHA.values()]
def trees(n):
    if n == 1:
        for a in alpha: yield a
        return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def walk(u):
    maxsz = 0
    for j in range(NODES):
        args, h = spine(u)
        if len(args) == 0: return "S", j, maxsz
        if len(args) <= 2: u = args[0]; continue
        st = list(reversed(args)); k = 0
        while len(st) > 2:
            a = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
            if k > BUD: return "bot?", j, maxsz
        u = st[-1]; maxsz = max(maxsz, size(u))
        if maxsz > 200000: return "huge", j, maxsz
    return "long", NODES, maxsz
from collections import Counter
stat = Counter(); longest = []
t0 = time.time()
for n in range(1, int(sys.argv[1]) + 1):
    for t in trees(n):
        c = cls(t)
        if LFl[c[0]] == 1 or MFl[c[1]] == 0: stat[("skip", LFl[c[0]], MFl[c[1]])] += 1; continue
        w, j, ms = walk(t)
        stat[w] += 1
        if w in ("long", "huge"): print("CANDIDATE", show(t), c, w, j, ms, flush=True)
        if w == "S": longest.append((j, show(t), c)); longest = sorted(longest)[-5:]
    print(n, dict(stat), "longest S-walks:", longest[-3:], round(time.time() - t0), "s", flush=True)
