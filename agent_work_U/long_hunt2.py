"""Gadget-alphabet hunt (memory-safe): trees over 8 gadget letters with exactly n letters; for flag-0 terms with an hnf,
walk the leftmost path (<= NODES nodes; per-round budget max(4000, 30*size)) and count large pushes (a pushed multiplier
at least as large as the popped one, child with an hnf).  Reports outcomes, the large-push distribution and candidates
(walks that do not end within NODES nodes)."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from collections import Counter
NODES = 400
ALPHA = ["S", "SS", "SSS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))", "SS(SS)", "S(SSS)"]
alpha = [parse(v) for v in ALPHA]
def trees(n):
    if n == 1:
        for a in alpha: yield a
        return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def walk(u):
    nlp = 0
    for j in range(NODES):
        if u == 0: return "S", j, nlp
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        args = spine(u)[0]
        st = list(reversed(args)); k = 0; bud = max(4000, 30 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", j, nlp
        c = st[-1]
        if size(c) > 100000: return "huge", j, nlp
        x = c; big = False
        while x != v and x != 0:
            if size(L[x]) >= size(q1): big = True
            x = R[x]
        if big and MFl[cls(c)[1]] == 1: nlp += 1
        u = c
    return "long", NODES, nlp
n = int(sys.argv[1])
stat = Counter(); lpd = Counter(); t0 = time.time(); best = []
for t in trees(n):
    c = cls(t)
    if LFl[c[0]] == 1 or MFl[c[1]] == 0: stat[("skip", LFl[c[0]], MFl[c[1]])] += 1; continue
    m = mark()
    w, j, nlp = walk(t)
    stat[w] += 1; lpd[nlp] += 1
    if w in ("long", "huge") or nlp >= 3:
        print("NOTE", w, j, nlp, show(t), c, flush=True)
    if w == "S" and j >= 12: best.append((j, nlp, show(t)))
    truncate(m); clear_cache(m)
best.sort()
print(n, dict(stat), "large-push distribution:", sorted(lpd.items()), "longest S-walks:", best[-4:],
      round(time.time() - t0), "s", flush=True)
