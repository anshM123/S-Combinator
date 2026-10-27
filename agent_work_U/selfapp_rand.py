"""Random self-application hunt: random closed X with lo..hi leaves; terms X X, X X S, S X X, X (S X); leftmost walks
<= 300 nodes.  Candidates: a flag-0 walk that does not end, or a flag-1 walk that ends at S."""
import sys, random, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
NODES = 300
def walk(u):
    for j in range(NODES):
        if u == 0: return "S", j
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        st = list(reversed(spine(u)[0])); k = 0; bud = max(3000, 20 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", j
        u = st[-1]
        if size(u) > 200000: return "huge", j
    return "long", NODES
from collections import Counter
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); lo, hi = int(sys.argv[3]), int(sys.argv[4])
def rtree(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rtree(k), rtree(n - k))
stat = Counter(); t0 = time.time()
for it in range(N):
    if time.time() - t0 > 2400: break
    m = mark()
    X = rtree(random.randint(lo, hi))
    for name, t in (("XX", app(X, X)), ("XXS", app(app(X, X), 0)), ("SXX", app(app(0, X), X)), ("X(SX)", app(X, app(0, X)))):
        c = cls(t)
        if MFl[c[1]] == 0: stat[(name, "noHNF")] += 1; continue
        w, j = walk(t)
        stat[(name, w, LFl[c[0]])] += 1
        if (w in ("long", "huge") and LFl[c[0]] == 0) or (w == "S" and LFl[c[0]] == 1):
            print("CANDIDATE", name, w, j, show(t), c, flush=True)
    truncate(m); clear_cache(m)
print(it + 1, "X sampled", round(time.time() - t0), "s"); print(sorted(stat.items()))
