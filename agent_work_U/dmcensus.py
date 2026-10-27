"""DM census on random terms: fraction with long leftmost paths and the growth profile of survivor sizes."""
import sys, random, collections
from dm import *
SEED, N, LEAVES, BUD = map(int, sys.argv[1:5])
random.seed(SEED)
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rand_term(k), rand_term(n - k))
hist = collections.Counter(); keep = []
for it in range(N):
    m = mark()
    t = rand_term(LEAVES)
    args, h = spine(t)
    st = list(reversed(args)); rounds = 0; sizes = []
    status = "budget"
    for step in range(BUD):
        n = len(st)
        if n >= 3:
            a = st[-1]; aa, hh = spine(a)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        elif n >= 1:
            c = st[-1]; rounds += 1
            if rounds <= 400: sizes.append(size(c))
            aa, hh = spine(c); st.clear(); st.extend(reversed(aa))
        else:
            status = "end"; break
    key = (status, "r>=100" if rounds >= 100 else ("r>=10" if rounds >= 10 else "r<10"))
    hist[key] += 1
    if rounds >= 100: keep.append((show(t), rounds, sizes[:60]))
    truncate(m)
print(dict(hist))
for k in keep[:12]: print(k[0], k[1], k[2][:40])
