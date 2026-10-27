"""Exhaustive search (terms with N leaves) for DM runs with many rounds; for each long run, print the sequence of
survivor sizes over the first rounds and the round-length sequence, to see whether the leftmost path is a simple
linear reload or something nested."""
import sys
from dm import *
N, BUD, MINR = map(int, sys.argv[1:4])
out = []
for t in trees(N):
    args, h = spine(t)
    m = mark()
    st = list(reversed(args)); rounds = 0; sizes = []; lens = []; last = 0
    for step in range(BUD):
        n = len(st)
        if n >= 3:
            a = st[-1]; aa, hh = spine(a)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        elif n >= 1:
            c = st[-1]; rounds += 1
            if len(sizes) < 200: sizes.append(size(c)); lens.append(step - last)
            last = step
            aa, hh = spine(c); st.clear(); st.extend(reversed(aa))
        else:
            break
    if rounds >= MINR:
        out.append((show(t), rounds, sizes[:60], lens[:60]))
    truncate(m)
print("terms with >=", MINR, "rounds:", len(out))
seen = set()
for o in out:
    key = tuple(o[2][:40])
    if key in seen: continue
    seen.add(key)
    print(o[0], o[1]); print("  sizes", o[2][:50]); print("  lens ", o[3][:50])
    if len(seen) >= 12: break
