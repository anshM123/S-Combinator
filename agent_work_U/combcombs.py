"""DM behaviour of S D_a D_b D_c (D_k = k nested S over S): end of leftmost path? size growth? number of rounds."""
import sys
from dm import *
D = [0]
for k in range(1, 30): D.append(app(0, D[-1]))
AMAX = int(sys.argv[1]); BUD = int(sys.argv[2])
for a in range(AMAX + 1):
    for b in range(AMAX + 1):
        for c in range(AMAX + 1):
            m = mark()
            st = [D[c], D[b], D[a]]
            rounds = 0; res = "budget"
            for t in range(BUD):
                n = len(st)
                if n >= 3:
                    x = st[-1]; args, h = spine(x)
                    st.pop(); y = st.pop(); z = st.pop()
                    st.append(app(y, z)); st.append(z); st.extend(reversed(args))
                elif n >= 1:
                    x = st[-1]; args, h = spine(x); st.clear(); st.extend(reversed(args)); rounds += 1
                else:
                    res = "end@%d" % t; break
            print(a, b, c, res, "rounds", rounds, "len", len(st), "maxsize", max([size(x) for x in st] or [0]))
            truncate(m)
