"""Print the full DM trace (all head-machine lists) of leftmost walks, to read off mechanisms."""
import sys
from dm import *
from classes import cls
def walk(s, maxnodes=30, maxsteps=200, width=150):
    u = parse(s)
    print("=== ", s, cls(u))
    for j in range(maxnodes):
        args, h = spine(u)
        if len(args) == 0: print("  leaf S"); return
        if len(args) <= 2:
            print("  struct", cls(u), show(u, maxlen=width)); u = args[0]; continue
        print("  NODE", cls(u), show(u, maxlen=width))
        st = list(reversed(args)); k = 0
        while len(st) > 2 and k < maxsteps:
            print("     [" + " | ".join(show(e, maxlen=40) for e in reversed(st)) + "]")
            a = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
        if len(st) > 2: print("  ... no hnf within", maxsteps); return
        print("     [" + " | ".join(show(e, maxlen=40) for e in reversed(st)) + "]  -> survivor")
        u = st[-1]
for s in sys.argv[1:]: walk(s)
