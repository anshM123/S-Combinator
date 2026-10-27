"""Detailed leftmost walks for chosen terms: for every computed node print its spine (elements shown), class, and the
survivor; mark which spine elements get EXECUTED (reach the front as data) during the round."""
import sys
from dm import *
from classes import cls, MFl
def round_detail(u, bud=100000):
    args, h = spine(u)
    ids = set(args)
    st = list(reversed(args)); executed = []
    for k in range(bud):
        if len(st) <= 2: return st[-1], executed
        a = st[-1]
        if a in ids and a not in executed: executed.append(a)
        aa, hh = spine(a)
        st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
    return None, executed
for s in sys.argv[1:]:
    t = parse(s); u = t
    print("=== walk of", s, cls(t))
    for j in range(40):
        args, h = spine(u)
        if len(args) == 0: print("   leaf S"); break
        if len(args) <= 2:
            print("   d", cls(u), show(u, maxlen=80)); u = args[0]; continue
        if MFl[cls(u)[1]] == 0: print("   BOT", show(u, maxlen=80)); break
        surv, ex = round_detail(u)
        print("   c", cls(u), "[" + " | ".join(show(a, maxlen=30) for a in args) + "]", " executed spine elems:",
              [args.index(e) for e in ex])
        if surv is None: print("   cap"); break
        u = surv
