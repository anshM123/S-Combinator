"""print the DM run of a state given as a list of terms (front first).  usage: python trace.py "P" "w1" ... -- steps"""
import sys
from dm import *
def trace(lst, steps, every=False, maxshow=8):
    st = list(reversed(lst))
    for t in range(steps):
        n = len(st)
        if every or n < 3:
            print("%4d len=%d  %s" % (t, n, " | ".join(show(x, maxlen=60) for x in reversed(st[-maxshow:]))) + (" ..." if n > maxshow else ""))
        if n >= 3:
            a = st[-1]; args, h = spine(a)
            if h != 0: print("STUCK"); return
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(args))
        elif n >= 1:
            c = st[-1]; args, h = spine(c)
            if h != 0: print("STUCK at", show(c)); return
            st.clear(); st.extend(reversed(args))
        else:
            print("END"); return
if __name__ == "__main__":
    args = sys.argv[1:]
    k = args.index("--")
    lst = [parse(s) for s in args[:k]]
    trace(lst, int(args[k + 1]), every=(len(args) > k + 2))
