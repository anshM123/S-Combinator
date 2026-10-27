"""print the successive leftmost-path states (survivors) of a DM run: size and shape."""
import sys
from dm import *
def run_rounds(lst, budget, maxr=60, every=1):
    st = list(reversed(lst)); r = 0; out = []
    for t in range(budget):
        n = len(st)
        if n >= 3:
            a = st[-1]; args, h = spine(a)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(args))
        elif n >= 1:
            c = st[-1]; args, h = spine(c); st.clear(); st.extend(reversed(args))
            out.append((t, c)); r += 1
            if r >= maxr: break
        else:
            out.append((t, None)); break
    return out
if __name__ == "__main__":
    lst = [parse(s) for s in sys.argv[1].split(",")]
    for t, c in run_rounds(lst, int(sys.argv[2]), int(sys.argv[3])):
        print(t, "END" if c is None else "%d  %s" % (size(c), show(c, maxlen=150)))
