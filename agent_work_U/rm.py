"""Right-spine machine RM: head machine; at a 2-list [c, d] emit c (it must normalise: checked with a budgeted
CBV normaliser) and continue with ch(d); at [c] continue with ch(c); [] ends.  usage as module."""
from dm import *
from cbv import nf_cbv
def rm_run(st, budget, nfbud=20000, maxout=10**9, record=None):
    """st: list front-at-end.  returns (status, steps, outputs list of (step, c))"""
    outs = []
    for t in range(budget):
        n = len(st)
        if n >= 3:
            a = st[-1]; args, h = spine(a)
            if h != 0: return ("stuck", t, outs)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(args))
        elif n == 2:
            c = st[-1]; d = st[-2]
            if nfbud is not None:
                r = nf_cbv(c, nfbud)
                if r is None: return ("leftdiv", t, outs)
            outs.append((t, c))
            if len(outs) >= maxout: return ("maxout", t, outs)
            args, h = spine(d)
            if h != 0: return ("stuck", t, outs)
            st.clear(); st.extend(reversed(args))
        elif n == 1:
            c = st[-1]; args, h = spine(c)
            if h != 0: return ("stuck", t, outs)
            st.clear(); st.extend(reversed(args))
        else:
            return ("end", t, outs)
    return ("budget", budget, outs)
if __name__ == "__main__":
    import sys
    t = parse(sys.argv[1]); st = list(reversed(spine(t)[0]))
    r = rm_run(st, int(sys.argv[2]))
    print(r[0], r[1], len(r[2]))
    for (s, c) in r[2][:int(sys.argv[3])]:
        print(s, size(c), show(c, maxlen=100))
