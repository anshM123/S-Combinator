"""DM rounds WITH FUEL: closed code C, data, then a closed fuel element at the bottom.  usage:
python fuelcat.py NMAX K FUEL BUDGET   (K = number of data atoms, FUEL = closed fuel term, e.g. S)
Records skeletons of data-holding survivors of the first round (no data execution)."""
import sys, collections
from dm import *
NMAX, K = int(sys.argv[1]), int(sys.argv[2]); FUEL = parse(sys.argv[3]); BUD = int(sys.argv[4])
xs = [atom("x"), atom("y"), atom("z")][:K]
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
names = {xs[i]: "xyz"[i] for i in range(K)}
def skel(i):
    if i in names: return names[i]
    if closed(i): return "c"
    args, h = spine(i)
    s = names.get(h, "S")
    return s + "".join("(" + skel(a) + ")" for a in args)
cnt = collections.Counter(); ex = {}
for n in range(1, NMAX + 1):
    for C in trees(n):
        args, h = spine(C)
        st = list(reversed(args + xs + [FUEL]))
        surv = None
        for t in range(BUD):
            m_ = len(st)
            if m_ >= 3:
                a = st[-1]; aa, ah = spine(a)
                if ah != 0: break
                st.pop(); b = st.pop(); c = st.pop()
                st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
            else:
                if m_ >= 1: surv = st[-1]
                break
        if surv is None or closed(surv): continue
        key = skel(surv)
        cnt[key] += 1
        if key not in ex: ex[key] = show(C)
for key, v in sorted(cnt.items(), key=lambda kv: (len(kv[0]), kv[0]))[:50]:
    print("%-60s" % key, v, "e.g.", ex[key])
print("distinct", len(cnt))
