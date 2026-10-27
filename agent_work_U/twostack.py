"""Two-stack DM search.  State h.(a.X).Y  (h closed code, a a closed 'stack symbol', X, Y opaque stack rests).
Run the DM; at every round end (descent) record the survivor if it contains X exactly once and Y exactly once and
has the form C.P.Q (head closed code C, spine [..., P, Q] with P containing X only, Q containing Y only).  Report the
transformation (P, Q) shapes reached, for every h <= NH leaves, a in SYMS.  usage: python twostack.py NH BUDGET MAXROUNDS"""
import sys
from dm import *
NH, BUDGET, MAXR = map(int, sys.argv[1:4])
X, Y = atom("X"), atom("Y")
SYMS = [parse(s) for s in ["S(SS)S", "S(SS)(SS)", "SSS", "S(SSS)S"]]
def occ(i, a):
    c = 0; st = [i]
    while st:
        j = st.pop()
        if j == a: c += 1
        elif j > 0: st.append(L[j]); st.append(R[j])
    return c
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
res = {}
for n in range(1, NH + 1):
    for h in trees(n):
        for a in SYMS:
            st = list(reversed(spine(h)[0] + [app(a, X), Y]))
            rounds = 0
            for t in range(BUDGET):
                m_ = len(st)
                if m_ >= 3:
                    f = st[-1]; args, hh = spine(f)
                    if hh != 0: break
                    st.pop(); b = st.pop(); c = st.pop()
                    st.append(app(b, c)); st.append(c); st.extend(reversed(args))
                elif m_ >= 1:
                    c = st[-1]; args, hh = spine(c)
                    rounds += 1
                    if occ(c, X) == 1 and occ(c, Y) == 1 and hh == 0 and len(args) >= 2:
                        P, Q = args[-2], args[-1]
                        if occ(P, X) == 1 and occ(Q, Y) == 1 and all(closed(z) for z in args[:-2]):
                            key = (show(P), show(Q))
                            if key not in res and (P != app(a, X) or Q != Y or rounds > 0):
                                res[key] = (show(h), show(a), rounds, show(c, maxlen=100))
                    if hh != 0 or rounds > MAXR: break
                    st.clear(); st.extend(reversed(args))
                else:
                    break
for k, v in sorted(res.items(), key=lambda kv: (len(kv[0][0]) + len(kv[0][1]))):
    print("P=%-25s Q=%-25s  h=%s a=%s round=%d surv=%s" % (k[0], k[1], v[0], v[1], v[2], v[3]))
print("distinct", len(res))
