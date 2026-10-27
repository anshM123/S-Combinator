"""Word rounds in the DM: state list [P, w1..wk, E] with w_i in {A, B}.  Run the DM until the list again has the form
[P, w'..., E] (w' over {A,B}) and record w -> w'.  Report (P, A, B, E) whose map is defined on all test words and is
NOT a symbol-wise substitution (i.e. some output depends on more than the symbol itself) and not identity.
usage: python wordround.py NP NA NB NE MAXLEN BUDGET"""
import sys, itertools
from dm import *
NP, NA, NB, NE, MAXLEN, BUDGET = map(int, sys.argv[1:7])
def upto(n):
    out = []
    for k in range(1, n + 1): out += trees(k)
    return out
Ps, As, Bs, Es = upto(NP), upto(NA), upto(NB), upto(NE)
words = []
for k in range(0, MAXLEN + 1):
    words += list(itertools.product((0, 1), repeat=k))
def run(P, sym, E, w):
    st = [E] + [sym[c] for c in reversed(w)] + [P]
    first = True
    for t in range(BUDGET):
        n = len(st)
        if n >= 3:
            a = st[-1]; args, h = spine(a)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(args))
        elif n >= 1:
            c = st[-1]; args, h = spine(c); st.clear(); st.extend(reversed(args))
        else:
            return None
        if len(st) >= 2 and st[0] == E and st[-1] == P:
            mid = st[1:-1]
            ok = True; out = []
            for x in reversed(mid):
                if x == sym[0]: out.append(0)
                elif x == sym[1]: out.append(1)
                else: ok = False; break
            if ok: return tuple(out), t + 1
    return None
nint = 0; ntot = 0; ngood = 0
for P in Ps:
    for A in As:
        for B in Bs:
            if A == B: continue
            sym = (A, B)
            for E in Es:
                ntot += 1
                m = mark()
                fm = {}
                good = True
                for w in words:
                    r = run(P, sym, E, w)
                    if r is None: good = False; break
                    fm[w] = r[0]
                truncate(m)
                if not good: continue
                ident = all(fm[w] == w for w in words)
                # symbol-wise substitution test: f(w) == concat f((c,)) for all w
                subst = all(fm[w] == tuple(x for c in w for x in fm[(c,)]) for w in words)
                if ident or subst:
                    if ngood < 15: print("trivial", show(P), show(A), show(B), show(E), "ident" if ident else "subst", fm[(0,)], fm[(1,)], fm[(0,1)], flush=True)
                    ngood += 1
                    continue
                nint += 1
                ex = ["%s->%s" % ("".join(map(str, w)), "".join(map(str, fm[w]))) for w in words if len(w) <= 3]
                print("P=%s A=%s B=%s E=%s | %s" % (show(P), show(A), show(B), show(E), " ".join(ex)), flush=True)
print("total", ntot, "good-trivial", ngood, "interesting", nint)
