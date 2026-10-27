"""Head-machine 'self-transformation' search: word W = S w1..wn E over symbols {A,B}, executed as [W, x, y | r]
(x, y, r opaque).  Run until an atom-headed front; look for a subterm of the final list of the form S w'1..w'm E with
w' over {A,B}; record w -> w' (the largest such word).  Report symbol sets whose map is defined on all words and is
neither identity nor a symbol-wise substitution.   usage: python selfword.py NA NB NE MAXLEN BUDGET"""
import sys, itertools
from dm import *
NA, NB, NE, MAXLEN, BUDGET = map(int, sys.argv[1:6])
def upto(n):
    out = []
    for k in range(1, n + 1): out += trees(k)
    return out
X, Y, Rr = atom("x"), atom("y"), atom("r")
words = []
for k in range(0, MAXLEN + 1): words += list(itertools.product((0, 1), repeat=k))
def decode(t, sym, E):
    args, h = spine(t)
    if h != 0 or not args or args[-1] != E: return None
    out = []
    for a in args[:-1]:
        if a == sym[0]: out.append(0)
        elif a == sym[1]: out.append(1)
        else: return None
    return tuple(out)
def subterms(lst):
    seen = set(); st = list(lst)
    while st:
        i = st.pop()
        if i <= 0 or i in seen: continue
        seen.add(i); st.append(L[i]); st.append(R[i])
    return seen
def run(sym, E, w):
    W = build(0, [sym[c] for c in w] + [E])
    st = [Rr, Y, X, W]
    for t in range(BUDGET):
        a = st[-1]; args, h = spine(a)
        if h != 0 or len(st) < 3: break
        st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(args))
    else:
        return None
    best = None
    for s in subterms(st):
        d = decode(s, sym, E)
        if d is not None and s != W and (best is None or len(d) > len(best)): best = d
    return best
cnt = 0; good = 0
for A in upto(NA):
    for B in upto(NB):
        if A == B: continue
        for E in upto(NE):
            cnt += 1
            m = mark(); fm = {}; ok = True
            for w in words:
                r = run((A, B), E, w)
                if r is None: ok = False; break
                fm[w] = r
            truncate(m)
            if not ok: continue
            good += 1
            ident = all(fm[w] == w for w in words)
            subst = all(fm[w] == tuple(x for c in w for x in fm[(c,)]) for w in words)
            if ident or subst: continue
            ex = ["%s->%s" % ("".join(map(str, w)), "".join(map(str, fm[w]))) for w in words if len(w) <= 3]
            print("A=%s B=%s E=%s | %s" % (show(A), show(B), show(E), " ".join(ex)), flush=True)
print("combos", cnt, "defined", good)
