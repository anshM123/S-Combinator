"""Is x -> nf(b x) (CBV normal form) a nontrivial transducer on string encodings?
enc(e) = E, enc(0w) = S enc(w), enc(1w) = S P enc(w)  (P, E normal forms).  For each b (normal form <= NB leaves) and
(P, E) from a small list, compute r_w = nf(b enc(w)) for all w of length <= MAXLEN; look for a fixed address
(path of L/R moves of depth <= 3) at which every r_w holds enc(f(w)) for a string f(w); report non-identity f."""
import sys, itertools
from dm import *
from cbv import mk_apply, Budget
NB, MAXLEN, BUD = map(int, sys.argv[1:4])
def isnf(t):
    st = [t]
    while st:
        i = st.pop()
        if i <= 0: continue
        args, h = spine(i)
        if len(args) >= 3: return False
        st.extend(args)
    return True
PE = [(parse("SS"), parse("S")), (parse("SS"), parse("SSS")), (parse("S(SS)"), parse("S")), (parse("SSS"), parse("S(SS)"))]
words = [w for k in range(MAXLEN + 1) for w in itertools.product((0, 1), repeat=k)]
def enc(w, P, E):
    t = E
    for c in reversed(w):
        t = app(0, t) if c == 0 else app(app(0, P), t)
    return t
def dec(t, P, E):
    out = []
    while t != E:
        if t <= 0: return None
        if L[t] == 0: out.append(0); t = R[t]; continue
        l = L[t]
        if l > 0 and L[l] == 0 and R[l] == P: out.append(1); t = R[t]; continue
        return None
    return tuple(out)
def at(t, path):
    for d in path:
        if t <= 0: return None
        t = L[t] if d == 0 else R[t]
    return t
paths = [()] + [p for k in range(1, 4) for p in itertools.product((0, 1), repeat=k)]
bs = [t for n in range(1, NB + 1) for t in trees(n) if isnf(t)]
found = 0
for (P, E) in PE:
    encs = {w: enc(w, P, E) for w in words}
    for b in bs:
        m = mark()
        res = {}
        ok = True
        for w in words:
            ap, c = mk_apply(BUD)
            try:
                res[w] = ap(b, encs[w])
            except (Budget, RecursionError):
                ok = False; break
        if ok:
            for p in paths:
                fm = {}
                for w in words:
                    s = at(res[w], p)
                    d = dec(s, P, E) if s is not None else None
                    if d is None: break
                    fm[w] = d
                else:
                    if any(fm[w] != w for w in words):
                        found += 1
                        print("P=%s E=%s b=%s path=%s : %s" % (show(P), show(E), show(b), p,
                              " ".join("%s>%s" % ("".join(map(str, w)), "".join(map(str, fm[w]))) for w in words if len(w) <= 2)), flush=True)
        truncate(m)
print("found", found)
