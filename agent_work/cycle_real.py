"""Real single-wrapper case (b) (b0 != S): first buffer, buffer-cycle completion, outcome."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
MEMO = {}
def cls(t):
    r = MEMO.get(t)
    if r is None:
        a = tg.atoms(t)
        r = 3 if (a.get(X) or a.get(Y) or a.get(Rr)) else (2 if a.get(P) else (1 if a.get(C) else 0))
        MEMO[t] = r
    return r
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] != Y: hm.truncate(M0); MEMO.clear(); continue
    w = hm.L[V]
    if hm.head(w) != 0 or hm.L[w] == 0: hm.truncate(M0); MEMO.clear(); continue   # case (b): b0 != S
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    lst = [Rr, Y, X, D3]; buffers = set(); cyc = 0; firstbuf_front = None
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        a, b, c = lst[-1], lst[-2], lst[-3]
        if cls(b) == 1 and cls(c) == 2:
            buffers.add(hm.app(b, c))
            if firstbuf_front is None: firstbuf_front = "front args=%d" % len(hm.spine(a)[0])
        if a in buffers and cls(b) == 2 and cls(c) == 3: cyc += 1
        hm.step(lst)
    h = hm.head(lst[-1]) if len(lst) >= 3 else None
    out = "reexec" if h == C else ("p'-front pos3=" + ("bare y" if lst[-3] == Y else "other") if h == P else "other")
    st[("buffer" if buffers else "no buffer", firstbuf_front or "-", "cycles=%d" % cyc, out)] += 1
    hm.truncate(M0); MEMO.clear()
for k in sorted(st): print(k, st[k])
