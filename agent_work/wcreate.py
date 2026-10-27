"""For real single-wrapper phase-2 transfers V = w.y: how was w created, and how was it glued onto y?
  glue step: list [a, w, y, ...] -> args(a) ++ [y, w.y, ...]  (record a's class)
  creation of w: (alpha) glue [x0, b0, c0] with b0.c0 = w; (beta) released as an argument of an opened front."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark(); ex = {}
for D2 in data:
    lst = [Rr, Y, X, D2]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst))
        hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3]) and hm.R[lst[-3]] == Y):
        hm.truncate(M0); continue
    V = lst[-3]; w = hm.L[V]
    # find glue step (last step whose 2nd element is w and 3rd is y)
    glue = None; create = None
    for t, L in enumerate(hist):
        if len(L) >= 3 and L[-2] == w and L[-3] == Y: glue = t
    for t, L in enumerate(hist[:glue] if glue is not None else hist):
        a, b, c = L[-1], L[-2], L[-3]
        if hm.head(a) != 0: continue
        if hm.app(b, c) == w: create = ("alpha", t, "x0=S" if a == 0 else "x0!=S", "b0=S" if b == 0 else "b0!=S")
        args, _ = hm.spine(a)
        if w in args: create = ("beta", t, "args=%d" % len(args), "")
    if glue is None: st["glue not found"] += 1
    else:
        a = hist[glue][-1]
        ga = "glue front " + E.cls(a).replace("P", "P'")
        key = (create[0] if create else "initial", create[2] if create else "", create[3] if create else "",
               "glue right after creation" if create and glue == create[1] + 1 else "later glue", ga)
        st[key] += 1
        ex.setdefault(key, (hm.show(D2), hm.show(V)))
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
for k, v in ex.items(): print("ex", k, v)
