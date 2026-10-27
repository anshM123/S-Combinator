"""Joint distribution of (levels of the phase datum, number of wrappers of the proper position-3 handler) for
right-comb data over p with closed wrappers (exhaustive <= N, or random with frozen atoms in wrappers)."""
import sys, collections, random
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, ml_wrappers as MW
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
st = collections.Counter(); ex = {}; M0 = hm.mark()
def nw(V):
    n = 0; t = V
    while t != Y: n += 1; t = hm.R[t]
    return n
def go(D2):
    o2, V, _ = T3.phase(D2, 1500)
    if o2 == "proper3":
        k = len(MW.levels(D2)) - 1   # number of wrappers of D2 (levels L1..Lk)
        n = nw(V)
        st[(k, n)] += 1
        ex.setdefault((k, n), (hm.show(D2), hm.show(V)))
if sys.argv[1] == "ex":
    data = [D for D in c3.rcombs(int(sys.argv[2])) if hm.head(D) == 0]
    M0 = hm.mark()
    for D2 in data:
        go(D2); hm.truncate(M0)
else:
    random.seed(int(sys.argv[2])); Nr = int(sys.argv[3]); maxk = int(sys.argv[4]); ws = int(sys.argv[5])
    for n in range(1, ws + 1): hm.trees(n)
    M0 = hm.mark()
    for it in range(Nr):
        k = random.randint(2, maxk)
        t = P
        for i in range(k):
            d = 0 if random.random() < 0.2 else hm.trees(random.randint(1, ws))[0] if False else None
            n = random.randint(1, ws)
            trs = hm.trees(n)
            d = trs[random.randrange(len(trs))]
            if random.random() < 0.3:   # sprinkle a frozen atom into the wrapper
                d = hm.app(d, c3.FROZ[1])
            t = hm.app(d, t)
        if hm.head(t) == 0: go(t)
        hm.truncate(M0)
for key in sorted(st): print(key, st[key])
for key in sorted(ex): print("ex", key, ex[key])
# liveness census: a handler is DEAD if some wrapper is p-headed (FH) or its outermost wrapper is the bare S (YD)
if len(sys.argv) > 1 and sys.argv[-1] == "live":
    pass
