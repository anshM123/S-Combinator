"""Coverage of FHL (some wrapper's leftmost first-argument path reaches p through S-headed terms with >= 1 argument;
includes FH and FH1) and YD among real proper position-3 handlers."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def lp_reaches_p(t):
    while True:
        h = hm.head(t)
        if h == P: return True
        if h != 0: return False
        args, _ = hm.spine(t)
        if not args: return False
        t = args[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3": hm.truncate(M0); continue
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    fhl = any(lp_reaches_p(w) for w in ws)
    key = "FHL" if fhl else ("YD" if ws[0] == 0 else ("replay a/b" if (len(ws) == 1 and hm.L[ws[0]] == 0) else "open"))
    st[(key, "single" if len(ws) == 1 else "multi")] += 1
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
