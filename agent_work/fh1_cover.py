"""Coverage of FH / FH1 / YD among real proper position-3 phase-2 handlers (exhaustive <= N):
  FH : some wrapper p-headed;  FH1: some wrapper has a p-headed FIRST spine argument;  YD: outermost wrapper = bare S."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3": hm.truncate(M0); continue
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    fh = any(hm.head(w) == P for w in ws)
    fh1 = any(hm.head(w) == 0 and hm.spine(w)[0] and hm.head(hm.spine(w)[0][0]) == P for w in ws)
    yd = ws[0] == 0
    key = "FH" if fh else ("FH1" if fh1 else ("YD" if yd else "open"))
    st[(key, "single" if len(ws) == 1 else "multi")] += 1
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
