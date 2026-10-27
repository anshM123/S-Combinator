"""Finer phase-3 events on real phase-2 outputs (all wrappers, exhaustive <= N):
  CYp : a C-element glued onto a p'-HEADED Y-element
  CYy : a C-element glued onto the bare y
  ydown_target : what the bare y is glued onto (class/headedness)
  PonYnonbare  : a P'-element glued onto a Y-element other than the bare y"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def hd(t):
    h = hm.head(t)
    return "S" if h == 0 else hm.NAMES.get(h, "?")
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
tot = collections.Counter(); M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3": hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    st = [Rr, Y, X, D3]; ev = set()
    for t in range(1500):
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        a, b, c = st[-1], st[-2], st[-3]
        cb, cc = E.cls(b), E.cls(c)
        if cb == "C" and cc == "Y":
            ev.add("C onto Y, Y-head=" + ("bare y" if c == Y else hd(c)))
        if cb == "P" and cc == "Y" and c != Y: ev.add("P' onto non-bare Y (head %s)" % hd(c))
        if b == Y: ev.add("ydown onto %s-headed %s" % (hd(c), cc))
        hm.step(st)
    end = "stuck " + hd(st[-1]) if len(st) >= 3 else "hnf"
    for e in ev: tot[(e, end)] += 1
    tot["runs"] += 1
    hm.truncate(M0)
for k in sorted(tot, key=str): print(k, tot[k])
