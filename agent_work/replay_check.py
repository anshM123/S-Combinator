"""Replay relation test.  For real phase-2 proper (position-3) transfers with a SINGLE wrapper (V = w.y): phase 3 is
the generic run of w.q (q fresh: q = new live atom, p = frozen).  Does the phase-2 run pass through the list
args(w) ++ [w, y, x.y, r] (= the w.q run with q := w)?  If so, phase 3 replays phase 2 from there until the first
w-front of phase 2 / q-front of phase 3."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark(); ex = []
for D2 in data:
    lst = [Rr, Y, X, D2]; trace = []
    for t in range(1500):
        trace.append(tuple(lst))
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): hm.truncate(M0); continue
    V = lst[-3]
    if hm.R[V] != Y: st["multi-wrapper"] += 1; hm.truncate(M0); continue
    w = hm.L[V]
    args, h = hm.spine(w)
    target = tuple([Rr, hm.app(X, Y), Y, w] + list(reversed(args))) if h == 0 else None
    hit = target is not None and target in trace
    st["single-wrapper, passes through args(w)++[w,y,xy,r]" if hit else "single-wrapper, does not"] += 1
    if not hit and len(ex) < 6: ex.append((hm.show(D2), hm.show(V)))
    hm.truncate(M0)
print(st)
for e in ex: print("no replay:", e)
