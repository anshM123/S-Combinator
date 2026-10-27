"""Lemma AB (absorbing): in the generic run (regions CL* P* Y*, P = contains the live atom p, no x/y/r), once the
P-region has >= 3 elements it keeps >= 3 elements for ever; in particular no P-element is glued onto a Y-element
afterwards.  Check on phase-2 runs (all right combs <= N leaves, single and multi-level) and on phase-3 runs."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def isP(t):
    a = tg.atoms(t)
    return bool(a.get(P)) and not (a.get(X) or a.get(Y) or a.get(Rr))
def isY(t):
    a = tg.atoms(t)
    return bool(a.get(X) or a.get(Y) or a.get(Rr))
def run_check(D, st, steps=3000):
    lst = [Rr, Y, X, D]; was3 = False
    for s in range(steps):
        if len(lst) < 3: break
        nP = sum(1 for e in lst if isP(e))
        if was3 and nP < 3: st["DECREASE"] += 1; return
        if nP >= 3: was3 = True
        a, b, c = lst[-1], lst[-2], lst[-3]
        if hm.head(a) != 0: break
        if was3 and isP(b) and isY(c): st["GLUE after 3"] += 1; return
        hm.step(lst)
    st["ok-reached3" if was3 else "ok-never3"] += 1
if __name__ == "__main__":
    N = int(sys.argv[1]); st2 = collections.Counter(); st3 = collections.Counter()
    data = c3.rcombs(N); M0 = hm.mark()
    for D in data:
        run_check(D, st2)
        r, Vs = c3.phase(D, 3000)
        if r == "proper":
            for V in Vs:
                run_check(tg.subst(tg.subst(V, P, C), Y, P), st3)
        hm.truncate(M0)
    print("phase 2:", st2); print("phase 3:", st3)
