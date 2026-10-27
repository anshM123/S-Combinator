"""R3 agent: do DANGEROUS single-wrapper y-combs ever occur in phase-2 lists (not only as transferred handlers)?
A term w.y (w free of x, y, r, w = b0.c0 with b0, c0 S-headed or b0 = S) is 'dangerous' if its V-run (the next
phase of w.y, renamed) makes a proper transfer.  We scan every element and every subterm of every list of every
phase-2 run (until its end) and test each distinct w.y once.  usage: danger.py N | danger.py t NK WK NT"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y, X, Rr, C = CL.P, CL.Y, CL.X, CL.Rr, CL.C
def subterms(t, acc):
    stack = [t]
    while stack:
        u = stack.pop()
        if u in acc or u <= 0: continue
        acc.add(u); stack.append(hm.L[u]); stack.append(hm.R[u])
def main(argv):
    data = list(CL.family(argv))
    st = collections.Counter(); ex = []; M0 = hm.mark()
    for D in data:
        lst = [Rr, Y, X, D]; seen = set(); end = "budget"
        for t in range(400):
            for e in lst: subterms(e, seen)
            if len(lst) < 3: end = "hnf"; break
            h = hm.head(lst[-1])
            if h != 0:
                end = "transfer" if (h == P and T3.S3.proper(lst[-3])) else "other"
                break
            hm.step(lst)
        for u in seen:
            if hm.R[u] != Y: continue
            w = hm.L[u]
            if w <= 0 or hm.head(w) != 0: continue
            a = tg.atoms(w)
            if a.get(Y) or a.get(X) or a.get(Rr) or not a.get(P): continue
            o3 = CL.phase3(u)[0]
            st[(end, o3)] += 1
            if o3 == "p'-front PROPER" and len(ex) < 8: ex.append((hm.show(D), hm.show(u), end))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
    for e in ex: print("DANGEROUS w.y in a phase-2 run:", e)
if __name__ == "__main__":
    main(sys.argv[1:])
