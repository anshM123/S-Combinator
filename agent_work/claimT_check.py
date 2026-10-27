"""Random check of Claim T and INV-Q on single-level runs (full lists):
 INVQ   : every non-p-headed P-element has a p-headed element above it or a p-headed P-element below it
 CLAIMT : if the P-region has exactly 2 elements, at least one is p-headed and every non-p-headed one has only
          p-headed P spine args
 STEP   : if the front is S-headed, 2nd in P and 3rd in Y then the 2nd is p-headed"""
import sys, random
import hm, invq_fast as F
def ph(e): return hm.head(e) == F.P
def check(L):
    cl = [F.cls(e) for e in L]
    seen_ph = False
    Pidx = [i for i in range(len(L)) if cl[i] == "P"]
    phP = [i for i in Pidx if ph(L[i])]
    lastphP = phP[-1] if phP else -1
    for i in range(len(L)):
        if cl[i] == "P" and not ph(L[i]) and not (seen_ph or lastphP > i): return "INVQ"
        if ph(L[i]): seen_ph = True
    if len(Pidx) == 2:
        es = [L[i] for i in Pidx]
        if not any(ph(e) for e in es): return "CLAIMT-noPH"
        for e in es:
            if not ph(e):
                args, _ = hm.spine(e)
                if any(F.cls(x) == "P" and not ph(x) for x in args): return "CLAIMT-Qarg"
    if len(L) >= 3 and hm.head(L[0]) == 0 and cl[1] == "P" and cl[2] == "Y" and not ph(L[1]): return "STEP"
    return None
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2])
    M0 = hm.mark(); bad = {}; runs = steps = 0
    for it in range(N):
        K = F.rand_term(random.randint(1, 16), frozen=(it % 2 == 1))
        if hm.head(K) != 0: hm.truncate(M0); F._cls.clear(); continue
        a, _ = hm.spine(K)
        st = list(reversed(a + [F.P, F.Y, hm.app(F.X, F.Y), F.Rr]))
        runs += 1
        for s in range(250):
            r = check(list(reversed(st)))
            if r: bad.setdefault(r, (hm.show(K), s)); break
            if len(st) < 3 or hm.step(st) < 0: break
            steps += 1
        hm.truncate(M0); F._cls.clear()
    print("runs", runs, "steps", steps, "violations", bad)
