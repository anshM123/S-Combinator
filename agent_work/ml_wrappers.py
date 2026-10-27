"""Multi-level phase-2 data (right combs over p with closed wrappers, k >= 2 levels).  For each proper transfer,
classify the innermost wrapper w (the one applied directly to y):
  PH : p-headed
  LP : level-prefixed: stripping right arguments from w reaches exactly a level L_j (j >= 2) of the datum
  SLP: S-headed, every P spine arg (containing p) is PH or LP
  other"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y = c3.P, c3.Y
def levels(D):
    Ls = []; t = D
    while t != P:
        Ls.append(t); t = hm.R[t]
    Ls.append(P)
    return Ls        # Ls[0] = D = L1, Ls[1] = L2, ..., last = p
def is_LP(w, Ls):
    t = w
    while True:
        if t in Ls[1:]: return True
        if t <= 0: return False
        t = hm.L[t]
def classify(w, Ls):
    if hm.head(w) == P: return "PH"
    if is_LP(w, Ls): return "LP"
    if hm.head(w) == 0:
        args, _ = hm.spine(w)
        pargs = [a for a in args if P in tg.atoms(a)]
        if all(hm.head(a) == P or is_LP(a, Ls) for a in pargs): return "SLP"
    return "other"
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = collections.defaultdict(list)
    data = [D for D in c3.rcombs(N) if hm.R[D] != P]       # k >= 2 levels
    M0 = hm.mark()
    for D in data:
        r, Vs = c3.phase(D, 4000)
        if r == "proper":
            Ls = levels(D)
            for V in Vs:
                ws = []; t = V
                while t != Y: ws.append(hm.L[t]); t = hm.R[t]
                k = classify(ws[-1], Ls)
                st[k] += 1
                if len(ex[k]) < 4: ex[k].append((hm.show(D), hm.show(V)[:60]))
        hm.truncate(M0)
    print("multi-level data:", len(data), st)
    for k, v in ex.items(): print(k, v)
