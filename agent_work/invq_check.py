"""Random check of the single-level invariants.  Datum K.p (K random closed, possibly with frozen atoms), list
args(K) ++ [p, y, x.y, r].  Regions: CL = free of p,x,y,r; P = contains p, not x,y,r; Y = contains x,y or r.
Check at every step:
  ORD  : list = CL* ++ P* ++ Y*
  INVQ : every S-headed P-element has a p-headed element above it or a p-headed P-element below it
  STEP : whenever the step's 2nd element is in P and its 3rd element is in Y, the 2nd element is p-headed
  YSP  : no S-headed Y-element has an S-headed P-element among its spine args"""
import sys, random
import hm, transfer_graph as tg
P = hm.atom("p"); X = hm.atom("x"); Y = hm.atom("y"); Rr = hm.atom("r"); C = hm.atom("c1")
def cls(t):
    a = tg.atoms(t)
    if a.get(X) or a.get(Y) or a.get(Rr): return "Y"
    if a.get(P): return "P"
    return "CL"
def rand_term(n, frozen=False):
    if n == 1: return C if (frozen and random.random() < 0.08) else 0
    k = random.randint(1, n - 1)
    return hm.app(rand_term(k, frozen), rand_term(n - k, frozen))
def check(st):
    L = list(reversed(st))     # front first
    cl = [cls(e) for e in L]
    order = {"CL": 0, "P": 1, "Y": 2}
    if any(order[cl[i]] > order[cl[i + 1]] for i in range(len(cl) - 1)): return "ORD"
    for i, e in enumerate(L):
        if cl[i] == "P" and hm.head(e) == 0:
            above = any(hm.head(L[j]) == P for j in range(i))
            below = any(cl[j] == "P" and hm.head(L[j]) == P for j in range(i + 1, len(L)))
            if not (above or below): return "INVQ"
        if cl[i] == "Y" and hm.head(e) == 0:
            a, _ = hm.spine(e)
            if any(cls(s) == "P" and hm.head(s) == 0 for s in a): return "YSP"
    if len(L) >= 3 and cl[1] == "P" and cl[2] == "Y" and hm.head(L[1]) != P: return "STEP"
    return None
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2])
    M0 = hm.mark(); bad = {}; runs = 0; steps = 0
    for it in range(N):
        K = rand_term(random.randint(1, 18), frozen=(it % 2 == 1))
        if hm.head(K) != 0: hm.truncate(M0); continue
        a, _ = hm.spine(K)
        st = list(reversed(a + [P, Y, hm.app(X, Y), Rr]))
        runs += 1
        for s in range(600):
            r = check(st)
            if r:
                bad.setdefault(r, hm.show(K)); break
            if len(st) < 3 or hm.step(st) < 0: break
            steps += 1
        hm.truncate(M0)
    print("runs", runs, "steps checked", steps, "violations:", bad)
