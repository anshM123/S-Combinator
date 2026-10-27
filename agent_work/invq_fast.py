"""Faster single-level invariant check with cached classes.  Reports: violations of ORD, INVQ, STEP, and counts of
(P,P,Y) steps (the case the hand proof does not cover)."""
import sys, random
import hm
P = hm.atom("p"); X = hm.atom("x"); Y = hm.atom("y"); Rr = hm.atom("r"); C = hm.atom("c1")
_cls = {}
def cls(t):
    if t in _cls: return _cls[t]
    if t == 0: r = "CL"
    elif t < 0: r = "Y" if t in (X, Y, Rr) else ("P" if t == P else "CL")
    else:
        a, b = cls(hm.L[t]), cls(hm.R[t])
        r = "Y" if "Y" in (a, b) else ("P" if "P" in (a, b) else "CL")
    _cls[t] = r; return r
def rand_term(n, frozen=False):
    if n == 1: return C if (frozen and random.random() < 0.08) else 0
    k = random.randint(1, n - 1)
    return hm.app(rand_term(k, frozen), rand_term(n - k, frozen))
def check(L):
    cl = [cls(e) for e in L]
    order = {"CL": 0, "P": 1, "Y": 2}
    for i in range(len(cl) - 1):
        if order[cl[i]] > order[cl[i + 1]]: return "ORD"
    ph_above = False
    # positions of p-headed P elements
    php = [i for i, e in enumerate(L) if cl[i] == "P" and hm.head(e) == P]
    lastphp = php[-1] if php else -1
    for i, e in enumerate(L):
        if cl[i] == "P" and hm.head(e) != P:
            if not (ph_above or lastphp > i): return "INVQ"
        if hm.head(e) == P: ph_above = True
    if len(L) >= 3 and cl[1] == "P" and cl[2] == "Y" and hm.head(L[1]) != P: return "STEP"
    return None
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2])
    M0 = hm.mark(); bad = {}; runs = steps = ppy_steps = 0
    for it in range(N):
        K = rand_term(random.randint(1, 16), frozen=(it % 2 == 1))
        if hm.head(K) != 0: hm.truncate(M0); _cls.clear(); continue
        a, _ = hm.spine(K)
        st = list(reversed(a + [P, Y, hm.app(X, Y), Rr]))
        runs += 1
        for s in range(400):
            L = list(reversed(st[-40:])) if len(st) > 40 else list(reversed(st))
            # only the top 40 elements are checked (deeper ones are untouched tape/junk)
            r = check(L if len(st) <= 40 else L)
            if r:
                bad.setdefault(r, (hm.show(K), s)); break
            if len(st) < 3: break
            if cls(st[-1]) == "P" and cls(st[-2]) == "P" and cls(st[-3]) == "Y" and hm.head(st[-1]) == 0: ppy_steps += 1
            if hm.step(st) < 0: break
            steps += 1
        hm.truncate(M0); _cls.clear()
    print("runs", runs, "steps", steps, "(P,P,Y) steps", ppy_steps, "violations", bad)
