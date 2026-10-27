"""Tail chains of the big-step head-normalisation recursion (PROOF.md Lemma 2(b)).

H(S) = S;  H(t1 t2) = App(H(t1), t2);  App(S, v) = S v;  App(S p, v) = S p v;
App(S p q, v) = App(App(H(p), v), q v)   -- the last call is the tail call.
A tail chain is a maximal run of tail calls App(S p_i q_i, v_i) -> App(S p_{i+1} q_{i+1}, q_i v_i) with
S p_{i+1} q_{i+1} = App(H(p_i), v_i). By Lemma R + Lemma 15 a counterexample to Q10 has an infinite one.
For every M35-F term we record its longest tail chain and, per step, the arity of H(p_i):
1 = 'peel' (p_{i+1} is the component of H(p_i), q_{i+1} = v_i), 2 = 'refill', 0 = chain ends.
Usage: python tailchain.py NMAX
"""
import sys, collections
from opencount import cl, F, M, s
from symb import trees, show

sys.setrecursionlimit(1000000)

class Budget(Exception):
    pass

def H(t, ctx):
    if t == "S":
        return ()
    return App(H(t[0], ctx), t[1], ctx)

def App(h, v, ctx):
    if len(h) < 2:
        return h + (v,)
    steps = []
    while len(h) == 2:
        p, q = h
        hp = H(p, ctx)
        h2 = App(hp, v, ctx)
        steps.append((len(hp), cl(p), cl(q), cl(v)))
        ctx["work"] += 1
        if ctx["work"] > ctx["budget"]:
            raise Budget
        h, v = h2, (q, v)
    ctx["chains"].append(steps)
    return h + (v,)

def chains_of(t, budget=10**5):
    ctx = {"work": 0, "budget": budget, "chains": []}
    H(t, ctx)
    return ctx["chains"]

if __name__ == "__main__":
    NMAX = int(sys.argv[1])
    for n in range(4, NMAX + 1):
        lens = collections.Counter(); refills = collections.Counter(); longest = (0, None, None)
        for t in trees(n):
            if not F[cl(t)]:
                continue
            for ch in chains_of(t):
                L = len(ch); lens[L] += 1
                r = sum(1 for k in ch if k[0] == 2); refills[r] += 1
                if L > longest[0]:
                    longest = (L, show(t), "".join("ePR"[k[0]] for k in ch))
        print(f"n={n}: chain lengths {dict(sorted(lens.items()))}; refills per chain {dict(sorted(refills.items()))}")
        print(f"   longest {longest}", flush=True)
