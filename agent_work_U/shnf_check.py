"""Sanity check of shnf_two_vars: for all closed M <= NMAX leaves, does M x y reach an S-headed hnf (list length <= 2
without an atom-headed front, within BUDGET steps)?  Compare with M in {S} u {S(comb j)}."""
import sys
from dm import *
NMAX, BUD = map(int, sys.argv[1:3])
X, Y = atom("x"), atom("y")
comb = [0]
for j in range(1, 40): comb.append(app(0, comb[-1]))
allowed = {0} | {app(0, c) for c in comb}
bad = 0; hits = 0; tot = 0; budget_out = 0
for n in range(1, NMAX + 1):
    for M in trees(n):
        tot += 1
        args, h = spine(M)
        st = list(reversed(args + [X, Y]))
        res = None
        for t in range(BUD):
            if len(st) <= 2: res = "shnf"; break
            a = st[-1]; aa, ah = spine(a)
            if ah != 0: res = "var"; break
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        if res is None:
            if len(st) <= 2: res = "shnf"
            else: budget_out += 1
        if res == "shnf":
            hits += 1
            if M not in allowed:
                bad += 1; print("COUNTEREXAMPLE", show(M))
print("terms", tot, "S-headed hnf", hits, "counterexamples", bad, "budget-outs", budget_out)
