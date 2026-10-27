"""Random checks for a W2 invariant.  Lists C ++ [X, Y] with random closed C; run until stuck/budget.
Check at every step: (A) the bottom is atom-headed; (B) at every 3-list [a, U, B], U is atom-headed or closed;
(C) the topmost data element (first element containing an atom) is atom-headed."""
import sys, random
from dm import *
SEED, NRUNS, MAXLEN, MAXLEAF, BUD = map(int, sys.argv[1:6])
random.seed(SEED)
X, Y = atom("X"), atom("Y")
def has_atom(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return True
        if j > 0: st.append(L[j]); st.append(R[j])
    return False
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rand_term(k), rand_term(n - k))
viol = {"A": 0, "B": 0, "C": 0}; steps = 0; ex = {}
for run in range(NRUNS):
    m0 = mark()
    C = [rand_term(random.randint(1, MAXLEAF)) for _ in range(random.randint(1, MAXLEN))]
    st = [Y, X] + list(reversed(C))      # front at end
    init = [show(c) for c in C]
    for t in range(BUD):
        if len(st) < 3: break
        a = st[-1]; aa, h = spine(a)
        if h != 0: break
        st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        steps += 1
        if head(st[0]) == 0:
            viol["A"] += 1; ex.setdefault("A", (init, t))
        if len(st) == 3:
            U = st[1]
            if has_atom(U) and head(U) == 0:
                viol["B"] += 1; ex.setdefault("B", (init, t))
        for e in reversed(st):
            if has_atom(e):
                if head(e) == 0: viol["C"] += 1; ex.setdefault("C", (init, t))
                break
    truncate(m0)
print("steps", steps, "violations", viol)
for k, v in ex.items(): print(k, v)
