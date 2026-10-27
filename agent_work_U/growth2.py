"""Single-datum DM with an opaque base X: track the number of occurrences of X in round-end survivors and the number
of rounds before X is executed (stuck at an X-headed state).  Histogram of (max occurrences, rounds)."""
import sys, random, collections
from dm import *
SEED, NRUNS, MAXSYM, K, BUDGET = map(int, sys.argv[1:6])
random.seed(SEED)
X = atom("X")
syms = []
for n in range(1, MAXSYM + 1): syms += trees(n)
def occ(i, a):
    c = 0; st = [i]; seen = {}
    # count with multiplicity using memo on dag
    memo = {}
    def f(j):
        if j == a: return 1
        if j <= 0: return 0
        if j in memo: return memo[j]
        r = f(L[j]) + f(R[j]); memo[j] = r; return r
    return f(i)
hist = collections.Counter(); ex = {}
for run in range(NRUNS):
    m0 = mark()
    word = [random.choice(syms) for _ in range(K)]
    t = X
    for w in reversed(word): t = app(w, t)
    args, h = spine(t)
    st = list(reversed(args))
    maxo = 1; rounds = 0; outcome = "budget"
    for step in range(BUDGET):
        n = len(st)
        if n >= 3:
            a = st[-1]; aa, hh = spine(a)
            if hh != 0: outcome = "Xexec"; break
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        elif n >= 1:
            c = st[-1]; rounds += 1
            maxo = max(maxo, occ(c, X))
            aa, hh = spine(c)
            if hh != 0: outcome = "Xexec"; break
            st.clear(); st.extend(reversed(aa))
        else:
            outcome = "end"; break
    key = (outcome, min(maxo, 10), min(rounds, 20))
    hist[key] += 1
    if key not in ex: ex[key] = [show(w) for w in word]
    truncate(m0)
for k, v in sorted(hist.items(), key=lambda kv: -kv[1])[:30]:
    print(k, v, ex[k])
