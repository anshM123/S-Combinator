"""Anatomy of infinite head runs (M35 bottom class): list length growth and the recurring top elements."""
import sys, collections
from verify_model import load
from symb import trees, show, spine
reps, F, M = load("../data/model35_hn.txt"); s = reps.index("S")
memo = {}
def cl(t):
    if t == "S": return s
    if t in memo: return memo[t]
    r = int(M[cl(t[0]), cl(t[1])]); memo[t] = r; return r
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
STEPS = 300
growth = collections.Counter(); tops = collections.Counter(); total = 0
for n in range(8, N + 1):
    for t in trees(n):
        if F[cl(t)]: continue
        total += 1
        h, args = spine(t)
        st = list(args)
        lens = []
        heads = []
        for step in range(STEPS):
            if len(st) < 3: break
            a, b, c = st[0], st[1], st[2]
            ha, ch = spine(a)
            heads.append(a)
            st = list(ch) + [c, (b, c)] + st[3:]
            lens.append(len(st))
            if len(st) > 5000: break
        g = "grows" if lens and lens[-1] > 50 else ("bounded" if lens and max(lens) < 30 else "mid")
        growth[g] += 1
        for a in heads[-60:]:
            if isinstance(a, tuple) and len(show(a)) <= 12: tops[show(a)] += 1
print("bottom-class terms with 8..%d leaves: %d" % (N, total), dict(growth))
print("most frequent small opened elements late in the runs:", tops.most_common(12))
