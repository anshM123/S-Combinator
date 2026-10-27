"""Engine lemma test: do infinite head runs reach a configuration whose top prefix S e1..ek (k = 3, 4) is
syntactically a small hnf-free 'kernel' (M35 class bottom, at most KMAX leaves)?"""
import sys, collections
from verify_model import load
from symb import trees, spine, size, show
reps, F, M = load("../data/model35_hn.txt"); s = reps.index("S")
memo = {}
def cl(t):
    if t == "S": return s
    if t in memo: return memo[t]
    r = int(M[cl(t[0]), cl(t[1])]); memo[t] = r; return r
N = int(sys.argv[1]); KMAX = int(sys.argv[2]); STEPS = int(sys.argv[3])
kernels = set(t for n in range(1, KMAX + 1) for t in trees(n) if not F[cl(t)])
print(f"catalogue: {len(kernels)} bottom-class terms with <= {KMAX} leaves", flush=True)
hit = miss = 0; when = collections.Counter(); kern_used = collections.Counter(); misses = []
for n in range(8, N + 1):
    for t in trees(n):
        if F[cl(t)]: continue
        _, st = spine(t); st = list(st); found = None
        for step in range(STEPS):
            for k in (3, 4):
                if len(st) >= k:
                    pre = "S"
                    for e in st[:k]: pre = (pre, e)
                    if size(pre) <= KMAX and pre in kernels: found = (step, show(pre)); break
            if found or len(st) < 3: break
            a, b, c = st[0], st[1], st[2]
            _, ch = spine(a)
            st = list(ch) + [c, (b, c)] + st[3:]
        if found: hit += 1; when[min(found[0] // 10, 20)] += 1; kern_used[found[1]] += 1
        else: miss += 1; misses.append(show(t))
print(f"bottom-class terms 8..{N} leaves: kernel reached {hit}, not reached within {STEPS} steps {miss}")
print("kernels used:", kern_used.most_common(8))
print("examples without a kernel:", misses[:6])
