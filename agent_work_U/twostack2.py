"""Random exploration of two-stack DM configurations with CONCRETE stack tops (symbols execute) and opaque bottoms X, Y.
State c.A.B, A = a1.(...(ak.X)), B = b1.(...(bm.Y)).  At each round end, if the survivor contains X once and Y once,
try to find two disjoint subterms that are right combs over X and over Y with closed wrappers ('clean stacks').
Record survivors where BOTH clean stacks exist and at least one differs from its initial version while X/Y occur once.
usage: python twostack2.py SEED NRUNS MAXSYM MAXC K BUDGET"""
import sys, random, collections
from dm import *
SEED, NRUNS, MAXSYM, MAXC, K, BUDGET = map(int, sys.argv[1:7])
random.seed(SEED)
X, Y = atom("X"), atom("Y")
syms = [t for n in range(1, MAXSYM + 1) for t in trees(n)]
ctrls = [t for n in range(1, MAXC + 1) for t in trees(n)]
def occ(i, a):
    memo = {}
    def f(j):
        if j == a: return 1
        if j <= 0: return 0
        if j in memo: return memo[j]
        r = f(L[j]) + f(R[j]); memo[j] = r; return r
    return f(i)
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
def comb(t, base):
    ws = []
    while t != base:
        if t <= 0 or not closed(L[t]): return None
        ws.append(L[t]); t = R[t]
    return ws
def find_comb(t, base):
    """find the maximal subterm that is a clean right comb over base (closest to root along the path to base)"""
    best = None; st = [t]
    while st:
        j = st.pop()
        if j <= 0: continue
        if occ(j, base) == 0: continue
        w = comb(j, base)
        if w is not None:
            if best is None or len(w) > len(best[1]): best = (j, w)
            continue
        st.append(L[j]); st.append(R[j])
    return best
stats = collections.Counter(); shown = 0
for run in range(NRUNS):
    m0 = mark()
    A0 = [random.choice(syms) for _ in range(random.randint(1, K))]
    B0 = [random.choice(syms) for _ in range(random.randint(1, K))]
    A = X
    for w in reversed(A0): A = app(w, A)
    B = Y
    for w in reversed(B0): B = app(w, B)
    c = random.choice(ctrls)
    st = list(reversed(spine(c)[0] + [A, B]))
    rounds = 0
    for step in range(BUDGET):
        n = len(st)
        if n >= 3:
            a = st[-1]; aa, h = spine(a)
            if h != 0: stats["stuck"] += 1; break
            st.pop(); b = st.pop(); cc = st.pop()
            st.append(app(b, cc)); st.append(cc); st.extend(reversed(aa))
        elif n >= 1:
            s = st[-1]; rounds += 1
            ox, oy = occ(s, X), occ(s, Y)
            if ox == 1 and oy == 1:
                ca, cb = find_comb(s, X), find_comb(s, Y)
                if ca and cb:
                    changed = (ca[1] != A0 or cb[1] != B0)
                    stats["both-clean"] += 1
                    if changed and len(ca[1]) + len(cb[1]) > 0:
                        stats["both-clean-changed"] += 1
                        if shown < 30:
                            shown += 1
                            print("c=%s A=%s B=%s round=%d -> A'=%s B'=%s surv=%s" % (show(c), [show(w) for w in A0], [show(w) for w in B0],
                                  rounds, [show(w) for w in ca[1]], [show(w) for w in cb[1]], show(s, maxlen=90)), flush=True)
            elif ox == 0 or oy == 0:
                stats["lost"] += 1; break
            aa, h = spine(s)
            if h != 0: stats["stuck-desc"] += 1; break
            st.clear(); st.extend(reversed(aa))
        else:
            stats["end"] += 1; break
    truncate(m0)
print(dict(stats))
