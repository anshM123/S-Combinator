"""Where does the product x·y sit during a tree call's generic run? (main agent) Max position of any copy of x·y (as a
list element) before the return, over k-ary levels and random compositions."""
import sys, random
sys.setrecursionlimit(1000000)
import hc
from waiting_nf import seq
def maxpos(C):
    X, Y = -1, -2; XY = hc.app(X, Y); stk = [-6, -5, -4, -3, Y, X, C]; mp = -1
    for n in range(10 ** 6):
        if stk[-1] == XY: return mp
        for pos, e in enumerate(reversed(stk)):
            if e == XY: mp = max(mp, pos)
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return None
res = []
for k in (2, 3, 4):
    L = hc.app(0, 0)
    for m in range(5): res.append(maxpos(L)); L = seq([L] * k)
random.seed(11); pool = [(hc.app(0, 0), 2)]
for it in range(200):
    k = random.randint(2, 4); As = [random.choice(pool) for _ in range(k)]
    T = sum(t for _, t in As) + k
    if T > 2000: continue
    C = seq([a for a, _ in As]); res.append(maxpos(C)); pool.append((C, T))
import collections
print("max position of x·y before the return, over", len(res), "tree calls:", dict(collections.Counter(res)))
