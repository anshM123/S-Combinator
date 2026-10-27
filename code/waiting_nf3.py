"""Relevance-closed invariant (main agent): a slot is RELEVANT if it is opened, or if it is merged as b into a product
b·c whose slot is relevant (b's spine becomes the product's spine). Claim: in the head run of a tree call (atomic
x, y, tape) no relevant slot is ever a non-normal form while it waits at position >= 3. Then a parallel pass changes
only irrelevant (junk) material, so the parallel run opens the same shapes at the same times as the head run."""
import sys, random
sys.setrecursionlimit(1000000)
import hc
from waiting_nf import is_nf, seq
def check(C):
    X, Y = -1, -2; XY = hc.app(X, Y); nid = [0]
    def new(e): nid[0] += 1; return (nid[0], e)
    stk = [new(e) for e in (-6, -5, -4, -3, Y, X, C)]
    waited_nonnf = set(); opened = set(); prod_b = {}
    for n in range(10 ** 6):
        if stk[-1][1] == XY: break
        for sid, e in stk[:-3]:
            if not is_nf(e): waited_nonnf.add(sid)
        (ia, a) = stk.pop(); bsl = stk.pop(); csl = stk.pop(); opened.add(ia)
        args, h = hc.spine(a)
        p = new(hc.app(bsl[1], csl[1])); prod_b[p[0]] = bsl[0]
        stk.append(p); stk.append(csl); stk.extend(new(x) for x in reversed(args))
    relevant = set(opened); changed = True
    while changed:
        changed = False
        for p, b in prod_b.items():
            if p in relevant and b not in relevant: relevant.add(b); changed = True
    return len(waited_nonnf & relevant), len(relevant)
bad = 0; tested = 0
for k in (2, 3, 4):
    L = hc.app(0, 0)
    for m in range(6):
        b, r = check(L); tested += 1; bad += b > 0
        L = seq([L] * k)
random.seed(11); pool = [(hc.app(0, 0), 2)]
for it in range(300):
    k = random.randint(2, 4); As = [random.choice(pool) for _ in range(k)]
    T = sum(t for _, t in As) + k
    if T > 3000: continue
    C = seq([a for a, _ in As]); b, r = check(C); tested += 1; bad += b > 0
    pool.append((C, T))
print(f"{tested} tree calls: runs where a relevant slot waited as a non-normal form: {bad}")
