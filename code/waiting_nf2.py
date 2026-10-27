"""Refined invariant (main agent): in the head run of a tree call (atomic x, y, tape), is every element that is LATER
OPENED a normal form whenever it waits at position >= 3? Slots carry identities (an element keeps its identity when it
moves as c; b·c and the spine arguments of an opened element are new slots)."""
import sys, random
sys.setrecursionlimit(1000000)
import hc
from waiting_nf import is_nf, seq
def check(C):
    X, Y = -1, -2; XY = hc.app(X, Y); nid = [0]
    def new(e): nid[0] += 1; return (nid[0], e)
    stk = [new(e) for e in (-6, -5, -4, -3, Y, X, C)]
    waited_nonnf = set(); opened = set()
    for n in range(10 ** 6):
        if stk[-1][1] == XY: break
        for sid, e in stk[:-3]:
            if not is_nf(e): waited_nonnf.add(sid)
        (ia, a) = stk.pop(); bsl = stk.pop(); csl = stk.pop(); opened.add(ia)
        args, h = hc.spine(a)
        stk.append(new(hc.app(bsl[1], csl[1]))); stk.append(csl); stk.extend(new(x) for x in reversed(args))
    return len(waited_nonnf & opened), len(waited_nonnf)
bad = 0; tested = 0; nonnf_total = 0
for k in (2, 3, 4):
    L = hc.app(0, 0)
    for m in range(6):
        b, t = check(L); tested += 1; bad += b > 0; nonnf_total += t
        L = seq([L] * k)
random.seed(11); pool = [(hc.app(0, 0), 2)]
for it in range(300):
    k = random.randint(2, 4); As = [random.choice(pool) for _ in range(k)]
    T = sum(t for _, t in As) + k
    if T > 3000: continue
    C = seq([a for a, _ in As]); b, t = check(C); tested += 1; bad += b > 0; nonnf_total += t
    pool.append((C, T))
print(f"{tested} tree calls: runs where a later-opened element waited as a non-normal form: {bad}; "
      f"waiting non-normal-form slots in total (all junk if bad = 0): {nonnf_total}")
