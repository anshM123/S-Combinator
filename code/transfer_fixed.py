"""Corrected transfer test (main agent): relevance closes under BOTH parts of a relevant product (opening b·c exposes c
as a spine argument). Checks the hypothesis 'every relevant slot is a normal form whenever it waits' over a window, for
the candidate counters and for tree calls."""
import sys, random
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from waiting_nf import is_nf, seq
def check_list(elems, N, stop=None):
    nid = [0]
    def new(e): nid[0] += 1; return (nid[0], e)
    stk = [new(e) for e in reversed(elems)]
    waited_nonnf = set(); opened = set(); parts = {}
    for n in range(N):
        if len(stk) < 3 or (stop is not None and stk[-1][1] == stop): break
        for sid, e in stk[:-3]:
            if not is_nf(e): waited_nonnf.add(sid)
        (ia, a) = stk.pop(); bsl = stk.pop(); csl = stk.pop(); opened.add(ia)
        ch, h = hc.spine(a)
        if h != 0: break
        p = new(hc.app(bsl[1], csl[1])); parts[p[0]] = (bsl[0], csl[0])
        stk.append(p); stk.append(csl); stk.extend(new(x) for x in reversed(ch))
    relevant = set(opened); changed = True
    while changed:
        changed = False
        for pp, (b, c) in parts.items():
            if pp in relevant:
                for q in (b, c):
                    if q not in relevant: relevant.add(q); changed = True
    return len(waited_nonnf & relevant)
for src in ("S(SS)S(S(S(SSS)))S", "S(S(SS))S(S(S(S(SS))))S", "SSS(SS)S(SS(SS))"):
    args, h = hc.spine(hc.from_tuple(parse(src)))
    print(f"{src}: relevant slots that waited as non-normal forms in 3000 steps: {check_list(args, 3000)}", flush=True)
X, Y = -1, -2; XY = hc.app(X, Y); bad = 0; tested = 0
L = hc.app(0, 0)
for k in (2, 3):
    L = hc.app(0, 0)
    for m in range(5):
        tested += 1; bad += check_list([L, X, Y, -3, -4, -5, -6], 10 ** 6, stop=XY) > 0; L = seq([L] * k)
random.seed(11); pool = [(hc.app(0, 0), 2)]
for it in range(200):
    k = random.randint(2, 4); As = [random.choice(pool) for _ in range(k)]
    T = sum(t for _, t in As) + k
    if T > 2000: continue
    C = seq([a for a, _ in As]); pool.append((C, T)); tested += 1
    bad += check_list([C, X, Y, -3, -4, -5, -6], 10 ** 6, stop=XY) > 0
print(f"tree calls: {tested} tested, {bad} violate the corrected hypothesis")
