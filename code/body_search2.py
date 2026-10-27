"""Accumulator bodies, generalised target (main agent). From [P, X, Z, A, J | r] (atoms), the run must hand control back
to the loop: the front element has head X and first argument Z, i.e. X·Z·w_1·…·w_k (k >= 0); the next iteration's
accumulator is w_1 if k >= 1, else the element at position 2. Success: that accumulator is a term over A and S other
than A itself (a transformed accumulator), and r is never popped. Also lists accumulators over A, J, S (near misses)."""
import sys, collections
sys.setrecursionlimit(100000)
from symb import trees, show
import hc
NMAX, CAP = int(sys.argv[1]), int(sys.argv[2])
X, Z, A, J = -1, -2, -3, -4
def over(i, allowed):
    if i == 0 or i in allowed: return True
    if i < 0: return False
    return over(hc.L[i], allowed) and over(hc.R[i], allowed)
def has(i, a):
    if i == a: return True
    if i <= 0: return False
    return has(hc.L[i], a) or has(hc.R[i], a)
def fshow(i):
    names = {A: "A", J: "J", 0: "S"}
    if i in names: return names[i]
    l, r = hc.L[i], hc.R[i]
    return fshow(l) + (("(" + fshow(r) + ")") if r > 0 else fshow(r))
found = collections.defaultdict(list); near = collections.defaultdict(list); returned = 0
for n in range(1, NMAX + 1):
    for t in trees(n):
        P = hc.from_tuple(t)
        stk = [-7, -6, -5, J, A, Z, X, P]; floor = 3; acc = None
        for step in range(CAP):
            a = stk[-1]
            args, h = hc.spine(a)
            if h == X:
                if args and args[0] == Z:
                    acc = args[1] if len(args) >= 2 else (stk[-3] if len(stk) >= 3 else None)
                break
            if h != 0 or len(stk) < 3: break
            stk.pop(); bb = stk.pop(); cc = stk.pop()
            if len(stk) < floor: acc = None; break
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
        if acc is None or len(stk) < floor: continue
        returned += 1
        if acc != A and over(acc, {A}) and has(acc, A): found[fshow(acc)].append((show(t), step))
        elif acc != A and over(acc, {A, J}) and has(acc, A): near[fshow(acc)].append((show(t), step))
    print(f"n <= {n}: bodies returning to the loop {returned}; transformed accumulators {sum(len(v) for v in found.values())}; "
          f"near misses {sum(len(v) for v in near.values())}", flush=True)
for f, L in sorted(found.items(), key=lambda kv: (len(kv[0]), kv[0]))[:20]: print(f"  f(A) = {f:28s} {len(L)} bodies, e.g. {L[:2]}")
for f, L in sorted(near.items(), key=lambda kv: (len(kv[0]), kv[0]))[:10]: print(f"  near: {f:28s} {len(L)} bodies, e.g. {L[:2]}")
