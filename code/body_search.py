"""Accumulator bodies for numeral loops (main agent).
Inside the loop (Theorem N) each iteration starts from [P, X, Z, A, J | r] with X = m̄·P the loop continuation, Z the
final continuation, A the accumulator (the old v2) and J junk (the old v1·v2). A body P is useful if the generic run
(X, Z, A, J, r atoms) returns to the loop: the front becomes X·Z, with r untouched, and the element two below the front
(which becomes the next iteration's accumulator) is a term f(A) built from A and S only. Report all f found.
Usage: python body_search.py NMAX CAP"""
import sys, collections
sys.setrecursionlimit(100000)
from symb import trees, show
import hc
NMAX, CAP = int(sys.argv[1]), int(sys.argv[2])
X, Z, A, J = -1, -2, -3, -4
XZ = hc.app(X, Z)
def only_A_and_S(i):
    if i == 0 or i == A: return True
    if i < 0: return False
    return only_A_and_S(hc.L[i]) and only_A_and_S(hc.R[i])
def no_control(i):
    """term containing A, built from A, J and S only (no X, Z)"""
    if i == 0 or i == A or i == J: return True
    if i < 0: return False
    return no_control(hc.L[i]) and no_control(hc.R[i])
def has_A(i):
    if i == A: return True
    if i <= 0: return False
    return has_A(hc.L[i]) or has_A(hc.R[i])
def fshow(i):
    if i == A: return "A"
    if i == 0: return "S"
    if i == J: return "J"
    l, r = hc.L[i], hc.R[i]
    return fshow(l) + (("(" + fshow(r) + ")") if r > 0 else fshow(r))
found = collections.defaultdict(list); near = collections.defaultdict(list)
for n in range(1, NMAX + 1):
    for t in trees(n):
        P = hc.from_tuple(t)
        stk = [-7, -6, -5, J, A, Z, X, P]; floor = 3; ok = False
        for step in range(CAP):
            a = stk[-1]
            if a == XZ:
                ok = len(stk) >= 3; break
            args, h = hc.spine(a)
            if h != 0 or len(stk) < 3: break
            stk.pop(); bb = stk.pop(); cc = stk.pop()
            if len(stk) < floor: break
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
        if ok and len(stk) >= floor + 3:
            acc = stk[-3]
            if only_A_and_S(acc): found[fshow(acc)].append((show(t), step))
            elif no_control(acc) and has_A(acc): near[fshow(acc)].append((show(t), step))
for f, L in sorted(found.items(), key=lambda kv: (len(kv[0]), kv[0])):
    print(f"f(A) = {f:24s} {len(L):5d} bodies, e.g. {L[:3]}")

print("near misses (A with junk J, no control):")
for f, L in sorted(near.items(), key=lambda kv: (len(kv[0]), kv[0]))[:20]:
    print(f"  f = {f:30s} {len(L):5d} bodies, e.g. {L[:2]}")
