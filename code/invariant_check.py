"""Empirical check of the candidate no-accumulation invariant (main agent): in the generic iteration run
[P, X, Z, A, J | r], at every step, every control-free element (no X, Z, J) containing A other than A itself lies above
(nearer the front than) every element containing X. Counts violations over all bodies <= NMAX leaves."""
import sys
sys.setrecursionlimit(100000)
from symb import trees, show
import hc
NMAX, CAP = int(sys.argv[1]), int(sys.argv[2])
X, Z, A, J = -1, -2, -3, -4
memo = {}
def kind(i):
    """bitmask: 1 = contains X, 2 = contains Z, 4 = contains A, 8 = contains J"""
    if i in memo: return memo[i]
    if i == 0: k = 0
    elif i == X: k = 1
    elif i == Z: k = 2
    elif i == A: k = 4
    elif i == J: k = 8
    elif i < 0: k = 16
    else: k = kind(hc.L[i]) | kind(hc.R[i])
    memo[i] = k; return k
viol = 0; examples = []; steps_checked = 0
for n in range(1, NMAX + 1):
    for t in trees(n):
        P = hc.from_tuple(t); stk = [-7, -6, -5, J, A, Z, X, P]
        for step in range(CAP):
            lst = stk[::-1]
            firstX = next((i for i, e in enumerate(lst) if kind(e) & 1), None)
            if firstX is not None:
                bad = [i for i, e in enumerate(lst) if i > firstX and e != A and kind(e) == 4]
                if bad:
                    viol += 1
                    if len(examples) < 5: examples.append((show(t), step))
                    break
            steps_checked += 1
            a = stk[-1]; args, h = hc.spine(a)
            if h != 0 or len(stk) < 4: break
            stk.pop(); bb = stk.pop(); cc = stk.pop()
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    print(f"n <= {n}: steps checked {steps_checked}, bodies violating {viol}", flush=True)
print("examples:", examples)
