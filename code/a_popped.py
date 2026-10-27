"""Is the accumulator A ever popped (as b or c) in generic iteration runs, and with what neighbours? (main agent)"""
import sys, collections
sys.setrecursionlimit(100000)
from symb import trees, show
import hc
from kind_profile import kind
NMAX, CAP = int(sys.argv[1]), int(sys.argv[2])
X, Z, A, J = -1, -2, -3, -4
stats = collections.Counter(); ex = collections.defaultdict(list)
for n in range(1, NMAX + 1):
    for t in trees(n):
        P = hc.from_tuple(t); stk = [-7, -6, -5, J, A, Z, X, P]
        for step in range(CAP):
            a = stk[-1]; args, h = hc.spine(a)
            if h != 0 or len(stk) < 4: break
            b, c = stk[-2], stk[-3]
            if b == A or c == A:
                role = "b" if b == A else "c"
                key = f"A popped as {role}: front kind {kind(a)}, other {kind(c if role == 'b' else b)}"
                stats[key] += 1
                if len(ex[key]) < 2: ex[key].append((show(t), step))
            stk.pop(); bb = stk.pop(); cc = stk.pop()
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
print(dict(stats) if stats else "A is never popped")
for k, v in ex.items(): print(" ", k, v)
