"""CBV functions on unary values u_n (u_0 = S, u_{n+1} = S u_n): for closed a (normal forms only, <= NMAX leaves),
compute nf(a u_n), n = 0..NN.  If every result is some u_k, print the map n -> k when it is not affine."""
import sys
from dm import *
from cbv import mk_apply, Budget
NMAX, NN, BUD = map(int, sys.argv[1:4])
U = [0]
for i in range(1, 2000): U.append(app(0, U[-1]))
Uid = {x: i for i, x in enumerate(U)}
def isnf(t):
    st = [t]
    while st:
        i = st.pop()
        if i <= 0: continue
        args, h = spine(i)
        if len(args) >= 3: return False
        st.extend(args)
    return True
found = {}
for n in range(1, NMAX + 1):
    for a in trees(n):
        if not isnf(a): continue
        ks = []
        for i in range(NN + 1):
            ap, cnt = mk_apply(BUD)
            try:
                r = ap(a, U[i])
            except (Budget, RecursionError):
                r = None
            ks.append(Uid.get(r) if r is not None else None)
            if ks[-1] is None: break
        if len(ks) == NN + 1 and None not in ks:
            d = set(ks[i] - ks[i - 1] for i in range(1, len(ks)))
            key = tuple(ks)
            if key not in found:
                found[key] = show(a)
for k, v in found.items():
    d = set(k[i] - k[i - 1] for i in range(1, len(k)))
    print(("AFFINE " if len(d) == 1 else "NONAFF ") + v, k)
