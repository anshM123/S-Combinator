"""sizes of nf(a u_n) (CBV) for closed NF a <= NMAX leaves; report a whose size sequence is not eventually affine."""
import sys
from dm import *
from cbv import mk_apply, Budget
NMAX, NN, BUD = map(int, sys.argv[1:4])
U = [0]
for i in range(1, 2000): U.append(app(0, U[-1]))
def isnf(t):
    st = [t]
    while st:
        i = st.pop()
        if i <= 0: continue
        args, h = spine(i)
        if len(args) >= 3: return False
        st.extend(args)
    return True
seen = set()
for n in range(1, NMAX + 1):
    for a in trees(n):
        if not isnf(a): continue
        szs = []
        m = mark()
        for i in range(NN + 1):
            ap, cnt = mk_apply(BUD)
            try:
                r = ap(a, U[i]); szs.append(size(r))
            except (Budget, RecursionError):
                szs.append(None); break
        truncate(m)
        if None in szs: continue
        d2 = [szs[i+1] - 2*szs[i] + szs[i-1] for i in range(1, len(szs)-1)]
        tail = d2[4:]
        if any(x != 0 for x in tail):
            key = tuple(szs)
            if key in seen: continue
            seen.add(key)
            print(show(a), szs)
print("done")
