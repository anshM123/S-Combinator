"""CBV iteration x_{k+1} = nf(f x_k) for closed NF f, x0 (<= NF, NX leaves).  Report pairs whose size sequence
(first K terms, all defined) has a non-eventually-constant second difference AND is not geometric."""
import sys
from dm import *
from cbv import mk_apply, Budget
NF_, NX, K, BUD = map(int, sys.argv[1:5])
def isnf(t):
    st = [t]
    while st:
        i = st.pop()
        if i <= 0: continue
        args, h = spine(i)
        if len(args) >= 3: return False
        st.extend(args)
    return True
def nfs(n):
    out = []
    for k in range(1, n + 1): out += [t for t in trees(k) if isnf(t)]
    return out
F = nfs(NF_); XS = nfs(NX)
seen = set(); cnt = 0
for f in F:
    for x0 in XS:
        m = mark()
        x = x0; szs = [size(x)]
        ok = True
        for k in range(K):
            ap, c = mk_apply(BUD)
            try:
                x = ap(f, x)
            except (Budget, RecursionError):
                ok = False; break
            szs.append(size(x))
            if szs[-1] > 200000: break
        truncate(m)
        if not ok or len(szs) < 8: continue
        d1 = [szs[i+1] - szs[i] for i in range(len(szs) - 1)]
        d2 = [d1[i+1] - d1[i] for i in range(len(d1) - 1)]
        ratios = set()
        geo = all(d1[i] > 0 and d1[i+1] == 2 * d1[i] for i in range(3, len(d1) - 1))
        if len(set(d2[3:])) > 1 and not geo:
            key = tuple(d1[:10])
            if key in seen: continue
            seen.add(key); cnt += 1
            if cnt <= 25: print(show(f), show(x0), szs)
print("count", cnt)
