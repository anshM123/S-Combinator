import sys
sys.path.insert(0, "../code")
from symb import spine, show, trees
from collections import Counter
K = int(sys.argv[1])
def run(Z, cap=80):
    stk = list(spine(Z)[1]) + ["u", "X", "Y"]
    for _ in range(cap):
        if len(stk) < 3: return None
        a = stk[0]; h, ch = spine(a)
        if h != "S": return stk
        b, c = stk[1], stk[2]
        stk = list(ch) + [c, (b, c)] + stk[3:]
    return None
cnt = Counter(); ex = {}
for n in range(1, K + 1):
    for Z in trees(n):
        st = run(Z)
        if not st: continue
        h, ch = spine(st[0])
        key = (h, show(ch[0]) if ch else None, show(st[1]) if not isinstance(st[1], str) else st[1])
        if h == "X":
            cnt[key] += 1; ex.setdefault(key, show(Z))
for k, v in cnt.most_common(30): print(k, v, ex[k])
