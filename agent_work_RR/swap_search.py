"""Search (agent_work_RR): closed S-terms Z (<= K leaves) such that the head run of [Z, u, X, Y] (u, X, Y opaque) stops
with X at the front and u directly below it (a 'swap with junk', allowed by Lemma 10 only with a second copy of X
somewhere).  Prints Z and the stopped list."""
import sys
sys.path.insert(0, "../code")
from symb import parse, spine, build, show, trees
K = int(sys.argv[1])
def run(Z, cap=60):
    stk = list(spine(Z)[1]) + ["u", "X", "Y"]
    for _ in range(cap):
        if len(stk) < 3: return None
        a = stk[0]; h, ch = spine(a)
        if h != "S": return stk
        b, c = stk[1], stk[2]
        stk = list(ch) + [c, (b, c)] + stk[3:]
    return None
for n in range(1, K + 1):
    for Z in trees(n):
        st = run(Z)
        if st and st[0] == "X" and len(st) > 1 and st[1] == "u":
            print(show(Z), "->", [show(e) if not isinstance(e, str) else e for e in st[:5]])
