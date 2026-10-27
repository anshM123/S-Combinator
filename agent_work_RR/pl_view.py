"""View Theorem PL's parallel loop: list below the window, C_i named.  D = S(SS), L = S D, C_1 = L, C_{i+1} = L C_i."""
import sys
from rr_tools import LP, T as LT
src = "S(S(S(S(SSS)(SSS))))SS"
t = LT(src); stk = [(e, 0) for e in reversed(LP.plain_spine(t))]
S = 0; D = LP.app(0, LP.app(0, 0)); L = LP.app(0, D); C = {L: "C1"}; x = L
for i in range(2, 80): x = LP.app(L, x); C[x] = f"C{i}"
NM = {0: "S", D: "D", L: "L"}
def nm(x, depth=0):
    if x in C: return C[x]
    if x in NM: return NM[x]
    if x <= 0: return "?"
    if depth > 6: return "…"
    a, b = nm(LP.A[x], depth + 1), nm(LP.B[x], depth + 1)
    return f"{a}" + (f"({b})" if LP.KIND[LP.B[x]] == 1 and LP.B[x] not in C and LP.B[x] not in NM else b if b in ("S",) else f"·{b}" if False else f"({b})")
N = int(sys.argv[1]) if len(sys.argv) > 1 else 120
for now in range(N):
    (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
    v1, v2, v3 = LP.delay(x1, now - b1), LP.delay(x2, now - b2), LP.delay(x3, now - b3)
    c = LP.spine(v1)
    stk.append((LP.app(v2, v3), now + 1)); stk.append((v3, now + 1)); stk.extend((e, now + 1) for e in reversed(c))
vals = [LP.canon(LP.delay(e, N - b)) for e, b in reversed(stk)]
print("pass", N, "list length", len(vals))
for i, v in enumerate(vals[:40]): print(i + 1, nm(v)[:150])
