"""E7 (agent_work_RR): race-node-shaped junk of ReplaceAll runs and its NORMALISATION times.
Runs the exact lazy ReplaceAll machine (code/lazy_par.py) on TERM for N passes.  At each pass the new product
v2.v3 is pushed (a waiting element: it evolves on its own as long as it is not reopened).  For every product of the
race-node shape S A B (v2 = S A) record n_par(A), n_par(B) (direct passes, caps) and whether A, B are already normal.
Prints rows (pass, n_par(A), n_par(B), size) for products where both sides are non-normal processes that normalise.
Usage: python junk_nf.py TERM N [CAP]"""
import sys
sys.setrecursionlimit(1000000)
from rr_tools import LP, T as LT
from nf_scan import hc, step_fn
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 400
CONV = {}
def to_hc(x):
    """lazy_par term (canonical, no DEL) -> hc term"""
    if x == 0: return 0
    r = CONV.get(x)
    if r is None:
        r = hc.app(to_hc(LP.A[x]), to_hc(LP.B[x])); CONV[x] = r
    return r
PSTEP = step_fn()
def npar(t, cap=CAP):
    PSTEP = step_fn()
    for k in range(cap + 1):
        u = PSTEP(t)
        if u == t: return k
        t = u
        if len(hc.L) > 1500000: return "cap"
    return None
def hsize(t, memo={}):
    if t <= 0: return 1
    r = memo.get(t)
    if r is None: r = hsize(hc.L[t]) + hsize(hc.R[t]); memo[t] = r
    return r
src, N = sys.argv[1], int(sys.argv[2])
t = LT(src); stk = [(e, 0) for e in reversed(LP.plain_spine(t))]
rows = []; nrace = 0
for now in range(N):
    if len(stk) < 3: print("hnf at pass", now); break
    (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
    v1, v2, v3 = LP.delay(x1, now - b1), LP.delay(x2, now - b2), LP.delay(x3, now - b3)
    c = LP.spine(v1)
    prod = LP.app(v2, v3)
    stk.append((prod, now + 1)); stk.append((v3, now + 1)); stk.extend((e, now + 1) for e in reversed(c))
    # race shape: v2 = S A (spine of v2 has length 1 with head S)
    cv2 = LP.canon(v2)
    if cv2 > 0 and LP.KIND[cv2] == 1 and LP.A[cv2] == 0:
        nrace += 1
        del hc.L[1:]; del hc.R[1:]; hc.TAB.clear(); CONV.clear(); PSTEP = step_fn()
        A = to_hc(LP.B[cv2]); B = to_hc(LP.canon(v3))
        na, nb = npar(A), npar(B)
        if na not in (0, None, "cap") and nb not in (0, None, "cap"):
            rows.append((now, na, nb, hsize(A), hsize(B)))
    if len(LP.KIND) > 1500000: print("node cap at pass", now); break
print(f"{src}: {nrace} race-shaped products in {now + 1} passes; {len(rows)} with both sides non-normal and normalising")
for r in rows[:60]: print(r)
