"""Lazy parallel (ReplaceAll) evaluation (main agent, 2026-10-26).
P = one parallel pass (contract every outermost redex S x y z, enter nothing inside a contracted redex). Two facts give a
machine that only computes what reaches the head (Lemma LP-par, PROOF.md):
  P(S a_1 a_2 a_3 a_4 ⋯ a_m) = a_1 a_3 (a_2 a_3) P(a_4) ⋯ P(a_m)      (m ≥ 3)
  P(S a_1 ⋯ a_m) = S P(a_1) ⋯ P(a_m)                                 (m ≤ 2)
so the parallel run is the head machine on a list whose elements carry pending passes: an element that waited w passes is
P^w of what was pushed, and opening it needs the spine of P^w(x), i.e. w passes of x's own (lazy) parallel run.
Terms: S = 0, APP(x, y), DEL(x, k) = P^k(x) (k ≥ 1, x not a DEL); hash-consed. A stack entry (x, b) means P^(now − b)(x).
Usage: python lazy_par.py TERM N [CHECK]   (CHECK: compare the first CHECK opcodes with the direct capped computation)"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse

KIND = [0]; A = [0]; B = [0]; TAB = {}          # id 0 = S; kind 1 = APP(A, B); kind 2 = DEL(A, k = B)
def mk(kind, a, b):
    key = (kind, a, b); r = TAB.get(key)
    if r is None:
        r = len(KIND); KIND.append(kind); A.append(a); B.append(b); TAB[key] = r
    return r
def app(x, y): return mk(1, x, y)
NORMAL = set()                                   # opaque atoms (ids < 0) that are normal forms: P leaves them unchanged
ATOMS = {}                                       # variable letter -> atom id (symbolic lemmas only)
class Opaque(Exception):
    pass
def delay(x, k):
    if k == 0 or x == 0: return x
    if x < 0: return x if x in NORMAL else mk(2, x, k)    # a general atom ages: DEL(atom, k) = P^k(atom), unknown
    if KIND[x] == 2: return mk(2, A[x], B[x] + k)
    return mk(2, x, k)
def from_tuple(t):
    if t == "S": return 0
    if isinstance(t, str): return ATOMS.setdefault(t, -(len(ATOMS) + 1))
    return app(from_tuple(t[0]), from_tuple(t[1]))

STATE = {}                                       # base x -> (now, stack) of x's own lazy run (stack: top last)
MEMO = {}                                        # (x, k) -> argument list of P^k(x)
def plain_spine(x):
    """argument list of x when x is S or an APP chain whose head is S or a DEL"""
    args = []
    while x > 0 and KIND[x] == 1: args.append(B[x]); x = A[x]
    args.reverse()
    if x == 0: return args
    if x < 0 or A[x] < 0: raise Opaque(x)          # an opaque head (possibly aged) would have to be opened
    return force(A[x], B[x]) + args
def spine(x):
    if x < 0: raise Opaque(x)
    if KIND[x] == 2:
        if A[x] < 0: raise Opaque(x)
        return force(A[x], B[x])
    return plain_spine(x)

CANON = {}
def canon(x):
    """the same term with every pass carried out: DEL nodes remain only around general atoms (P^k(S a b) = S P^k(a) P^k(b),
    and an active P^k(x) is forced)"""
    if x <= 0: return x
    r = CANON.get(x)
    if r is not None: return r
    if KIND[x] == 1: r = app(canon(A[x]), canon(B[x]))
    elif A[x] < 0: r = x
    else:
        r = 0
        for a in force(A[x], B[x]): r = app(r, canon(a))
    CANON[x] = r; return r
NAMES = {}
def show(x, top=True):
    """print a canonical term (S, atoms by letter, aged atoms as x^k)"""
    if x == 0: return "S"
    if x < 0: return NAMES.get(x) or next((k for k, v in ATOMS.items() if v == x), f"a{-x}")
    if KIND[x] == 2: return show(A[x]) + "^" + str(B[x])
    f, y = A[x], B[x]
    ys = show(y, False)
    if y > 0 and KIND[y] == 1: ys = "(" + ys + ")"
    return show(f, False) + ys

def force(x, k):
    """argument list of P^k(x) (x not a DEL)"""
    r = MEMO.get((x, k))
    if r is not None: return r
    st = STATE.get(x)
    if st is None or st[0] > k:
        st = (0, [(e, 0) for e in reversed(plain_spine(x))])
    now, stk = st[0], list(st[1])
    while now < k:
        if len(stk) < 3:                          # head normal form: every element just waits
            now = k; break
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        v1, v2, v3 = delay(x1, now - b1), delay(x2, now - b2), delay(x3, now - b3)
        c = spine(v1)
        stk.append((app(v2, v3), now + 1)); stk.append((v3, now + 1))
        stk.extend((e, now + 1) for e in reversed(c))
        now += 1
    STATE[x] = (now, stk)
    r = [delay(e, k - b) for e, b in reversed(stk)]
    MEMO[(x, k)] = r
    return r

def par_ops(src, N):
    """opcode (spine length of the opened element) at each of the first N passes of the parallel run of src"""
    t = from_tuple(parse(src)); stk = [(e, 0) for e in reversed(plain_spine(t))]; ops = []
    for now in range(N):
        if len(stk) < 3: break
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        v1, v2, v3 = delay(x1, now - b1), delay(x2, now - b2), delay(x3, now - b3)
        c = spine(v1); ops.append(len(c))
        stk.append((app(v2, v3), now + 1)); stk.append((v3, now + 1))
        stk.extend((e, now + 1) for e in reversed(c))
    return ops

def reset():
    del KIND[1:]; del A[1:]; del B[1:]; TAB.clear(); STATE.clear(); MEMO.clear(); CANON.clear()

if __name__ == "__main__":
    import time
    src, N = sys.argv[1], int(sys.argv[2])
    CHECK = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    t0 = time.time(); ops = par_ops(src, N)
    print(f"{src}: {len(ops)} passes in {time.time() - t0:.1f}s, {len(KIND)} nodes, {len(MEMO)} forced lists")
    w = "".join(chr(48 + o) for o in ops); print(w[:400])
    if CHECK:
        import hc
        from par_vs_head import par_ops as direct, reset as hreset
        hreset(); d, why = direct(src, CHECK, 2000000)
        m = min(len(d), len(ops))
        print(f"direct capped computation: {len(d)} passes ({why}); lazy = direct on the first {m}: {d[:m] == ops[:m]}")
