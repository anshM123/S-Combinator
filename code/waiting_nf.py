"""Are all waiting elements (positions >= 3) of a tree call's head run normal forms? (main agent)
Tree calls: k-ary levels (k = 2..4, m <= 5) and random compositions; atomic x, y, tape. A term is a normal form iff no
subterm has head S with >= 3 arguments. Report the first violation, with its position and shape."""
import sys, random
sys.setrecursionlimit(1000000)
import hc
nf_memo = {}
def is_nf(i):
    if i <= 0: return True
    r = nf_memo.get(i)
    if r is not None: return r
    args, h = hc.spine(i)
    r = not (h == 0 and len(args) >= 3) and all(is_nf(a) for a in args)
    nf_memo[i] = r; return r
def seq(As):
    t = hc.app(As[-1], 0)
    for A in reversed(As[:-1]): t = hc.app(hc.app(0, A), t)
    return hc.app(0, t)
def check(C):
    X, Y = -1, -2; XY = hc.app(X, Y); stk = [-6, -5, -4, -3, Y, X, C]; worst = None
    for n in range(10 ** 6):
        if stk[-1] == XY: return n, None
        for pos, e in enumerate(reversed(stk[:-3])):
            if not is_nf(e): return n, (pos + 3, len(hc.spine(e)[0]))
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); args, h = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return None, "no return"
def _main():
  pass
if __name__ == "__main__":
    viol = 0; tested = 0
    for k in (2, 3, 4):
        L = hc.app(0, 0)
        for m in range(6):
            n, v = check(L); tested += 1
            if v: viol += 1; print(f"k={k} m={m}: waiting non-normal-form at step {n}: (position, root spine) = {v}")
            L = seq([L] * k)
    random.seed(11); pool = [(hc.app(0, 0), 2)]
    for it in range(300):
        k = random.randint(2, 4); As = [random.choice(pool) for _ in range(k)]
        T = sum(t for _, t in As) + k
        if T > 3000: continue
        C = seq([a for a, _ in As]); n, v = check(C); tested += 1
        if v: viol += 1; print(f"random call T={T}: waiting non-normal-form at step {n}: {v}") if viol <= 5 else None
        pool.append((C, T))
    print(f"{tested} tree calls checked; runs with a waiting non-normal form: {viol}")
