"""Minimal linear recurrence (linear complexity) of parallel-evaluation size sequences via Berlekamp–Massey over GF(p)
(main agent). Sizes are computed with the memoised parallel step (parallel_eval.step_fn) and saved to data/.
An inhomogeneous recurrence of order k is a homogeneous one of order k + 1, so the reported L bounds both."""
import sys, json, time
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn, size
def bm(seq, p):
    C, B = [1], [1]; L, m, b = 0, 1, 1
    for n in range(len(seq)):
        d = seq[n] % p
        for i in range(1, L + 1): d = (d + C[i] * seq[n - i]) % p
        if d == 0: m += 1; continue
        T = C[:]; coef = d * pow(b, p - 2, p) % p
        C = C + [0] * (len(B) + m - len(C))
        for i in range(len(B)): C[i + m] = (C[i + m] - coef * B[i]) % p
        if 2 * L <= n: L, B, b, m = n + 1 - L, T, d, 1
        else: m += 1
    return L
if __name__ == "__main__":
    src, N, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    t = hc.from_tuple(parse(src)); s = [size(t)]; t0 = time.time()
    for n in range(N):
        t = step_fn()(t); s.append(size(t))
    json.dump(s, open(out, "w"))
    print(f"{src}: {len(s)} sizes in {time.time() - t0:.0f}s (saved {out})")
    for p in (1_000_000_007, 998_244_353, 2_147_483_647):
        for start in (0, 20, 40):
            tail = s[start:]
            print(f"  p={p} from n={start}: linear complexity L = {bm(tail, p)} of {len(tail)} terms")
