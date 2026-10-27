"""Parity of numerals via a 2-code arrangement: run [N_n, x, y, J, K, L] (x, y closed, J, K, L opaque) for n = 1..NMAX
and look for outcomes (head atom of stuck front) that change more than once in n."""
import sys, collections
import hm
J1, J2, J3 = hm.atom("J"), hm.atom("K"), hm.atom("L")
SS = hm.parse("SS")
NUM = {}
def num(n):
    if n in NUM: return NUM[n]
    t = SS
    for _ in range(n - 1): t = hm.app(SS, t)
    NUM[n] = t; return t
if __name__ == "__main__":
    xmax = int(sys.argv[1]); ymax = int(sys.argv[2]); NMAX = 10; budget = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    X = [t for n in range(1, xmax + 1) for t in hm.trees(n)]
    Y = [t for n in range(1, ymax + 1) for t in hm.trees(n)]
    for n in range(1, NMAX + 1): num(n)
    M0 = hm.mark()
    cnt = collections.Counter(); hits = []
    for x in X:
        for y in Y:
            outs = []
            for n in range(1, NMAX + 1):
                st = [J3, J2, J1, y, x, num(n)]
                s, k = hm.run(st, budget)
                outs.append(hm.show(hm.head(st[-1])) if s == "stuck" else s[0])
                hm.truncate(M0)
            ch = sum(1 for i in range(1, NMAX) if outs[i] != outs[i - 1])
            cnt[min(ch, 3)] += 1
            if ch >= 2: hits.append((hm.show(x), hm.show(y), "".join(o[0] for o in outs)))
    print(cnt); print("hits", len(hits))
    for h in hits[:40]: print(h)
