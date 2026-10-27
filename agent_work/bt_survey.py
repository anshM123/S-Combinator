"""Survey: for closed S-terms T (n leaves), head-reduce T x1..xk (k opaque atoms) and record which variable ends at the
head (or hnf / budget).  Purpose: see which 'calling conventions' S-terms can have."""
import sys, collections
import hm
K = int(sys.argv[2]) if len(sys.argv) > 2 else 6
xs = [hm.atom("x%d" % (i + 1)) for i in range(K)]
idx = {x: i + 1 for i, x in enumerate(xs)}
def behave(T, budget=2000):
    args, h = hm.spine(T)
    st = list(reversed(args + xs))
    status, n = hm.run(st, budget)
    if status == "stuck":
        f = st[-1]
        a, hv = hm.spine(f)
        return ("var", idx.get(hv, hv), len(a), n), st
    return (status, None, None, n), st
if __name__ == "__main__":
    N = int(sys.argv[1])
    cnt = collections.Counter()
    for n in range(1, N + 1):
        for T in hm.trees(n):
            b, st = behave(T)
            cnt[(b[0], b[1])] += 1
    for k, v in sorted(cnt.items(), key=lambda kv: str(kv[0])):
        print(k, v)
