"""S-streams as unary counters: run [p, q, S^m, T0, T1, J] (T0, T1, J opaque) for m = 0..M and record the stuck front's
head atom and a normalised description of the front's spine and the next elements.  Looks for zero tests
(outcome changes between m = 0 and m >= 1) whose m >= 1 outcome contains a packed counter W.S^(m-1) or W.S^m."""
import sys, collections
import hm
T0, T1, J = hm.atom("T"), hm.atom("U"), hm.atom("J")
def describe(st):
    f = st[-1]; a, h = hm.spine(f)
    return hm.show(h), len(st)
def count_trailing_S(t):
    a, h = hm.spine(t)
    k = 0
    for x in reversed(a):
        if x == 0: k += 1
        else: break
    return k
if __name__ == "__main__":
    smax = int(sys.argv[1]); M = 7
    res = collections.Counter(); hits = []
    terms = [t for n in range(1, smax + 1) for t in hm.trees(n)]
    for p in terms:
        for q in terms:
            if hm.size(p) + hm.size(q) > smax + 1: continue
            outs = []
            for m in range(M + 1):
                st = [J, T1, T0] + [0] * m + [q, p]
                status, k = hm.run(st, 3000)
                if status != "stuck": outs.append(status); continue
                outs.append(hm.show(hm.head(st[-1])))
            key = tuple(outs)
            res[key] += 1
            changes = sum(1 for i in range(1, len(outs)) if outs[i] != outs[i-1])
            if changes >= 2 or (changes == 1 and outs[0] != outs[1]):
                hits.append((hm.show(p), hm.show(q), outs))
    for k, v in res.most_common(30): print(v, k)
    print("hits", len(hits))
    for h in hits[:60]: print(h)
