"""Random Church-chain census: random S-headed data with one or two occurrences of p (and optionally an older
frozen atom), sizes up to N leaves; follow proper position-3 transfers; record chain lengths."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y = c3.P, c3.Y; F9 = c3.FROZ[6]
def rterm(n, holes):
    """random binary tree with n leaves; 'holes' leaves become p, others S or (rarely) the frozen atom c7"""
    leaves = [P] * holes + [0] * (n - holes)
    random.shuffle(leaves)
    leaves = [F9 if (x == 0 and random.random() < 0.05) else x for x in leaves]
    def build(lo, hi):
        if hi - lo == 1: return leaves[lo]
        k = random.randint(lo + 1, hi - 1)
        return hm.app(build(lo, k), build(k, hi))
    return build(0, n)
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); M = int(sys.argv[3])
st = collections.Counter(); M0 = hm.mark(); ex = {}
for it in range(M):
    n = random.randint(4, N)
    D = rterm(n, random.choice([1, 1, 1, 2]))
    if hm.head(D) != 0: hm.truncate(M0); continue
    ln = 0
    for ph in range(6):
        o, V, _ = T3.phase(D, 3000)
        if o != "proper3": break
        ln += 1
        D = tg.subst(tg.subst(V, P, c3.FROZ[ph]), Y, P)
    st["length %d" % ln] += 1
    if ln >= 2: ex.setdefault(ln, hm.show(D))
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("example datum after a chain of length", k, ":", v)
