"""R3 agent: random test of (S1) on ordered single-occurrence data (4..N leaves): for each proper single-wrapper
transfer glued in pattern beta, does phase 2 run c0 on (w, y) before the glue?  usage: s1rand.py SEED N COUNT"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import s1test, r3search as RS
hm = s1test.hm
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); M = int(sys.argv[3])
    st = collections.Counter(); ex = collections.defaultdict(list); M0 = hm.mark()
    for it in range(M):
        D = RS.rtree(random.randint(4, N), 1)
        if hm.head(D) != 0 or not RS.pg.ordered(D): hm.truncate(M0); continue
        r = s1test.info(D)
        if r is not None:
            k = r if r[0] == "beta" else (r[0],)
            st[k] += 1
            if len(ex[k]) < 2: ex[k].append(hm.show(D))
        hm.truncate(M0)
    for k in sorted(st, key=str): print(k, st[k], ex[k])
