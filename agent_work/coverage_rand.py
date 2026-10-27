"""Combined coverage on RANDOM phase-2 data: D2 = K.(d2.(...(dk.p))) with K a random S-term (<= NK leaves) and
1-3 random wrappers (<= W leaves; with probability pf a wrapper gets an older frozen atom c2 attached somewhere)."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3
import coverage_all as CA
P = c3.P; F2 = c3.FROZ[1]
def rterm(n, pf):
    if n == 1: return F2 if random.random() < pf else 0
    k = random.randint(1, n - 1)
    return hm.app(rterm(k, pf), rterm(n - k, pf))
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); NK = int(sys.argv[3]); W = int(sys.argv[4]); pf = float(sys.argv[5])
st = collections.Counter(); M0 = hm.mark(); openex = []
for it in range(N):
    t = P
    for i in range(random.randint(1, 3)):
        t = hm.app(rterm(random.randint(1, W), pf), t)
    K = rterm(random.randint(1, NK), 0.0)
    D2 = hm.app(K, t)
    if hm.head(D2) == 0:
        r = CA.classify(D2)
        if r is not None:
            st[r] += 1
            if r[0] == "open" and len(openex) < 5: openex.append(hm.show(D2))
    hm.truncate(M0)
tot = sum(st.values())
for k in sorted(st): print(k, st[k])
print("total", tot, " covered", tot - sum(v for k, v in st.items() if k[0] == "open"))
for e in openex: print("open:", e)
