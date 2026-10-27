import sys, collections
import hm, transfer_graph as tg
smax = int(sys.argv[1])
edges = {}; kinds = collections.Counter()
M0 = None
for n in range(2, smax + 1):
    for G in tg.contexts(n):
        e = tg.edge(G)
        if e and e[0] == "clean": edges[G] = e[1]
print("clean edges", len(edges))
proper = {G: H for G, H in edges.items() if H != tg.HOLE}
print("proper edges", len(proper))
targets = collections.Counter(hm.show(H) for H in proper.values())
print("distinct proper targets", len(targets))
# for each proper target H, compute its edge (any size)
bad = []
for H in set(proper.values()):
    e = tg.edge(H)
    kinds[e[0] if e else "none"] += 1
    if e and e[0] == "clean" and e[1] != tg.HOLE:
        bad.append((hm.show(H), hm.show(e[1])))
print("targets' own edges:", kinds)
print("proper->proper chains:", bad[:20])
# shape of targets: right comb of closed terms over the hole?
def rcomb(H):
    while H != tg.HOLE:
        if H <= 0: return False
        l, r = hm.L[H], hm.R[H]
        if tg.atoms(l): return False
        H = r
    return True
print("all targets right combs:", all(rcomb(H) for H in proper.values()))
