"""Necessary condition for the size-weighted ranking certificate of Q10: no non-bottom configuration [x,y,z|R] with
R o rho_{yz} == R (that would force W(z,R) >= W(z,R) + W(yz,R))."""
from verify_model import load
reps, F, M = load("../data/model35_hn.txt"); n = len(reps); s = reps.index("S")
ident = tuple(range(n))
gens = {c: tuple(int(M[x, c]) for x in range(n)) for c in range(n)}
mon = {ident}; frontier = [ident]
while frontier:
    new = []
    for g in frontier:
        for c, h in gens.items():
            comp = tuple(h[g[x]] for x in range(n))
            if comp not in mon: mon.add(comp); new.append(comp)
    frontier = new
mon = list(mon)
def compose(lam, rho):  # first rho, then lam : x -> lam(rho(x))
    return tuple(lam[rho[x]] for x in range(n))
bad = []
for lam in mon:
    for y in range(n):
        for z in range(n):
            yz = int(M[y, z])
            if compose(lam, gens[yz]) != lam: continue
            # is some configuration [x, y, z | R] with this R non-bottom?
            xs = [x for x in range(n) if F[lam[int(M[int(M[x, z]), yz])]]]
            if xs: bad.append((y, z, lam, xs[:3]))
print("fixed points lam o rho_yz == lam in non-bottom configurations:", len(bad))
for y, z, lam, xs in bad[:5]:
    print("  y", reps[y], " z", reps[z], " yz", reps[int(M[y,z])], " example x", [reps[x] for x in xs])
