"""BEKW Question 7, two pump sites (main agent, 2026-10-27): E a two-hole context, pumps P, Q; the chain refines the
P-site and the Q-site alternately: M_k = E[P^{ceil(k/2)}[S], Q^{floor(k/2)}[S]]. Each step replaces one S by P[S] or
Q[S], so the chain is a refinement chain. Prints chains with at least MINCH certified colour changes and no unknowns.
Usage: python q7_search2.py EMAX PMAX K [MINCH]"""
import sys
sys.setrecursionlimit(100000)
from q7_search import trees, count, put_hole, plug, colour, Budget, contexts, H

H2 = "K"


def two_hole(n):
    for t in trees(n):
        m = count(t)
        for i in range(m):
            for j in range(m):
                if i != j:
                    yield put2(t, i, j)


def put2(t, i, j, off=0):
    if t == "S":
        if off == i: return H
        if off == j: return H2
        return t
    k = count(t[0])
    return (put2(t[0], i, j, off), put2(t[1], i, j, off + k))


def plug2(C, u, v):
    if C == H: return u
    if C == H2: return v
    if C == "S": return "S"
    return (plug2(C[0], u, v), plug2(C[1], u, v))


if __name__ == "__main__":
    EMAX, PMAX, K = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    MINCH = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    pumps = [P for n in range(2, PMAX + 1) for P in contexts(n)]
    found = 0
    for ne in range(2, EMAX + 1):
        for E in two_hole(ne):
            for P in pumps:
                for Q in pumps:
                    u, v = "S", "S"
                    cols = []
                    for k in range(K + 1):
                        try:
                            cols.append(colour(plug2(E, u, v), 100000))
                        except Budget:
                            cols.append("?")
                        if k % 2 == 0: u = plug(P, u)
                        else: v = plug(Q, v)
                    s = "".join(cols)
                    ch = sum(1 for a, b in zip(s, s[1:]) if a != b)
                    if "?" not in s and ch >= MINCH:
                        found += 1
                        print(f"E={E} P={P} Q={Q}: {s} ({ch})", flush=True)
    print("found", found)
