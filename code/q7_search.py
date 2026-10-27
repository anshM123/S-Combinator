"""BEKW Question 7 (colour change puzzle) search (main agent, 2026-10-27). A pumping family E[P^j[S]] is a refinement
chain (replace the innermost S by P[S]). Colour of a term: green = has a normal form (= terminating, Theorem T),
red = no normal form. Red is certified when some Böhm-tree node reached has M35 class bottom (Theorem A); green is
certified by computing the normal form. Reports families whose colour changes at least MINCH times for j = 0..J.
Usage: python q7_search.py EMAX PMAX J [MINCH]"""
import sys, itertools
sys.setrecursionlimit(100000)
from verify_model import load

reps, F, T = load("../data/model35_hn.txt")
BOT = [k for k in range(35) if not F[k]][0]

H = "H"  # hole marker


def trees(n):
    """all binary trees with n leaves over {S}"""
    if n == 1:
        yield "S"; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k):
                yield (l, r)


def contexts(n):
    """one-hole contexts with n leaves (the hole counts as a leaf)"""
    for t in trees(n):
        leaves = count(t)
        for i in range(leaves):
            yield put_hole(t, i)


def count(t):
    return 1 if t == "S" else count(t[0]) + count(t[1])


def put_hole(t, i):
    if t == "S":
        return H if i == 0 else t
    k = count(t[0])
    if i < k:
        return (put_hole(t[0], i), t[1])
    return (t[0], put_hole(t[1], i - k))


def plug(C, u):
    if C == H:
        return u
    if C == "S":
        return "S"
    return (plug(C[0], u), plug(C[1], u))


CL = {}


def cls(t):
    if t == "S":
        return 0
    r = CL.get(t)
    if r is None:
        r = int(T[cls(t[0]), cls(t[1])])
        CL[t] = r
    return r


def spine(t):
    a = []
    while t != "S":
        a.append(t[1]); t = t[0]
    a.reverse()
    return a


def size(t):
    return 1 if t == "S" else size(t[0]) + size(t[1])


class Budget(Exception):
    pass


def colour(t, budget):
    """'G' if t normalises, 'R' if certified red, raises Budget otherwise"""
    stack = [t]
    steps = 0
    while stack:
        u = stack.pop()
        if cls(u) == BOT:
            return "R"
        L = spine(u)
        while len(L) >= 3:
            steps += 1
            if steps > budget or sum(size(x) for x in L[:3]) > 4000:
                raise Budget
            a, b, c = L[0], L[1], L[2]
            L = spine(a) + [c, (b, c)] + L[3:]
        stack.extend(L)
        if len(stack) > 20000:
            raise Budget
    return "G"


if __name__ == "__main__":
    EMAX, PMAX, J = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    MINCH = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    found = 0
    for ne in range(1, EMAX + 1):
        for E in contexts(ne):
            for npc in range(2, PMAX + 1):
                for P in contexts(npc):
                    cols = []
                    u = "S"
                    for j in range(J + 1):
                        t = plug(E, u)
                        try:
                            cols.append(colour(t, 200000))
                        except Budget:
                            cols.append("?")
                        u = plug(P, u)
                    s = "".join(cols)
                    ch = sum(1 for a, b in zip(s, s[1:]) if a != b and "?" not in (a, b))
                    if ch >= MINCH and "?" not in s:
                        found += 1
                        print(f"E={E} P={P}: {s}  ({ch} changes)", flush=True)
    print("families found:", found)
