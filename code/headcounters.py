"""Counter programs inside ONE infinite head run (leftmost-outermost evaluation of a term without hnf).

Configuration template T(i, k) = ch(C) ++ [N(W,B1,i), N(W,B2,k)] ++ tail, with C a closed 'code' term, N(W,B,n) the
nest W^n(B) (symbolic n). Run the exact symbolic head machine (case splits n = 0 / n >= 1, W-applications folded back
into nests) until the configuration again starts with ch(C) followed by two nests of the families (B1', B2') from the
base pool (state changes allowed); record the guarded transition (i, k) -> (i', k') and the new family.
Usage: python headcounters.py CODEMAX BASEMAX STEPS
"""
import sys, itertools, collections
import nestwalk as nw
from symb import trees, show, spine as sspine

CODEMAX, BASEMAX, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
W = [("S", "S")]
bases = [t for n in range(1, BASEMAX + 1) for t in trees(n)]
bidx = {b: i for i, b in enumerate(bases)}

def nestinfo(e):
    return (e[2], e[3], e[4]) if isinstance(e, tuple) and len(e) == 5 and e[0] == "N" else None

def transitions(C, b1, b2, tail):
    cs = sspine(C)[1]
    start = list(cs) + [("N", 0, b1, "i", 0), ("N", 0, b2, "k", 0)] + tail
    out = []
    work = [(start, nw.Br({}), 0)]
    while work:
        K, br, n = work.pop()
        if n > 0 and len(K) >= len(cs) + 2 and K[:len(cs)] == cs:
            a, b = nestinfo(K[len(cs)]), nestinfo(K[len(cs) + 1])
            if a and b:
                out.append((dict(br.cons), (a, b))); continue
        if n >= STEPS or len(K) < 3 or any(v[1] > nw.CAP for v in br.cons.values()):
            continue
        x, y, z = K[0], K[1], K[2]
        for (l, b2_) in nw.open_el(x, W, bases, br):
            newK = [nw.fold(e, W) for e in (l + [z, (y, z)])] + K[3:]
            work.append((newK, b2_, n + 1))
    return out

if __name__ == "__main__":
    codes = [t for n in range(1, CODEMAX + 1) for t in trees(n)]
    tails = [[], ["S"]]
    progs = collections.Counter(); ex = {}
    for C in codes:
        for b1, b2 in itertools.product(range(len(bases)), repeat=2):
            for tail in tails:
                tr = transitions(C, b1, b2, tail)
                if len(tr) < 2: continue
                key = tuple(sorted((tuple(sorted(c.items())), (a[0] != b1 or b[0] != b2, a[1:], b[1:])) for c, (a, b) in tr))
                interesting = any(a[1:] not in (("i", -1), ("i", 0)) or b[1:] != ("k", 0) or a[0] != b1 or b[0] != b2
                                  for c, (a, b) in tr)
                if interesting:
                    progs[key] += 1
                    ex.setdefault(key, (show(C), show(bases[b1]), show(bases[b2]), [show(x) for x in tail]))
    print(f"distinct non-trivial head-run counter programs: {len(progs)}")
    for key, cnt in progs.most_common(15):
        print(f"  [{cnt}] code={ex[key][0]} B1={ex[key][1]} B2={ex[key][2]} tail={ex[key][3]}")
        for g, t in key: print("        ", dict(g), "->", t)
