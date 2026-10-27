"""LPM program search.  State u = X . A . B . T  (spine(u) = spine(X) ++ [A, B, T]) with A = N_a, B = N_b numerals
over a base beta (N_0 = beta, N_{n+1} = SS.N_n).  One LPM step: head-normalise u, take the first component.
For each (X, T, beta) record the map (a, b) -> next state parsed as X'.N_a'.N_b'.T' (X', T' arbitrary closed terms;
the parse takes the last three spine args).  Report maps where both counters move or X' depends on (a, b)."""
import sys, collections
import hm, lpm
SS = hm.parse("SS")
def numval(x, beta):
    c = 0
    while x != beta:
        if x > 0 and hm.L[x] == SS: c += 1; x = hm.R[x]
        else: return None
    return c
def parse_state(t, beta):
    a, h = hm.spine(t)
    if h != 0 or len(a) < 3: return None
    A, B, T = a[-3], a[-2], a[-1]
    va, vb = numval(A, beta), numval(B, beta)
    if va is None or vb is None: return None
    X = hm.build(0, a[:-3])
    return (hm.show(X), va, vb, hm.show(T))
if __name__ == "__main__":
    xmax = int(sys.argv[1]); tmax = int(sys.argv[2]); K = 4
    betas = [hm.parse(s) for s in ["S(SS)(SS)", "S", "SSS", "S(SS)", "S(SSS)S", "SS"]]
    Xs = [t for n in range(1, xmax + 1) for t in hm.trees(n)]
    Ts = [t for n in range(1, tmax + 1) for t in hm.trees(n)]
    nums = {}
    for beta in betas:
        for n in range(K + 1): nums[(beta, n)] = lpm.nest(beta, n)
    M0 = hm.mark()
    stats = collections.Counter(); found = []
    for beta in betas:
        for X in Xs:
            for T in Ts:
                tab = {}
                for a in range(K + 1):
                    for b in range(K + 1):
                        u = hm.build(0, hm.spine(X)[0] + [nums[(beta, a)], nums[(beta, b)], T])
                        nxt, st, k, Lst = lpm.lpm_step(u, 3000)
                        tab[(a, b)] = parse_state(nxt, beta) if nxt is not None else st
                        hm.truncate(M0)
                parsed = [v for v in tab.values() if isinstance(v, tuple)]
                if len(parsed) < (K + 1) ** 2 // 2: stats["mostly unparsed"] += 1; continue
                # classify
                moves = set()
                for (a, b), v in tab.items():
                    if isinstance(v, tuple): moves.add((v[0], v[1] - a, v[2] - b, v[3]))
                    else: moves.add(("-", v))
                key = tuple(sorted(map(str, moves)))
                both = any(isinstance(v, tuple) and v[1] != a and v[2] != b for (a, b), v in tab.items())
                xdep = len({v[0] for v in parsed}) > 1
                stats[("both" if both else "") + ("xdep" if xdep else "")] += 1
                if both or xdep:
                    found.append((hm.show(beta), hm.show(X), hm.show(T), tab))
    print(stats)
    print("found", len(found))
    seen = set()
    for beta, X, T, tab in found[:400]:
        sig = tuple((k, (v[1] - k[0], v[2] - k[1]) if isinstance(v, tuple) else v) for k, v in sorted(tab.items()))
        if sig in seen: continue
        seen.add(sig)
        print("beta=%s X=%s T=%s" % (beta, X, T))
        for a in range(K + 1):
            print("   ", [tab[(a, b)] if not isinstance(tab[(a, b)], tuple) else (tab[(a, b)][0][:10], tab[(a, b)][1], tab[(a, b)][2], tab[(a, b)][3][:8]) for b in range(K + 1)])
