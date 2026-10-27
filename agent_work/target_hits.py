"""For the 'good' phase-3 hits w (right combs over p), search phase-2 data D2 = K.(d.T) / K.T with T = w, K closed
<= NK leaves, d closed <= ND leaves: does the phase-2 run make a proper position-3 transfer, and does phase 3 then
make one?"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def parse(s):
    # tiny parser for the show() format: juxtaposition = application, parentheses group, S, p
    toks = [ch for ch in s if ch in "Sp()"]
    pos = [0]
    def atom():
        ch = toks[pos[0]]; pos[0] += 1
        if ch == "S": return 0
        if ch == "p": return P
        if ch == "(":
            t = seq(); pos[0] += 1; return t
        raise ValueError(s)
    def seq():
        t = atom()
        while pos[0] < len(toks) and toks[pos[0]] != ")":
            t = hm.app(t, atom())
        return t
    return seq()
HITS = """S(S(S(SS)(SS)p)) S(S(S(SSSSS)p)) S(S(SS(S(SS))(SS)p)) S(S(S(SSS)p)) S(S(S(SS(SS))(Sp))) S(S(SS(SS)(SSp)))
S(S(S(SS(SSS))(Sp))) S(S(S(SS(SS)S)(Sp))) S(S(SS(SS(SS))(SS(SSp)))) S(S(S(SSS)(Sp))) S(S(SSSS(SSp)))
S(S(S(S(S(SS))(SS))(Sp))) S(S(S(SSS)(S(SS(Sp))))) S(S(SS(SS)(S(SS)(SSp)))) S(S(SS(S(SS))(SS)(SSp)))
S(S(SSS(SS(Sp)))) S(S(SSS(SS(S(Sp))))) S(S(S(SS)(SS)(Sp))) S(S(SS(SS(SS))(SSp)))""".split()
NK, ND = int(sys.argv[1]), int(sys.argv[2])
Ks = [t for n in range(1, NK + 1) for t in hm.trees(n) if hm.head(t) == 0]
Ds = [None] + [t for n in range(1, ND + 1) for t in hm.trees(n)]
M0 = hm.mark(); st = collections.Counter(); found = []
for hs in HITS:
    T = parse(hs)
    assert hm.show(T) == hs, (hm.show(T), hs)
    M1 = hm.mark()
    for d in Ds:
        tail = T if d is None else hm.app(d, T)
        for K in Ks:
            D2 = hm.app(K, tail)
            o2, V, _ = T3.phase(D2, 2000)
            st["p2 " + o2] += 1
            if o2 == "proper3":
                inner = V
                while hm.R[inner] != Y: inner = hm.R[inner]
                if hm.L[inner] == T: st["V innermost = hit"] += 1
                D3 = tg.subst(tg.subst(V, P, C), Y, P)
                o3, V3, l3 = T3.phase(D3, 2000)
                st["p3 " + o3] += 1
                if o3 == "proper3": found.append((hm.show(D2), hm.show(V)))
            hm.truncate(M1)
print(st)
for f in found[:10]: print("PHASE-3 PROPER", f)
