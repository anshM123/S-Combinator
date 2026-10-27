import sys
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def parse(s):
    toks = [ch for ch in s if ch in "Sp()"]; pos = [0]
    def atom():
        ch = toks[pos[0]]; pos[0] += 1
        if ch == "S": return 0
        if ch == "p": return P
        t = seq(); pos[0] += 1; return t
    def seq():
        t = atom()
        while pos[0] < len(toks) and toks[pos[0]] != ")": t = hm.app(t, atom())
        return t
    return seq()
D = parse(sys.argv[1])
for ph in range(2, 6):
    st = [Rr, Y, X, D]; lines = []
    for t in range(40):
        lines.append(hm.show_list(st, maxn=7)[:170])
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        hm.step(st)
    print("phase", ph, "datum", hm.show(D))
    for l in lines[:12]: print("   ", l)
    if not (len(st) >= 3 and hm.head(st[-1]) == P and T3.S3.proper(st[-3])): print("   -> no proper transfer"); break
    V = st[-3]; print("   -> proper transfer V =", hm.show(V))
    D = tg.subst(tg.subst(V, P, c3.FROZ[ph]), Y, P)
