"""Phase-3 p'-fronts: classify positions 2 and 3 at every p'-headed stuck state (and every p'-headed front reached
during the run, if the run is continued past it by opening p' as an opaque predecessor is not possible — so only the
stuck state).  Also record whether bare y is still present and where."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def desc(t):
    if t == Y: return "y"
    a = tg.atoms(t)
    if a.get(X) or a.get(Rr): return "Yx"
    if a.get(Y): return "Ywrap" if not a.get(P) else "Ywrap+p"
    if a.get(P): return "P'"
    if a.get(C): return "C"
    return "CL"
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = {}
    data = [D for D in c3.rcombs(N) if hm.R[D] != P]
    M0 = hm.mark()
    for D in data:
        r, Vs = c3.phase(D, 4000)
        if r != "proper": hm.truncate(M0); continue
        for V in Vs:
            D3 = tg.subst(tg.subst(V, P, C), Y, P)
            lst = [Rr, Y, X, D3]
            s, k = hm.run(lst, 4000)
            if s == "stuck" and hm.head(lst[-1]) == P:
                L = list(reversed(lst))
                ypos = L.index(Y) + 1 if Y in L else None
                key = (desc(L[1]) if len(L) > 1 else "-", desc(L[2]) if len(L) > 2 else "-", "bare y at %s" % ypos)
                st[key] += 1; ex.setdefault(key, (hm.show(D3)[:50], hm.show_list(lst, maxn=5)[:110]))
        hm.truncate(M0)
    for k, v in st.most_common(): print(v, k, ex[k])
