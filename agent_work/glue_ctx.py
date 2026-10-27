"""Phase 3: at every step that glues a P'-element w onto the bare y, record the class of the front a (CL / C / P' /
Y), whether a is c-headed, and the outcome of the run."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, phase3_glue as G
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = {}
    data = [D for D in c3.rcombs(N) if hm.R[D] != P]
    M0 = hm.mark()
    for D in data:
        r, Vs = c3.phase(D, 4000)
        if r != "proper": hm.truncate(M0); continue
        for V in Vs:
            D3 = tg.subst(tg.subst(V, P, C), Y, P)
            lst = [Rr, Y, X, D3]; events = []
            for s in range(3000):
                if len(lst) < 3: break
                a, b, c = lst[-1], lst[-2], lst[-3]
                if hm.head(a) != 0: break
                if G.cls(b) == "P" and c == Y:
                    events.append(G.cls(a))
                hm.step(lst)
            h = hm.head(lst[-1]) if len(lst) >= 3 else None
            outcome = "REEXEC" if h == C else ("p'" if h == P else hm.NAMES.get(h, str(h)))
            if events:
                key = (tuple(events[:3]), outcome)
                st[key] += 1; ex.setdefault(key, hm.show(D3)[:60])
        hm.truncate(M0)
    for k, v in st.most_common(): print(v, k, ex[k])
