"""S1 agent: for ALL ordered single-occurrence S-headed data (<= N leaves), find the FIRST violation of INV-PY
(a list with non-empty P-region whose first Y-element is not the bare y) and classify: the step that caused it,
whether the previous step opened a single-argument P-front S.U with y at position 3, and the eventual phase-2
outcome (proper transfer single/multi, with IGEN?, non-proper p-front, call, reexec, budget).
usage: pyyviol.py N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ytopinv as YI
hm, tg, pg, P, Y = YI.hm, YI.tg, YI.pg, YI.P, YI.Y
cls = YI.cls
def run(D, budget=2000):
    X, Rr = YI.X, YI.Rr
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    hist.append(tuple(lst))
    return hist
def outcome(hist):
    L = hist[-1]
    if len(L) < 3: return "hnf"
    h = hm.head(L[-1])
    if h == 0: return "budget"
    if h == P:
        V = L[-3]
        if not YI.proper(V): return "pfront-nonproper"
        aV, _ = hm.spine(V); k = len(aV)
        igen = any(len(M) >= k and list(reversed(M[-k:])) == aV for M in hist[:-1])
        return ("proper-single" if hm.R[V] == Y else "proper-multi") + ("-IGEN" if igen else "")
    return "call/reexec"
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = {}
    for n in range(2, N + 1):
        CS = tg.contexts(n); M0 = hm.mark()
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) == 0 and pg.ordered(D):
                hist = run(D)
                viol = None
                for t in range(1, len(hist)):
                    L = list(reversed(hist[t]))
                    np_ = sum(1 for e in L if cls(e) == "P")
                    ys = [e for e in L if cls(e) == "Y"]
                    if np_ >= 1 and (not ys or ys[0] != Y):
                        Lp = list(reversed(hist[t - 1]))
                        ty = cls(Lp[0]) + cls(Lp[1]) + cls(Lp[2])
                        prev = ""
                        if t >= 2:
                            Lq = list(reversed(hist[t - 2]))
                            a, h = hm.spine(Lq[0])
                            prev = "prev:%s nargs=%d pos3=%s" % (cls(Lq[0]) + cls(Lq[1]) + cls(Lq[2]), len(a), "y" if Lq[2] == Y else cls(Lq[2]))
                        viol = (ty, prev)
                        break
                key = (viol, outcome(hist)) if viol else ("no violation", outcome(hist))
                st[key] += 1
                if key not in ex: ex[key] = hm.show(D)
            hm.truncate(M0); YI._cl.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
