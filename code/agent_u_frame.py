"""Agent U round 5: list templates whose control is a frame F[N_k] (F context <= MAXF leaves, N = SS-nest),
with a second SS-nest counter M_m in the tape: [F[N_k], M_m, c, w] and [F[N_k], c, M_m, w] (c in {S, SS}).
Reports transitions of the template (k-offset, m-offset) for every branch."""
import sys, collections
from agent_u_ctxnest import run, isC, spine, plug, match_ctx
from agent_u_saw3 import contexts, SS, B
from symb import show
def ctxmatch(t, ctx):
    c = match_ctx(t, ctx)
    return c if c not in (None, False) and isC(c) else None
if __name__ == "__main__":
    MAXF = int(sys.argv[1]); cnt = collections.Counter(); hits = []
    fams = [((SS, "#"), B)]
    for F in contexts(MAXF):
        for c in ("S", SS):
            for order in ("Mc", "cM"):
                ctrl = plug(F, ("C", 0, "k", 0))
                tape = [("C", 0, "m", 0), c] if order == "Mc" else [c, ("C", 0, "m", 0)]
                start = [ctrl] + tape + ["w1", "w2"]
                def stop(K, br, n, F=F, c=c, order=order):
                    x = ctxmatch(K[0], F)
                    if x is None or len(K) < 3: return None
                    mpos, cpos = (1, 2) if order == "Mc" else (2, 1)
                    if K[cpos] != c or not isC(K[mpos]): return None
                    return (x[2:], K[mpos][2:])
                out = run(start, fams, stop, maxsteps=60, cap=4)
                tr = [o for o in out if isinstance(o[1], tuple)]
                for o in tr: cnt[(o[1][0][0], o[1][0][1], o[1][1][0], o[1][1][1])] += 1
                if any(o[1][1] != ("m", 0) for o in tr):
                    hits.append((F, show(c), order, [(o[0], o[1], o[2]) for o in tr]))
    print(cnt.most_common(15)); print("templates where M changes:", len(hits))
    for h in hits[:12]: print(h)
