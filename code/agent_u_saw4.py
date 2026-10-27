"""Agent U round 5: node N_i . X . c with A = SS-nest (i), X = a B-family counter (any context <= 4 leaves) possibly
carrying ONE extra junk argument (frame-compound allowed by the frame lemma), c a small constant.
Reports node-shape transitions (A offset, B offset, junk-arity) per branch."""
import sys, collections
from agent_u_ctxnest import run, isC, spine
from agent_u_saw3 import contexts, SS, B
from symb import trees, show
def mk_stop(c):
    def stop(K, br, n):
        h, a = spine(K[0])
        if not (isC(h) and h[1] == 0 and len(a) == 2 and a[1] == c): return None
        x = a[0]; hx, ax = spine(x)
        if isC(hx) and hx[1] == 1 and len(ax) <= 1:
            return (h[2:], hx[2:], len(ax))
        return None
    return stop
if __name__ == "__main__":
    cnt = collections.Counter(); hits = []
    consts = [t for n in range(1, 3) for t in trees(n)]
    for ctxB in contexts(4):
        for bB in [t for n in range(1, 4) for t in trees(n)]:
            for c in consts:
                fams = [((SS, "#"), B), (ctxB, bB)]
                node = (((("C", 0, "i", 0)), ("C", 1, "k", 0)), c)
                out = run([node, "w1", "w2"], fams, mk_stop(c), maxsteps=60, cap=4)
                tr = [o for o in out if isinstance(o[1], tuple)]
                for o in tr: cnt[(o[1][0][1] if o[1][0][0] == "i" else ("->", o[1][0]), o[1][1][1] if o[1][1][0] == "k" else ("->", o[1][1]), o[1][2])] += 1
                if any(o[1][0][0] == "i" and o[1][0][1] < 0 and o[1][1][0] == "k" and o[1][1][1] > 0 for o in tr):
                    hits.append((ctxB, show(bB), show(c), [(o[0], o[1], o[2]) for o in tr]))
    print(cnt.most_common(20)); print("transfer hits:", len(hits))
    for h in hits[:10]: print(h)
