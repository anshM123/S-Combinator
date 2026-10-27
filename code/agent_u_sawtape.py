"""Agent U round 6 (a): sawtooth node N_i . N_k . V over a tape holding a counter C (family ctxC, base bC):
tape layouts [C], [c, C], [C, c], [j, C] (j opaque junk). Reports transitions (i, k, C) of node + tape shape."""
import sys, collections
from agent_u_ctxnest import run, isC, spine
from agent_u_saw3 import contexts
from symb import trees, show
SS = ("S", "S"); B = (("S", SS), SS)
def mk(V, lay):
    def stop(K, br, n):
        h, a = spine(K[0])
        if not (isC(h) and h[1] == 0 and len(a) == 2 and isC(a[0]) and a[0][1] == 0 and a[1] == V): return None
        # tape after the node: find C per layout (junk slots are wildcards)
        tape = K[1:1 + len(lay)]
        if len(tape) < len(lay): return None
        cval = None
        for s, x in zip(lay, tape):
            if s == "C":
                if isC(x) and x[1] == 1: cval = x[2:]
                else: return ("node", h[2:], a[0][2:])
            elif s == "j": pass
            elif x != s: return ("node", h[2:], a[0][2:])
        return (h[2:], a[0][2:], cval)
    return stop
if __name__ == "__main__":
    fuels = [t for n in range(1, 4) for t in trees(n)]
    small = [t for n in range(1, 3) for t in trees(n)]
    layouts = [["C"], ["j", "C"]] + [[c, "C"] for c in small] + [["C", c] for c in small]
    cnt = collections.Counter(); hits = []
    for ctxC in contexts(3):
        for V in fuels:
            for lay in layouts:
                fams = [((SS, "#"), B), (ctxC, B)]
                node = ((("C", 0, "i", 0), ("C", 0, "k", 0)), V)
                tape = [("C", 1, "m", 0) if s == "C" else ("j1" if s == "j" else s) for s in lay]
                out = run([node] + tape + ["w1", "w2"], fams, mk(V, lay), maxsteps=60, cap=4)
                tr = [o for o in out if isinstance(o[1], tuple) and o[1][0] != "node"]
                for o in tr: cnt[(o[1][0][1] if o[1][0][0] == "i" else o[1][0], o[1][1][1] if o[1][1][0] == "k" else o[1][1], o[1][2])] += 1
                if any(o[1][2] is not None and o[1][2] != ("m", 0) for o in tr):
                    hits.append((ctxC, show(V), lay, [(o[0], o[1], o[2]) for o in tr]))
    print(cnt.most_common(15)); print("C changes:", len(hits))
    for h in hits[:12]: print(h)
