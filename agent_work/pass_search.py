"""Search 1-hole contexts C (hole = opaque atom X) for activation rules [C[X], u, v | r] -> ... where the stuck front
is u-, v- or X-headed, and classify how X appears in the result list:
   'clean-arg'  : X is a top-level spine argument of the front, or a list element by itself
   'glued'      : X occurs only inside larger compounds
Reports contexts where X is passed cleanly AND the front is u- or v-headed (data hands a component to a handler)."""
import sys, collections
import hm
X = hm.atom("X"); u = hm.atom("u"); v = hm.atom("v"); r = hm.atom("r"); r2 = hm.atom("q")
_ctx = {}
def contexts(n):
    if n in _ctx: return _ctx[n]
    out = []
    if n == 1: out = [X]
    else:
        for k in range(1, n):
            for l in contexts(k):
                for rr in hm.trees(n - k): out.append(hm.app(l, rr))
            for l in hm.trees(k):
                for rr in contexts(n - k): out.append(hm.app(l, rr))
    _ctx[n] = out
    return out
def occurs(t, a):
    stack = [t]
    while stack:
        i = stack.pop()
        if i == a: return True
        if i > 0: stack.append(hm.L[i]); stack.append(hm.R[i])
    return False
if __name__ == "__main__":
    smax = int(sys.argv[1])
    res = collections.Counter(); hits = []
    for s in range(2, smax + 1):
        for C in contexts(s):
            if hm.head(C) != 0: continue
            st = [r2, r, v, u, C]
            status, k = hm.run(st, 2000)
            if status != "stuck": res[status] += 1; continue
            f = st[-1]; fargs, fh = hm.spine(f)
            hname = hm.show(fh)
            clean = (X in fargs) or (X in st[:-1])
            res[(hname, clean)] += 1
            if clean and fh in (u, v):
                hits.append((hm.show(C), k, hm.show_list(st)))
    print(res)
    print("hits:", len(hits))
    for h in hits[:80]: print(h)
