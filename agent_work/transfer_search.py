"""Search for Church-style transfer contexts.
For a 1-hole context F (hole = opaque atom a), run the generic list [F[a], x, b | r] (a, x, b, r opaque) until stuck.
Record contexts where the stuck front is exactly a (the predecessor runs next) and the third element e2 (the
v-input of a's activation) is built from b and S only (b occurring), i.e. e2 = G[b] for a context G.
Then check the reverse condition for G: run [G[b], y, a'] and see whether it gets stuck at front b with v-input F[a'].
Also report 'self-transfer' contexts with G = F."""
import sys, collections
import hm
A = hm.atom("a"); Xx = hm.atom("x"); B = hm.atom("b"); Rr = hm.atom("r"); Y = hm.atom("y"); A2 = hm.atom("c")
_ctx = {}
def contexts(n, hole):
    key = (n, hole)
    if key in _ctx: return _ctx[key]
    out = []
    if n == 1: out = [hole]
    else:
        for k in range(1, n):
            for l in contexts(k, hole):
                for rr in hm.trees(n - k): out.append(hm.app(l, rr))
            for l in hm.trees(k):
                for rr in contexts(n - k, hole): out.append(hm.app(l, rr))
    _ctx[key] = out
    return out
def atoms_in(t):
    s = set(); stack = [t]
    while stack:
        i = stack.pop()
        if i < 0: s.add(i)
        elif i > 0: stack.append(hm.L[i]); stack.append(hm.R[i])
    return s
def subst(t, at, val, memo=None):
    if memo is None: memo = {}
    if t == at: return val
    if t <= 0: return t
    r = memo.get(t)
    if r is None:
        r = hm.app(subst(hm.L[t], at, val, memo), subst(hm.R[t], at, val, memo)); memo[t] = r
    return r
def count_occ(t, at):
    if t == at: return 1
    if t <= 0: return 0
    return count_occ(hm.L[t], at) + count_occ(hm.R[t], at)
if __name__ == "__main__":
    smax = int(sys.argv[1]); budget = 4000
    stats = collections.Counter(); cands = []
    for s in range(2, smax + 1):
        for F in contexts(s, A):
            if hm.head(F) != 0: continue
            st = [Rr, B, Xx, F]
            status, k = hm.run(st, budget)
            if status != "stuck": stats[status] += 1; continue
            if st[-1] != A: stats["front!=a"] += 1; continue
            if len(st) < 3: stats["short"] += 1; continue
            e1, e2 = st[-2], st[-3]
            at = atoms_in(e2)
            if at == {B} and count_occ(e2, B) == 1:
                stats["clean G"] += 1
                cands.append((F, e1, e2, k))
            else:
                stats["other e2"] += 1
    print(stats)
    print("candidates:", len(cands))
    selfs = []
    for F, e1, e2, k in cands:
        G = subst(e2, B, A)  # G as context with hole a
        # reverse check: [G[b], y, c] -> stuck at front b with v-input F[c]?
        Gb = subst(G, A, B)
        st = [Rr, A2, Y, Gb]
        status, k2 = hm.run(st, budget)
        rev = None
        if status == "stuck" and st[-1] == B and len(st) >= 3:
            rev = st[-3]
        Fc = subst(F, A, A2)
        ok = (rev == Fc)
        tag = "SELF" if G == F else ""
        if ok or tag:
            selfs.append((hm.show(F), hm.show(G), k, k2, ok, tag))
        print(f"F={hm.show(F):28s} u'={hm.show(e1):24s} G[b]={hm.show(e2):20s} k={k} | rev front={hm.show(st[-1]) if status=='stuck' else status} v'={hm.show(rev) if rev else '-'} {'OK' if ok else ''} {tag}")
    print("REVERSE-OK / SELF:", selfs)
