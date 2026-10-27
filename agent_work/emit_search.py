"""Find closed T whose generic rule [T, u, v | r] ->* L ++ [r] has the 'emitter' shape
   L[0] = v . w1 ... wj  (front: the bare next symbol with closed extra args),
   L[1] = (u.v) . w'1 ... w'k  (accumulator with closed symbols appended),
   L[2:] closed.
Such T would stream like S but emit the closed symbols w' into the accumulator."""
import sys, collections
import hm
u = hm.atom("u"); v = hm.atom("v"); r = hm.atom("r")
Z = hm.app(u, v)
def closed(t):
    stack = [t]
    while stack:
        i = stack.pop()
        if i < 0: return False
        if i > 0: stack.append(hm.L[i]); stack.append(hm.R[i])
    return True
if __name__ == "__main__":
    N = int(sys.argv[1])
    found = []; cnt = collections.Counter()
    for n in range(1, N + 1):
        for T in hm.trees(n):
            st = [r, v, u, T]
            status, k = hm.run(st, 5000)
            if status != "stuck": continue
            Lst = list(reversed(st))
            if Lst[-1] != r: continue
            Lst = Lst[:-1]
            if len(Lst) < 2: continue
            fa, fh = hm.spine(Lst[0])
            if fh != v: continue
            # front's args: args(v) are unknown; Lst[0] = v.w1..wj means spine args (with head v) all closed
            if not all(closed(w) for w in fa): continue
            sa, sh = hm.spine(Lst[1])
            # second must be Z . closed...: spine of Lst[1] w.r.t head u: args = [v, w'...]
            if sh != u or not sa or sa[0] != v or not all(closed(w) for w in sa[1:]): continue
            if not all(closed(x) for x in Lst[2:]): continue
            cnt[(len(fa), len(sa) - 1, len(Lst) - 2)] += 1
            found.append((hm.show(T), k, hm.show_list(st)))
    print(cnt)
    for f in found[:60]: print(f)
