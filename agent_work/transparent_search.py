"""Find closed S-terms T whose generic activation rule [T, u, v | r] ->* L ++ [r] has the 'transparent' shape:
L[0] = v exactly (front is the bare v), L[1] = u.v (= Z) exactly, and every other element of L closed (no u, v).
Such T can be appended to an accumulator by the S-absorption queue mechanism."""
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
    found = []; shapes = collections.Counter()
    for n in range(1, N + 1):
        for T in hm.trees(n):
            st = [r, v, u, T]
            status, k = hm.run(st, 5000)
            if status != "stuck": continue
            Lst = list(reversed(st))
            if Lst[-1] != r: continue
            Lst = Lst[:-1]
            if Lst[0] == v and len(Lst) >= 2 and Lst[1] == Z and all(closed(x) for x in Lst[2:]):
                found.append((hm.show(T), k, [hm.show(x) for x in Lst[2:]]))
            # also record shapes where front is v and Z occurs right after with junk containing v
            if Lst[0] == v and len(Lst) >= 2:
                shapes["front v, second=" + ("Z" if Lst[1] == Z else "other")] += 1
    print(shapes)
    print("transparent:", len(found))
    for f in found[:50]: print(f)
