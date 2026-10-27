"""Can closed code rebuild itself? For every closed S-term Q with <= NMAX leaves, run the head machine on
[Q, x1, x2, x3, x4] (x_i opaque, never opened) for STEPS steps and record whether Q reappears as the front element
(code reproduces itself in control) or as the element directly above an opaque datum (rebuilt in place of a target).
Usage: python selfrep.py NMAX STEPS
"""
import sys, collections
from symb import trees, show, spine
sys.setrecursionlimit(100000)

def run(Q, steps):
    K = [Q, "x1", "x2", "x3", "x4"]
    front_again = above_datum = None
    for n in range(1, steps + 1):
        if len(K) < 3: return front_again, above_datum, "hnf"
        a, b, c = K[0], K[1], K[2]
        ha, aa = spine(a)
        if ha != "S": return front_again, above_datum, "stuck"
        K = list(aa) + [c, (b, c)] + K[3:]
        if front_again is None and K[0] == Q: front_again = n
        if above_datum is None:
            for i in range(len(K) - 1):
                if K[i] == Q and isinstance(K[i + 1], str) and K[i + 1] != "S":
                    above_datum = n; break
    return front_again, above_datum, "running"

if __name__ == "__main__":
    NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
    stat = collections.Counter(); ex = []
    for n in range(2, NMAX + 1):
        for Q in trees(n):
            f, a, how = run(Q, STEPS)
            stat[how] += 1
            if f: stat["front_again"] += 1
            if a: stat["above_datum_again"] += 1
            if (f or a) and len(ex) < 10: ex.append((show(Q), f, a, how))
    print(dict(stat))
    for e in ex: print("  ", e)
