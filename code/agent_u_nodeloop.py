"""Agent U: node-level loop search inside ONE head run (Lemma P descent); reproduces the sawtooth.
Usage: python agent_u_nodeloop.py

node-level loop search, general node shapes and two nest families.
node = Nest(fam f0, var 'i') . arg1 . ... . argr ; arg = ('C', const) | ('N', fam, var).  Tape w1, w2 opaque.
Records every later front element of the same shape (constants equal, nest slots: same family, any var/offset)."""
import sys
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
import nestwalk as nw
from symb import trees, show, spine as sspine
VARS = ("w1", "w2")
def headvar(e):
    while isinstance(e, tuple) and e[0] != "N": e = e[0]
    return e in VARS
def fold(t, W):
    if isinstance(t, str) or (isinstance(t, tuple) and t[0] == "N"): return t
    f, a = fold(t[0], W), fold(t[1], W)
    if isinstance(a, tuple) and a and a[0] == "N":
        h, args = nw.spine(f) if isinstance(f, tuple) else (f, [])
        if h == "S" and args == sspine(W[a[1]])[1]:
            return ("N", a[1], a[2], a[3], a[4] + 1)
    return (f, a)
def isN(e): return isinstance(e, tuple) and len(e) == 5 and e[0] == "N"
def match(e, shape):
    args = []
    while isinstance(e, tuple) and not isN(e): args.append(e[1]); e = e[0]
    args.reverse()
    if not isN(e) or e[1] != shape[0]: return None
    if len(args) != len(shape) - 1: return None
    out = [(e[3], e[4])]
    for a, s in zip(args, shape[1:]):
        if s[0] == "C":
            if a != s[1]: return None
        else:
            if not isN(a) or a[1] != s[1]: return None
            out.append((a[3], a[4]))
    return tuple(out)
def explore(W, B, shape, vars_, maxsteps=150, cap=5):
    nw.CAP = cap
    e = ("N", shape[0], shape[0], vars_[0], 0); vi = 1
    for s in shape[1:]:
        if s[0] == "C": e = (e, s[1])
        else: e = (e, ("N", s[1], s[1], vars_[vi], 0)); vi += 1
    work = [([e, "w1", "w2"], nw.Br({}), 0)]; out = []
    while work:
        K, br, n = work.pop()
        if n > 0:
            m = match(K[0], shape)
            if m is not None: out.append((dict(br.cons), m, n)); continue
        if n >= maxsteps: out.append((dict(br.cons), "budget", n)); continue
        if len(K) < 3: out.append((dict(br.cons), "hnf", n)); continue
        if any(v[1] > cap for v in br.cons.values()): out.append((dict(br.cons), "cap", n)); continue
        if headvar(K[0]): out.append((dict(br.cons), "stuck", n)); continue
        for (l, b2) in nw.open_el(K[0], W, B, br):
            newK = [fold(x, W) for x in (l + [K[2], (K[1], K[2])])] + K[3:]
            work.append((newK, b2, n + 1))
    return out
if __name__ == "__main__":
    import collections
    SSt = ("S", "S"); B0 = (("S", SSt), SSt)
    print("sawtooth N_i N_k S:", explore([SSt], [B0], [0, ("N", 0), ("C", "S")], ["i", "k"]))
    Ws = [t for n in range(1, 4) for t in trees(n)]; Bs = [t for n in range(1, 5) for t in trees(n)]
    cs = [t for n in range(1, 4) for t in trees(n)]
    shapes = [[0, ("N", 0)]] + [[0, ("N", 0), ("C", c)] for c in cs] + [[0, ("C", c), ("N", 0)] for c in cs]
    cnt = collections.Counter(); hits = 0
    for W in Ws:
        for Bb in Bs:
            for sh in shapes:
                out = explore([W], [Bb], sh, ["i", "k"], maxsteps=100, cap=4)
                body = [o for o in out if o[0].get("i") != ("eq", 0)]
                for o in body:
                    if isinstance(o[1], tuple): cnt[o[1]] += 1
                if body and all(isinstance(o[1], tuple) and o[1][0] == ("i", -1) and o[1][1][1] >= 1 for o in body): hits += 1
    print("same-family node templates:", len(Ws) * len(Bs) * len(shapes), "body transitions:", dict(cnt), "A--,B++ bodies:", hits)
