"""Extract a parity-counting family predicted by a non-aperiodic finite S-model and print concrete S-terms.

Finds a shortest context word w (generators x -> a*x, x -> x*a over class representatives) whose map f has a cycle of
length > 1, a class x on that cycle with alternating images, and a learned context e separating the alternating classes;
prints t_k = e[P^k[rep x]] for k = 0..K together with the model's predicted verdicts.
usage: python parityfam.py MODELFILE K OUTFILE"""
import sys
from verify_model import load

path, K, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
reps, F, T = load(path)
n = len(reps); s = reps.index("S")
ctxs = [l[2:].strip() for l in open(path) if l.startswith("# ") and "#" in l[2:] and not l.startswith("# lstar")
        and not l.startswith("# product") and not l.startswith("# end") and not l.startswith("# contexts")]

gens = []   # (map tuple, kind, class)
for a in range(n):
    gens.append((tuple(int(T[a, x]) for x in range(n)), "L", a))
    gens.append((tuple(int(T[x, a]) for x in range(n)), "R", a))
ident = tuple(range(n))
word = {ident: []}; frontier = [ident]
def period(g):
    seen = {}; r = ident; k = 0
    while r not in seen: seen[r] = k; r = tuple(g[r[x]] for x in range(n)); k += 1
    return k - seen[r], seen[r]
found = None
while frontier and not found:
    new = []
    for g in frontier:
        for h, kind, a in gens:
            c = tuple(h[g[x]] for x in range(n))
            if c in word: continue
            word[c] = word[g] + [(kind, a)]
            new.append(c)
            p, idx = period(c)
            if p > 1: found = (c, p, idx); break
        if found: break
    frontier = new
f, p, idx = found
print(f"map with period {p} (index {idx}) found after {len(word)} monoid elements; word length {len(word[f])}")

def ctx_of(w):
    """one-hole context string for the word (innermost first)"""
    c = "#"
    for kind, a in w:
        c = ("(" + reps[a] + ")(" + c + ")") if kind == "L" else ("(" + c + ")(" + reps[a] + ")")
    return c

def fill(c, t): return c.replace("#", "(" + t + ")")

def power(g, k):
    r = ident
    for _ in range(k): r = tuple(g[r[x]] for x in range(n))
    return r

# choose x and an outer context separating the alternating classes
best = None
for x in range(n):
    seq = [power(f, k)[x] for k in range(idx + 2 * p + 2)]
    tail = seq[idx:]
    if len(set(tail[:p])) > 1:
        c1, c2 = tail[0], tail[1]
        for e in ["#"] + ctxs:
            # acceptance of e[class] via the table: evaluate the context on the class
            def ev_ctx(e_str, cls):
                # parse context string to tuple with '#'
                pos = [0]
                def atom():
                    ch = e_str[pos[0]]
                    if ch == "(":
                        pos[0] += 1; t = term(); pos[0] += 1; return t
                    pos[0] += 1; return "S" if ch == "S" else "#"
                def term():
                    t = atom()
                    while pos[0] < len(e_str) and e_str[pos[0]] != ")": t = (t, atom())
                    return t
                tt = term()
                def cl(u):
                    if u == "S": return s
                    if u == "#": return cls
                    return int(T[cl(u[0]), cl(u[1])])
                return cl(tt)
            if F[ev_ctx(e, c1)] != F[ev_ctx(e, c2)]:
                best = (x, e, [bool(F[ev_ctx(e, power(f, k)[x])]) for k in range(K + 1)]); break
    if best: break
x, e, pred = best
P = ctx_of(word[f])
print("pumping context P =", P)
print("base D = rep of class", x, "=", reps[x])
print("outer context E =", e)
print("predicted BT-finite for k = 0..K:", "".join("1" if v else "0" for v in pred))
with open(out, "w") as fo:
    for k in range(K + 1):
        t = reps[x]
        for _ in range(k): t = fill(P, t)
        fo.write(fill(e, t) + "\n")
print("wrote", K + 1, "terms to", out)
