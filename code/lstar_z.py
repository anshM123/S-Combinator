"""L* learner of a finite S-model for head normalisation of OPEN S-terms over {S, z} (z an opaque variable).

Head machine with a variable: a configuration whose first element has head z is stuck = a head normal form.
Oracle verdict 1 = has an hnf (S-hnf or stuck), 0 = no hnf. Shortcuts (sound): a closed prefix S.[e1..ej], j >= 3, of
the configuration whose M35 class is bottom never head-normalises (Theorem A + Lemma 2(c)), so neither does the whole;
a closed configuration is decided by M35 (Theorem Q10). Otherwise run the machine with step budget CAP (exhaustion = 0).
Generators: class 0 = S, class 1 = z.
usage: python lstar_z.py CAP NTEST NRAND OUTFILE [MAXCLASSES]
"""
import sys, random, time
sys.setrecursionlimit(100000)
from verify_model import load

Mr, MF, MT = load("../data/model35_hn.txt"); sM = Mr.index("S"); BOT = [i for i in range(len(Mr)) if not MF[i]][0]
CAP, NTEST, NRAND, OUT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
MAXCLS = int(sys.argv[5]) if len(sys.argv) > 5 else 3000

def to_str(t):
    if t in ("S", "z", "#"): return t
    a = t[1]
    return to_str(t[0]) + (to_str(a) if a in ("S", "z", "#") else "(" + to_str(a) + ")")

def parse_tuple(s):
    pos = [0]
    def atom():
        c = s[pos[0]]
        if c == "(":
            pos[0] += 1; t = term(); pos[0] += 1; return t
        pos[0] += 1; return c
    def term():
        t = atom()
        while pos[0] < len(s) and s[pos[0]] != ")": t = (t, atom())
        return t
    return term()

mcache = {}
def mcls(t):
    """M35 class of a closed term, None if the term contains z"""
    if t == "S": return sM
    if t == "z": return None
    r = mcache.get(t, -1)
    if r == -1:
        a = mcls(t[0]); b = mcls(t[1]) if a is not None else None
        r = None if (a is None or b is None) else int(MT[a, b])
        mcache[t] = r
    return r

def spine(t):
    args = []
    while isinstance(t, tuple):
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

def oracle_term(t):
    c = mcls(t)
    if c is not None: return int(MF[c])
    h, K = spine(t)
    if h == "z": return 1
    steps = 0
    while len(K) >= 3:
        # closed-prefix bottom test
        k = sM; j = 0
        for e in K:
            ce = mcls(e)
            if ce is None: break
            k = int(MT[k, ce]); j += 1
            if k == BOT and j >= 3: return 0
        if steps >= CAP: return 0
        a, b, c3 = K[0], K[1], K[2]
        ha, aa = spine(a)
        if ha == "z": return 1
        K = aa + [c3, (b, c3)] + K[3:]; steps += 1
    return 1

ocache = {}; ncalls = 0
def evaluate(strs):
    global ncalls
    out = []
    for s in strs:
        r = ocache.get(s)
        if r is None:
            r = oracle_term(parse_tuple(s)); ocache[s] = r; ncalls += 1
        out.append(r)
    return out

def fill(c, s): return c.replace("#", "(" + s + ")")
def app(a, b): return a + (b if b in ("S", "z") else "(" + b + ")")

# a context separating S from z: # A A A with A A (A A) bottom in M35
def find_sep():
    def trees(n):
        if n == 1: return ["S"]
        return [(l, r) for i in range(1, n) for l in trees(i) for r in trees(n - i)]
    for n in range(1, 8):
        for A in trees(n):
            a = mcls(A)
            if int(MT[int(MT[a, a]), int(MT[a, a])]) == BOT:
                return "#" + "(" + to_str(A) + ")" * 1 + "(" + to_str(A) + ")" + "(" + to_str(A) + ")"
SEP = find_sep()

R = ["S", "z"]; E = ["#", SEP]; SIG = {}; PROD = {}; table = {}; sig_of = {}

def sync(terms):
    need = []
    for t in terms:
        s = SIG.setdefault(t, [])
        for j in range(len(s), len(E)): need.append((t, j))
    if not need: return
    v = evaluate([fill(E[j], t) for t, j in need])
    for (t, j), r in zip(need, v):
        s = SIG[t]
        while len(s) <= j: s.append(None)
        s[j] = r

def close():
    global R, sig_of, table
    while True:
        sync(R)
        sig_of = {}; newR = []
        for r in R:
            k = tuple(SIG[r])
            if k not in sig_of: sig_of[k] = len(newR); newR.append(r)
        if len(newR) != len(R): raise RuntimeError("representatives merged")
        R = newR
        pairs = [(a, b) for a in range(len(R)) for b in range(len(R))]
        for a, b in pairs:
            if (a, b) not in PROD: PROD[(a, b)] = app(R[a], R[b])
        sync([PROD[p] for p in pairs])
        added = 0; table = {}
        for a, b in pairs:
            k = tuple(SIG[PROD[(a, b)]])
            if k not in sig_of:
                sig_of[k] = len(R); R.append(PROD[(a, b)]); added += 1
            table[(a, b)] = sig_of[k]
        if added == 0 or len(R) > MAXCLS: return added == 0

def cls(t):
    if t == "S": return 0
    if t == "z": return 1
    return table[(cls(t[0]), cls(t[1]))]

def all_trees(n, memo={}):
    if n in memo: return memo[n]
    r = ["S", "z"] if n == 1 else [(l, rr) for i in range(1, n) for l in all_trees(i) for rr in all_trees(n - i)]
    memo[n] = r; return r

def rand_tree(n, rng):
    if n == 1: return "z" if rng.random() < 0.2 else "S"
    k = rng.randint(1, n - 1)
    return (rand_tree(k, rng), rand_tree(n - k, rng))

def subst(e, t):
    if e == "#": return t
    if e in ("S", "z"): return e
    return (subst(e[0], t), subst(e[1], t))
def get(u, p):
    for ch in p: u = u[int(ch)]
    return u
def put(u, p, v):
    if not p: return v
    return (put(u[0], p[1:], v), u[1]) if p[0] == "0" else (u[0], put(u[1], p[1:], v))
def postorder(u, p=""):
    if u in ("S", "z"): return []
    return postorder(u[0], p + "0") + postorder(u[1], p + "1") + [p]

def process(t):
    cur = t; v0 = evaluate([to_str(cur)])[0]
    for p in postorder(t):
        sub = get(cur, p)
        rep = parse_tuple(R[table[(cls(sub[0]), cls(sub[1]))]])
        nxt = put(cur, p, rep); v1 = evaluate([to_str(nxt)])[0]
        if v1 != v0:
            ctx = to_str(put(cur, p, "#"))
            if ctx not in E: E.append(ctx); return True
            return False
        cur = nxt
    return False

def main():
    rng = random.Random(4242)
    tests = [t for n in range(1, NTEST + 1) for t in all_trees(n)]
    test_v = evaluate([to_str(t) for t in tests])
    t0 = time.time()
    for it in range(100000):
        ok = close()
        F = [SIG[r][0] == 1 for r in R]
        if not ok: print(f"iter {it}: class limit exceeded ({len(R)})"); break
        rnd = [rand_tree(rng.randint(NTEST + 1, NTEST + 10), rng) for _ in range(NRAND)]
        rnd_v = evaluate([to_str(t) for t in rnd])
        bad = [t for t, v in zip(tests + rnd, test_v + rnd_v) if (v == 1) != F[cls(t)]]
        ctxs = [parse_tuple(e) for e in E]; reps = [parse_tuple(r) for r in R]
        for c in range(len(R)):
            for j, e in enumerate(ctxs):
                t = subst(e, reps[c])
                if (SIG[R[c]][j] == 1) != F[cls(t)]: bad.append(t)
        nR = len(R); found = 0
        for x in range(nR):
            if found >= 3: break
            for y in range(nR):
                if found >= 3: break
                for z in range(nR):
                    if table[(table[(table[(0, x)], y)], z)] != table[(table[(x, z)], table[(y, z)])]:
                        found += 1
                        X, Y, Z = reps[x], reps[y], reps[z]
                        T1, T2 = ((("S", X), Y), Z), ((X, Z), (Y, Z))
                        cand = [subst(e, T) for e in ctxs for T in (T1, T2)]
                        cv = evaluate([to_str(u) for u in cand])
                        bad += [u for u, v in zip(cand, cv) if (v == 1) != F[cls(u)]]
                        if found >= 3: break
        print(f"iter {it}: classes {len(R)} contexts {len(E)} counterexamples {len(bad)} oracle calls {ncalls} "
              f"({time.time() - t0:.0f}s)", flush=True)
        if not bad: break
        bad.sort(key=lambda u: len(to_str(u)))
        progress = False
        for t in bad[:8]:
            if process(t): progress = True
        if not progress: print("no progress — stopping"); break
    n = len(R)
    viol = sum(1 for x in range(n) for y in range(n) for z in range(n)
               if table[(table[(table[(0, x)], y)], z)] != table[(table[(x, z)], table[(y, z)])])
    print(f"final: classes {n}, contexts {len(E)}, S-identity violations {viol} of {n**3}", flush=True)
    with open(OUT, "w") as f:
        f.write(f"# lstar_z cap={CAP} classes={n} contexts={len(E)} sid_violations={viol} generators S=0 z=1\n")
        for c in range(n):
            f.write(f"class {c} HN={int(F[c])} count 1 ctxHN 0 rep {R[c]}\n")
        f.write("# product table (rows a, cols b: class of rep(a) rep(b)); new=0\n")
        for a in range(n): f.write(" ".join(str(table[(a, b)]) for b in range(n)) + "\n")
        f.write("# end\n# contexts\n" + "\n".join("# " + c for c in E) + "\n")

if __name__ == "__main__":
    main()
