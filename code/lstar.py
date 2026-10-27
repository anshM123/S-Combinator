"""Angluin-style learner of a finite S-model (magma) for a Böhm-tree language of closed S-terms.

Classes = signatures over a growing set E of one-hole contexts; representatives R have distinct signatures; the
product table maps (class a, class b) to the class of rep(a) rep(b). A counterexample t (model verdict ≠ oracle verdict)
is reduced by replacing innermost subterms with their representatives one at a time (post-order): the first replacement
that flips the oracle verdict exhibits a context separating a product of representatives from its representative; that
context is added to E. Signatures are stored per term and extended column by column when E grows. Oracle calls are
batched through `sterm evalfile` in parallel processes.

usage: python lstar.py ORACLE CAP NTEST NRAND OUTFILE [MAXCLASSES]   (ORACLE 1 = BT finite, 2 = BT has no bottom)
"""
import os, sys, random, subprocess, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
STERM = os.path.join(HERE, "sterm15.exe")
NPROC = 20
ORACLE, CAP = int(sys.argv[1]), int(sys.argv[2])
NTEST, NRAND, OUT = int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
MAXCLS = int(sys.argv[6]) if len(sys.argv) > 6 else 2000
WORK = tempfile.mkdtemp(prefix="lstar_")
ncalls = 0
unknown_seen = 0

def to_str(t):
    if t == "S" or t == "#": return t
    a = t[1]
    return to_str(t[0]) + (to_str(a) if a in ("S", "#") else "(" + to_str(a) + ")")

def parse_tuple(s):
    pos = [0]
    def atom():
        c = s[pos[0]]
        if c == "(":
            pos[0] += 1; t = term(); pos[0] += 1; return t
        pos[0] += 1; return "S" if c == "S" else "#"
    def term():
        t = atom()
        while pos[0] < len(s) and s[pos[0]] != ")": t = (t, atom())
        return t
    return term()

def fill(c, s): return c.replace("#", "(" + s + ")")
def app(a, b): return a + (b if b == "S" else "(" + b + ")")

def evaluate(strs):
    """oracle verdicts for a list of term strings (parallel batches, no global cache)"""
    global ncalls, unknown_seen
    if not strs: return []
    uniq = list(dict.fromkeys(strs))
    ncalls += len(uniq)
    k = max(1, min(NPROC, len(uniq) // 300 + 1))
    procs = []
    for i in range(k):
        chunk = uniq[i::k]
        fin, fout = os.path.join(WORK, f"in{i}.txt"), os.path.join(WORK, f"out{i}.txt")
        with open(fin, "w") as f: f.write("\n".join(chunk) + "\n")
        procs.append((subprocess.Popen([STERM, "evalfile", str(ORACLE), str(CAP), fin, fout],
                                       stdout=subprocess.DEVNULL), fout))
    res = {}
    for p, fout in procs:
        p.wait()
        for line in open(fout):
            r, s = line.rstrip("\n").split(" ", 1)
            res[s] = int(r)
    out = [res[s] for s in strs]
    unknown_seen += sum(1 for v in out if v < 0)
    return out

R = ["S"]            # representatives (strings)
E = ["#"]            # contexts
SIG = {}             # term string -> list of verdicts (len == len(E) after sync)
PROD = {}            # (a, b) -> product string
table = {}
sig_of = {}

def sync(terms):
    """make SIG[t] cover all contexts for each t in terms"""
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
        sig_of = {}
        newR = []
        for r in R:
            k = tuple(SIG[r])
            if k not in sig_of: sig_of[k] = len(newR); newR.append(r)
        if len(newR) != len(R): raise RuntimeError("representatives merged — inconsistent oracle")
        R = newR
        pairs = [(a, b) for a in range(len(R)) for b in range(len(R))]
        for a, b in pairs:
            if (a, b) not in PROD: PROD[(a, b)] = app(R[a], R[b])
        sync([PROD[p] for p in pairs])
        added = 0
        table = {}
        for a, b in pairs:
            k = tuple(SIG[PROD[(a, b)]])
            if k not in sig_of:
                sig_of[k] = len(R); R.append(PROD[(a, b)]); added += 1
            table[(a, b)] = sig_of[k]
        if added == 0 or len(R) > MAXCLS: return added == 0

def cls(t):
    if t == "S": return 0
    return table[(cls(t[0]), cls(t[1]))]

def all_trees(n, memo={}):
    if n in memo: return memo[n]
    r = ["S"] if n == 1 else [(l, rr) for i in range(1, n) for l in all_trees(i) for rr in all_trees(n - i)]
    memo[n] = r; return r

def rand_tree(n, rng):
    if n == 1: return "S"
    k = rng.randint(1, n - 1)
    return (rand_tree(k, rng), rand_tree(n - k, rng))

def subst(e, t):
    if e == "#": return t
    if e == "S": return "S"
    return (subst(e[0], t), subst(e[1], t))

def get(u, p):
    for ch in p: u = u[int(ch)]
    return u
def put(u, p, v):
    if not p: return v
    return (put(u[0], p[1:], v), u[1]) if p[0] == "0" else (u[0], put(u[1], p[1:], v))
def postorder(u, p=""):
    if u == "S": return []
    return postorder(u[0], p + "0") + postorder(u[1], p + "1") + [p]

def process(t):
    cur = t
    v0 = evaluate([to_str(cur)])[0]
    for p in postorder(t):
        sub = get(cur, p)
        rep = parse_tuple(R[table[(cls(sub[0]), cls(sub[1]))]])
        nxt = put(cur, p, rep)
        v1 = evaluate([to_str(nxt)])[0]
        if v1 < 0: return False
        if v1 != v0:
            ctx = to_str(put(cur, p, "#"))
            if ctx not in E:
                E.append(ctx); return True
            return False
        cur = nxt
    return False

def main():
    rng = random.Random(12345)
    tests = [t for n in range(1, NTEST + 1) for t in all_trees(n)]
    test_v = evaluate([to_str(t) for t in tests])
    t0 = time.time()
    for it in range(10000):
        ok = close()
        F = [SIG[r][0] == 1 for r in R]
        if not ok:
            print(f"iter {it}: class limit exceeded ({len(R)})"); break
        rnd = [rand_tree(rng.randint(NTEST + 1, NTEST + 8), rng) for _ in range(NRAND)]
        rnd_v = evaluate([to_str(t) for t in rnd])
        bad = [t for t, v in zip(tests + rnd, test_v + rnd_v) if v >= 0 and (v == 1) != F[cls(t)]]
        # (a) the table must reproduce its own observations: e[R[c]] for every context e in E
        ctxs = [parse_tuple(e) for e in E]
        reps = [parse_tuple(r) for r in R]
        for c in range(len(R)):
            for j, e in enumerate(ctxs):
                t = subst(e, reps[c])
                if (SIG[R[c]][j] == 1) != F[cls(t)]: bad.append(t)
        # (b) S-identity violations: S x y z and x z (y z) are convertible, so some context in E mispredicts one side
        nR = len(R); found = 0
        for x in range(nR):
            for y in range(nR):
                for z in range(nR):
                    if found >= 3: break
                    if table[(table[(table[(0, x)], y)], z)] != table[(table[(x, z)], table[(y, z)])]:
                        found += 1
                        X, Y, Z = reps[x], reps[y], reps[z]
                        T1, T2 = ((("S", X), Y), Z), ((X, Z), (Y, Z))
                        cand = [subst(e, T) for e in ctxs for T in (T1, T2)]
                        cv = evaluate([to_str(u) for u in cand])
                        bad += [u for u, v in zip(cand, cv) if v >= 0 and (v == 1) != F[cls(u)]]
        print(f"iter {it}: classes {len(R)} contexts {len(E)} counterexamples {len(bad)} "
              f"oracle calls {ncalls} unknown {unknown_seen} ({time.time() - t0:.0f}s)", flush=True)
        if not bad: break
        bad.sort(key=lambda u: len(to_str(u)))
        progress = False
        for t in bad[:8]:
            if process(t): progress = True
        if not progress:
            print("no progress from counterexamples — stopping"); break
    n = len(R)
    viol = sum(1 for x in range(n) for y in range(n) for z in range(n)
               if table[(table[(table[(0, x)], y)], z)] != table[(table[(x, z)], table[(y, z)])])
    print(f"final: classes {n}, contexts {len(E)}, S-identity violations {viol} of {n**3}", flush=True)
    with open(OUT, "w") as f:
        f.write(f"# lstar oracle={ORACLE} cap={CAP} classes={n} contexts={len(E)} sid_violations={viol}\n")
        for c in range(n):
            f.write(f"class {c} HN={int(F[c])} count 1 ctxHN 0 rep {R[c]}\n")
        f.write("# product table (rows a, cols b: class of rep(a) rep(b)); new=0\n")
        for a in range(n): f.write(" ".join(str(table[(a, b)]) for b in range(n)) + "\n")
        f.write("# end\n")
        f.write("# contexts\n" + "\n".join("# " + c for c in E) + "\n")

if __name__ == "__main__":
    main()
