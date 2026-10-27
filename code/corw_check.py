"""Random exact checks for two disprover statements.

(U*) Theorem U survives zero tests. Data = elements containing a MARKED closed occurrence (marks: ('M', tag, term));
opening a marked occurrence at the front pushes its children UNMARKED (the 'zero test' of a counter base). If the initial
list satisfies F1 (no data element directly above a closed one) and F2 (no spine of any subterm has a data argument
directly followed by a closed one), every later list does.
(W) No writing behind a live control. Two colours x (above) and y; initial list F1/F2 and J1/J2 (Lemma 10: no element
containing y above an element containing x but not y, and the same inside every spine). Then a clean write b.c
(b closed at position 2, c containing y at position 3) never happens while some list element contains x but not y.
Usage: python corw_check.py TRIALS STEPS SEED
"""
import sys, random
sys.setrecursionlimit(100000)

def is_mark(t): return isinstance(t, tuple) and len(t) == 3 and t[0] == "M"

def spine(t):
    args = []
    while isinstance(t, tuple) and not is_mark(t):
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args          # head: 'S' or a mark

def tags(t, memo):
    if t == "S": return frozenset()
    k = id(t)
    if k in memo: return memo[k]
    r = (frozenset([t[1]]) | tags(t[2], memo)) if is_mark(t) else tags(t[0], memo) | tags(t[1], memo)
    memo[k] = r; return r

def full_spine(t):
    """head S and the FULL spine: marks on the left spine are looked through (audit 7 fix)"""
    args = []
    while True:
        if isinstance(t, tuple) and not is_mark(t):
            args.append(t[1]); t = t[0]
        elif is_mark(t):
            t = t[2]
        else:
            break
    args.reverse(); return t, args

def open_top(a):
    """opening consumes every mark on a's left spine and exposes the full spine (nested marks included)"""
    return full_spine(a)[1]

def f1f2(K, memo):
    d = [bool(tags(e, memo)) for e in K]
    if any(d[i] and not d[i + 1] for i in range(len(K) - 1)): return False
    seen = set(); stack = list(K)
    while stack:
        t = stack.pop()
        if t == "S" or id(t) in seen: continue
        seen.add(id(t))
        if is_mark(t): stack.append(t[2]); continue
        h, args = full_spine(t)
        dd = [bool(tags(a, memo)) for a in args]
        if any(dd[i] and not dd[i + 1] for i in range(len(args) - 1)): return False
        stack.extend(args)
        u = t                                    # also visit marked terms sitting on the left spine
        while isinstance(u, tuple):
            if is_mark(u): stack.append(u[2]); break
            u = u[0]
    return True

def j_ok(seq, memo):
    """J on one list: no element containing y above an element containing x but not y"""
    seen_y = False
    for e in seq:
        tg = tags(e, memo)
        if "x" in tg and "y" not in tg and seen_y: return False
        if "y" in tg: seen_y = True
    return True

def j1j2(K, memo):
    if not j_ok(K, memo): return False
    seen = set(); stack = list(K)
    while stack:
        t = stack.pop()
        if t == "S" or id(t) in seen: continue
        seen.add(id(t))
        if is_mark(t): stack.append(t[2]); continue
        h, args = full_spine(t)
        if not j_ok(args, memo): return False
        stack.extend(args)
        u = t
        while isinstance(u, tuple):
            if is_mark(u): stack.append(u[2]); break
            u = u[0]
    return True

def rand_term(n, rng):
    if n == 1: return "S"
    k = rng.randint(1, n - 1)
    return (rand_term(k, rng), rand_term(n - k, rng))

def rand_marked(n, rng, tagp):
    """random term where some subterms are wrapped as marked occurrences"""
    if n == 1:
        return ("M", rng.choice(tagp), "S") if rng.random() < 0.15 else "S"
    k = rng.randint(1, n - 1)
    t = (rand_marked(k, rng, tagp), rand_marked(n - k, rng, tagp))
    if rng.random() < 0.08:
        inner = rand_marked(rng.randint(1, 6), rng, tagp) if rng.random() < 0.3 else rand_term(rng.randint(1, 6), rng)
        t = ("M", rng.choice(tagp), inner)
    return t

if __name__ == "__main__":
    trials, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    stat = {"U_runs": 0, "U_steps": 0, "U_viol": 0, "zero_tests": 0, "W_runs": 0, "W_steps": 0, "W_viol": 0,
            "writes_on_y": 0}
    tries = 0
    while stat["U_runs"] < trials and tries < 200 * trials:
        tries += 1
        tagp = ["x", "y"]
        K = [rand_marked(rng.randint(1, 12), rng, tagp) for _ in range(rng.randint(3, 7))]
        memo = {}
        if not any(tags(e, memo) for e in K) or not f1f2(K, memo): continue
        wcase = j1j2(K, memo)
        stat["U_runs"] += 1; stat["W_runs"] += wcase
        for n in range(steps):
            if len(K) < 3: break
            memo = {}
            a, b, c = K[0], K[1], K[2]
            h, _ = spine(a)
            if is_mark(h): stat["zero_tests"] += 1
            if wcase and not tags(b, memo) and "y" in tags(c, memo):
                stat["writes_on_y"] += 1
                if any("x" in tags(e, memo) and "y" not in tags(e, memo) for e in K):
                    stat["W_viol"] += 1
            K = open_top(a) + [c, (b, c)] + K[3:]
            memo = {}
            stat["U_steps"] += 1
            if not f1f2(K, memo):
                stat["U_viol"] += 1; break
            if wcase:
                stat["W_steps"] += 1
                if not j1j2(K, memo): stat["W_viol"] += 1; break
    print(stat)
