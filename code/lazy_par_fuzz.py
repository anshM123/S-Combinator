"""Randomised differential tests of the parallel machinery (main agent, 2026-10-26).
(1) Lemma LZ machine: for random S-terms, the lazy parallel opcode word (lazy_par.py) equals the word of direct
    ReplaceAll passes (par_vs_head.capped_pass), for as many passes as the direct computation fits under a node cap.
(2) Canonical aging (par_loop_prover2.ParEng2.age, the rule both lazy-representation provers use): for random terms x and
    k, the representation age(x, k) — with every DK_j·y node evaluated by j direct passes — equals P^k(x) computed by k
    direct passes.
Usage: python lazy_par_fuzz.py NTERMS PASSES SEED"""
import sys, random
sys.setrecursionlimit(1000000)
import hc
import lazy_par as lz
from par_vs_head import capped_pass, Overflow

def rand_term(rng, leaves):
    if leaves == 1: return "S"
    k = rng.randint(1, leaves - 1)
    return (rand_term(rng, k), rand_term(rng, leaves - k))

def show(t):
    if t == "S": return "S"
    f, x = t
    xs = show(x)
    return show(f) + (xs if x == "S" else "(" + xs + ")")

def direct_word(t, N, cap):
    hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
    x = hc.from_tuple(t); ops = []
    for n in range(N):
        args, h = hc.spine(x)
        if len(args) < 3: return ops, "hnf"
        ops.append(len(hc.spine(args[0])[0]))
        try:
            x = capped_pass(cap)(x)
        except Overflow:
            return ops, "cap"
    return ops, "done"

def check_machine(rng, n_terms, N, cap=300_000):
    agree = total_passes = 0; bad = []
    for i in range(n_terms):
        t = rand_term(rng, rng.randint(6, 18))
        d, why = direct_word(t, N, cap)
        lz.reset(); l = lz.par_ops(show(t), len(d))
        if l[:len(d)] == d and (why != "hnf" or len(l) == len(d)): agree += 1
        else: bad.append(show(t))
        total_passes += len(d)
    return agree, total_passes, bad

def check_aging(rng, n_cases, cap=300_000):
    import par_loop_prover2 as p2
    from loop_prover import Fail
    def interpret(x):
        """an hc pattern with DK nodes -> the plain term it denotes (DK_j·y = j direct passes of y)"""
        if x <= 0: return x
        args, h = hc.spine(x)
        if p2.is_dk(h):
            y = interpret(args[0])
            for _ in range(p2.dk_k(h)): y = capped_pass(cap)(y)
            r = y
            for a in args[1:]: r = hc.app(r, interpret(a))
            return r
        r = h
        for a in args: r = hc.app(r, interpret(a))
        return r
    ok = tried = 0; bad = []
    for i in range(n_cases):
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear(); p2.plp._nf.clear()
        t = hc.from_tuple(rand_term(rng, rng.randint(4, 14))); k = rng.randint(1, 12)
        try:
            eng = p2.ParEng2(); rep = eng.age(t, k)
            if isinstance(rep, tuple): continue               # (cannot happen for concrete terms)
            got = interpret(rep)
            want = t
            for _ in range(k): want = capped_pass(cap)(want)
        except (Overflow, Fail):
            continue
        tried += 1
        if got == want: ok += 1
        else: bad.append((k, hc.show(t)))
    return ok, tried, bad

if __name__ == "__main__":
    n, N, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    a, tp, bad = check_machine(rng, n, N)
    print(f"lazy machine = direct passes: {a}/{n} random terms ({tp} passes compared){'; differ: ' + ', '.join(bad[:5]) if bad else ''}")
    ok, tried, bad2 = check_aging(rng, n)
    print(f"canonical aging = direct passes: {ok}/{tried} random (term, k) cases{'; differ: ' + str(bad2[:3]) if bad2 else ''}")
    print("ALL CHECKS PASS" if not bad and not bad2 and tried > 0 else "SOME CHECK FAILS")
