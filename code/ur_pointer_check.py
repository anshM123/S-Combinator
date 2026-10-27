"""Machine check of the pointer-transition lemmas behind Theorem UR-C (main agent, 2026-10-26).
For a Φ-element c write w(c) for its walk (left-spine layers: 1 = S x, (2, t) = S x t), m(c) for its number of type-1
layers, and z(c) for its pointer: Ψ(c) = S c if m = 0, else Ψ(c) = S z X with X = S^(m−1)(S c), where S z is the u
before the last type-1 step — the t of the preceding type-2 layer, v_(m−2) = S^(m−2)(S c) if the last two type-1 layers
are consecutive, or S c if the last type-1 layer is the first layer of the walk.
Predicted transitions (PROOF.md, Theorem UR-C):
  T0  m(c_k) = 0                      -> m(c_{k+1}) = 1, last type-1 layer at position 0, z(c_{k+1}) = c_{k+1};
  T1  m(c_k) >= 1, w(z_k) starts with 1 -> m(c_k) = 1 (else the run dies two rounds later), m(c_{k+1}) = 1,
                                          z(c_{k+1}) = c_k;
  T2  m(c_k) >= 1, w(z_k) starts with 2 -> m(c_{k+1}) = m(z_k) and z(c_{k+1}) is the inherited predecessor pointer of
                                          w(z_k) — a proper subterm of z_k — or the self pointer (consecutive layers).
Also checked: c_{k+1} = S c_k or S z_k X_k, and the eventual regime (type A: m = 1 with the period-2 alternation
z_{i+2j+1} = β fixed; type II: m = 2 consecutive, self pointer) reached after finitely many rounds.
Usage: python ur_pointer_check.py real FILE [ROUNDS] | sample N ROUNDS SEED"""
import sys, collections, random
sys.setrecursionlimit(1000000)
import hc
from symb import parse

def walk(x):
    out = []
    while x != 0:
        args, h = hc.spine(x)
        out.append((1, None) if len(args) == 1 else (2, args[1])); x = args[0]
    return out

def S_pow(j, x):
    for _ in range(j): x = hc.app(0, x)
    return x

def subterm(a, b):
    """a is a proper subterm of b"""
    seen = set(); todo = [b]
    while todo:
        x = todo.pop()
        if x <= 0 or x in seen: continue
        seen.add(x)
        for y in (hc.L[x], hc.R[x]):
            if y == a: return True
            todo.append(y)
    return False

def analyse(c):
    """(m, kind, z) of the Φ-round on c: kind in {'none', 'pos0', 'pred', 'cons'}"""
    w = walk(c); ones = [i for i, (ty, t) in enumerate(w) if ty == 1]; m = len(ones)
    if m == 0: return 0, "none", None
    p = ones[-1]
    if p == 0: return m, "pos0", c
    ty, t = w[p - 1]
    if ty == 1: return m, "cons", (c if m == 2 else S_pow(m - 3, hc.app(0, c)))
    args, h = hc.spine(t)
    return m, "pred", args[0]

def check_orbit(cs, stats):
    """cs: consecutive Φ-elements of one run (all rounds valid)"""
    ok = True
    for k in range(len(cs) - 1):
        c, c1 = cs[k], cs[k + 1]
        m, kind, z = analyse(c); m1, kind1, z1 = analyse(c1)
        if m == 0:
            good = c1 == hc.app(0, c) and m1 == 1 and kind1 == "pos0" and z1 == c1; rule = "T0"
        else:
            good = c1 == hc.app(hc.app(0, z), S_pow(m - 1, hc.app(0, c)))
            wz = walk(z)
            if wz and wz[0][0] == 1:
                rule = "T1"; good &= m == 1 and m1 == 1 and z1 == c
            else:
                rule = "T2"
                mz = sum(1 for ty, t in wz if ty == 1)
                good &= m1 == mz
                if kind1 == "pred": good &= subterm(z1, z)
                elif kind1 == "cons": good &= z1 == (c1 if m1 == 2 else S_pow(m1 - 3, hc.app(0, c1)))
                elif kind1 == "none": good &= mz == 0
                else: good = False
        stats[rule] += 1; stats[rule + " ok"] += good; ok &= good
    # eventual regime on the second half
    tail = [analyse(c) for c in cs[len(cs) // 2:]]
    if all(m == 2 and kind == "cons" for m, kind, z in tail): stats["type II"] += 1
    elif all(m == 1 for m, kind, z in tail):
        odd = {z for i, (m, kind, z) in enumerate(tail) if i % 2 == 0}
        even = {z for i, (m, kind, z) in enumerate(tail) if i % 2 == 1}
        stats["type A" if len(odd) == 1 or len(even) == 1 else "type A without fixed base"] += 1
    else: stats["other"] += 1
    return ok

def real_orbits(path, R):
    terms = [l.split()[1] for l in open(path, encoding="utf-8") if len(l.split()) > 2 and l.split()[1].startswith("S")]
    for src in terms:
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
        args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; cs = []; prev = None
        for n in range(200000):
            if len(stk) < 3 or len(cs) > R: break
            if prev == 0 and stk[-2] == hc.app(0, stk[-1]) and stk[-3] == stk[-2]: cs.append(stk[-1])
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch)); prev = len(ch)
        yield src, cs

def sampled_orbits(n, R, seed):
    import ur_psi_explore as ex
    rng = random.Random(seed)
    for i in range(n):
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
        c = ex.rand_phi_element(rng, rng.randint(1, 8)); cs = [c]
        for k in range(R):
            r = ex.psi(c)
            if r is None: break
            c = r[0]; cs.append(c)
        if len(cs) == R + 1: yield i, cs

if __name__ == "__main__":
    stats = collections.Counter(); bad = []
    if sys.argv[1] == "real":
        R = int(sys.argv[3]) if len(sys.argv) > 3 else 60
        gen = real_orbits(sys.argv[2], R)
    else:
        gen = sampled_orbits(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    n = 0
    for name, cs in gen:
        n += 1
        if not check_orbit(cs, stats): bad.append(name)
    print(f"{n} orbits; transitions: " + ", ".join(f"{r} {stats[r + ' ok']}/{stats[r]}" for r in ("T0", "T1", "T2")))
    print(f"eventual regime: type A {stats['type A']}, type II {stats['type II']}, "
          f"type A without fixed base {stats['type A without fixed base']}, other {stats['other']}")
    print("ALL TRANSITIONS AS PREDICTED" if not bad else f"MISMATCH in {len(bad)} orbits, e.g. {bad[:3]}")
