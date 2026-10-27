"""Unique-redex runs via Theorem UR-Phi (main agent, 2026-10-26).
Theorem UR-Phi (PROOF.md). Let Bases be a set of normal forms such that each beta in Bases satisfies the base lemma
  BL(beta):  [beta, S x, S y] ++ R  ->*  Phi(S x (S y)) ++ R'     (x, y opaque normal forms, R never read, second
             element of spine <= 1 at every step),
where Phi(c) = [c, S c, S c]. Let C(Bases) be the least set containing Bases and closed under (p, q) -> S p (S q). Then
for every c = S p (S q) in C(Bases) and every list R of normal forms, the term with list Phi(c) ++ R has a unique redex at
every step for ever and passes through Phi(c_k) ++ R_k with c_0 = c and c_{k+1} = S q_m (S c_k), where q_m is found by
walking down c_k's left spine (p_i = S p_{i+1} (S q_{i+1}) until p_m is a base).
This script proves, term by term: (1) BL(beta) for every base met, symbolically; (2) the concrete run of the term keeps a
unique redex (all list elements normal forms, second element of spine <= 1) until a Phi-state Phi(c) with
c = S p (S q) in C(Bases); then Theorem UR-Phi gives the rest. Terms whose Phi-elements follow the other rule found,
c' = S c (S (S c)), are reported separately.
Usage: python ur_phi_proof.py FILE [MAXSTEPS]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from li_explore import has_redex
from ur_walk import form, walk

X, Y = -1, -2
JUNK = [-99, -98, -97, -96]

def phi(c): return [c, hc.app(0, c), hc.app(0, c)]

def base_lemma(beta, cap=400):
    """the base lemma on the head machine with opaque normal forms x, y: from [beta, S x, S y] ++ junk to the first
    Phi-state, keeping a unique redex and never reading the junk. Returns (kind, opcode word) with kind 'A' if that state
    is Phi(S x (S y)), 'II' if it is Phi(S y (S (S y))), or None"""
    Sx, Sy = hc.app(0, X), hc.app(0, Y)
    targets = {"A": hc.app(hc.app(0, X), Sy), "II": hc.app(hc.app(0, Y), hc.app(0, Sy))}
    stk = ([beta, Sx, Sy] + JUNK)[::-1]               # top of stack = first list element
    ops = []
    for n in range(cap):
        top = stk[::-1][:3]
        for kind, c2 in targets.items():
            if top == phi(c2): return kind, "".join(map(str, ops))
        a, b, c = stk[-1], stk[-2], stk[-3]
        if any(e in JUNK for e in (a, b, c)): return None
        bargs, bh = hc.spine(b)
        if bh != 0 or len(bargs) >= 2: return None    # second element: an atom (unknown spine) or spine >= 2
        args, h = hc.spine(a)
        if h != 0: return None                        # an opaque head would be opened
        del stk[-3:]
        stk.append(hc.app(b, c)); stk.append(c); stk.extend(reversed(args)); ops.append(len(args))
    return None

def p_chain_base(c):
    """the base where the walk down c's p-chain stops (c = S p (S q), p = S p' (S q'), ...), or None"""
    if form(c) is None: return None
    p = form(c)[0]
    while form(p) is not None: p = form(p)[0]
    return p

def in_closure(c, bases, memo):
    if c in bases: return True
    r = memo.get(c)
    if r is None:
        pq = form(c)
        r = pq is not None and in_closure(pq[0], bases, memo) and in_closure(pq[1], bases, memo)
        memo[c] = r
    return r

def prove_term(src, maxsteps, bl_cache):
    """concrete run with unique-redex checks until a Phi-state covered by Theorem UR-Phi (type-A bases: c in the closure
    C(bases) under S p (S q), p, q in C) or Theorem UR-Phi-II (c's p-chain ends at a type-II base)"""
    hc_t = hc.from_tuple(parse(src))
    args, h = hc.spine(hc_t)
    if len(args) < 3 or any(has_redex(e) for e in args): return "not unique-redex at the start", None
    stk = args[::-1]
    for n in range(maxsteps):
        if len(stk) < 3: return "head normal form", None
        if len(hc.spine(stk[-2])[0]) >= 2: return f"second redex at step {n}", None
        c = stk[-1]
        if stk[-2] == hc.app(0, c) and stk[-3] == stk[-2] and form(c) is not None:
            beta = p_chain_base(c)
            bl = bl_cache.setdefault(beta, base_lemma(beta))
            if bl is not None and bl[0] == "II":
                return f"PROVED by UR-Phi-II (Phi-state at step {n}, base lemma {bl[1]})", {beta}
            bases, todo = set(), [c]
            while todo:
                t = todo.pop()
                pq = form(t)
                if pq is None: bases.add(t)
                else: todo.extend(pq)
            ok = all((bl_cache.setdefault(b, base_lemma(b)) or ("", ""))[0] == "A" for b in bases)
            if ok and in_closure(c, bases, {}):
                return f"PROVED by UR-Phi (Phi-state at step {n}, {len(bases)} base(s))", bases
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return "no certified Phi-state", None

if __name__ == "__main__":
    path = sys.argv[1]; maxsteps = int(sys.argv[2]) if len(sys.argv) > 2 else 5000
    terms = [l.split()[1] for l in open(path, encoding="utf-8") if len(l.split()) > 2 and l.split()[1].startswith("S")]
    res = collections.Counter(); bl_cache = {}; other = []
    for src in terms:
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear(); bl_cache.clear()
        st, bases = prove_term(src, maxsteps, bl_cache)
        res[st.split(" (")[0]] += 1
        if not st.startswith("PROVED"): other.append((src, st))
    print(f"{path}: {len(terms)} terms — " + ", ".join(f"{v} {k}" for k, v in res.most_common()))
    for s, st in other: print(f"  {s}: {st}")
