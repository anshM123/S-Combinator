"""Phi-state structure of unique-redex runs (main agent, 2026-10-26).
Theorem UR's proof routes the run of t_0 through states Phi(c; R) = [c, S c, S c] ++ R. For each unique-redex term given,
this records the first element c_i at every Phi-state and tests whether one fixed context G (a term with one or more holes)
gives c_{i+s} = G[c_i] for all late i, with step s = 1 or 2 (runs whose Phi-states come in two interleaved sequences) —
i.e. whether the Phi-elements form a comb family, as in Theorem UR (c' = S q (S c)) — or, failing that, a context in the
two previous elements, c_{i+2} = G[c_{i+1}, c_i] (a second-order recurrence).
Usage: python ur_phi.py FILE [STEPS]   (FILE: output of unique_redex.py)"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from loop_prover import holeify, fill, HOLE

def phi_elements(src, N):
    hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; out = []
    for n in range(N):
        if len(stk) < 3 or len(hc.spine(stk[-2])[0]) >= 2: return out, False
        c, b2, b3 = stk[-1], stk[-2], stk[-3]
        if b2 == hc.app(0, c) and b3 == b2: out.append((n, c))
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return out, True

def comb_context(cs, step):
    """a context G with cs[i+step] = G[cs[i]] for every i in the second half of cs, or None"""
    if len(cs) < 2 * step + 4: return None
    i0 = len(cs) // 2
    G = holeify(cs[i0 + step], cs[i0], {})
    if G == cs[i0 + step] or G == HOLE: return None
    for i in range(i0, len(cs) - step):
        if fill(G, cs[i]) != cs[i + step]: return None
    return G

H1, H2 = -61, -62
def holeify2(t, s1, s2, memo):
    """t with occurrences of s1 replaced by H1 and then of s2 by H2 (s1 tried first at every node)"""
    if t == s1: return H1
    if t == s2: return H2
    if t <= 0: return t
    r = memo.get(t)
    if r is None:
        r = hc.app(holeify2(hc.L[t], s1, s2, memo), holeify2(hc.R[t], s1, s2, memo)); memo[t] = r
    return r
def fill2(G, x1, x2, memo=None):
    if memo is None: memo = {}
    if G == H1: return x1
    if G == H2: return x2
    if G <= 0: return G
    r = memo.get(G)
    if r is None: r = hc.app(fill2(hc.L[G], x1, x2, memo), fill2(hc.R[G], x1, x2, memo)); memo[G] = r
    return r
def pair_context(cs):
    """a context G with cs[i+2] = G[cs[i+1], cs[i]] for every i in the second half of cs, or None"""
    if len(cs) < 10: return None
    i0 = len(cs) // 2
    G = holeify2(cs[i0 + 2], cs[i0 + 1], cs[i0], {})
    if G in (H1, H2) or G == cs[i0 + 2]: return None
    for i in range(i0, len(cs) - 2):
        if fill2(G, cs[i + 1], cs[i]) != cs[i + 2]: return None
    return G

if __name__ == "__main__":
    path = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    terms = [l.split()[1] for l in open(path, encoding="utf-8") if len(l.split()) > 2 and l.split()[1].startswith("S")]
    kinds = collections.Counter(); ctxs = collections.Counter()
    for src in terms:
        ph, ur = phi_elements(src, N)
        cs = [c for n, c in ph]
        G1, G2 = comb_context(cs, 1), comb_context(cs, 2)
        G3 = pair_context(cs) if G1 is None and G2 is None else None
        kind = "step 1" if G1 is not None else "step 2" if G2 is not None else "pair" if G3 is not None else "none"
        kinds[(ur, kind)] += 1
        G = G1 if G1 is not None else G2 if G2 is not None else G3
        if G is not None: ctxs[hc.show(G).replace("a51", "[]").replace("a61", "[1]").replace("a62", "[2]")] += 1
        else: print(f"  no comb context: {src} (unique redex for {N} steps: {ur}, {len(cs)} Phi-states)")
    print(f"{len(terms)} terms; (unique redex for {N} steps, Phi-elements form a comb with step): {dict(kinds)}")
    print("contexts G (c' = G[c]):")
    for g, k in ctxs.most_common(12): print(f"  {k:4d}  {g}")
