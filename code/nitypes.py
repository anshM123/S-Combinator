"""Canonical non-idempotent intersection-type derivations of head-normalising S-terms.

Types: 'ok' (value / head normal form) or ('a', M, R) = M -> R, M a multiset (sorted tuple) of types.
S-axiom types: ok, [] -> ok, [] -> [] -> ok, and [[M1 -> [C1..Ck] -> B]] -> [N1->C1, ..., Nk->Ck] -> (M1+N1+...+Nk) -> B.
A typing derivation of a closed term is finite; each head step S a b c -> a c (b c) removes the S axiom and three
application nodes and adds 2 + k application nodes, so with S-axiom weight w = 6 + 2k + |M1| + sum|Ni| the derivation
weight strictly decreases: typable with ok  =>  head normalising (works for recursive types too).

This script builds the canonical derivation of every M35-F term by subject expansion along its head run (provenance
machine of opencount.py) and reports the types given to subterm occurrences, grouped by M35 class.
Usage: python nitypes.py NMAX
"""
import sys, collections
from opencount import cl, F, number, reps
from symb import trees, show

OK = "ok"
def arrow(M, R):
    return ("a", tuple(sorted(M, key=repr)), R)

def run_configs(t, budget):
    root, kids, leaf = number(t)
    conf = [(c, ()) for c in kids[root]]                     # top first
    steps = []
    while len(conf) >= 3 and len(steps) < budget:
        a, b, c = conf[0], conf[1], conf[2]
        opened = [(k, ()) for k in kids[a[0]]] + list(a[1])
        steps.append(len(opened))
        conf = opened + [c, (b[0], b[1] + (c,))] + conf[3:]
    return root, kids, steps, conf

def derive(t, budget=400):
    """canonical derivation: returns (root, kids, per-element derivation lists of the initial configuration, head type)"""
    root, kids, steps, final = run_configs(t, budget)
    if len(final) >= 3:
        return None
    L = [() for _ in final]                                  # final hnf: components untyped
    for p in reversed(steps):
        Ds_c_own, Ds_bc, R = L[p], L[p + 1], L[p + 2:]
        def types(Ds): return [D[0] for D in Ds]
        tail = OK
        for Ds in reversed(L[p + 2:]):
            tail = arrow(types(Ds), tail)
        tau_a = arrow(types(Ds_c_own), arrow(types(Ds_bc), tail))
        D_a = (tau_a, tuple(L[:p]))
        Ds_b = tuple((arrow(types(D[1][-1]), D[0]), D[1][:-1]) for D in Ds_bc)
        Ds_c = tuple(Ds_c_own) + tuple(x for D in Ds_bc for x in D[1][-1])
        L = [(D_a,), Ds_b, Ds_c] + list(R)
    return root, kids, L

def occurrence_types(t):
    """(subterm, type) for every typed occurrence, with multiplicity: every node of the binary tree, including the
    head S leaves and the partial applications on each left spine"""
    res = derive(t)
    if res is None:
        return None
    root, kids, L = res
    out = []
    stack = [(t, (OK, tuple(L)))]          # derivation = (type, per-spine-argument derivation lists)
    while stack:
        u, (T, args) = stack.pop()
        out.append((u, T))
        if u == "S":
            assert not args
            continue
        last = args[-1]
        stack.append((u[0], (arrow([D[0] for D in last], T), args[:-1])))
        for D in last:
            stack.append((u[1], D))
    return out

def depth(T):
    if T == OK: return 0
    return 1 + max([depth(T[2])] + [depth(A) for A in T[1]])

def show_type(T):
    if T == OK: return "o"
    return "[" + ",".join(show_type(A) for A in T[1]) + "]>" + show_type(T[2])

if __name__ == "__main__":
    NMAX = int(sys.argv[1])
    per_class = collections.defaultdict(set)
    for n in range(1, NMAX + 1):
        mult = collections.Counter(); dmax = 0; ntyped = 0
        for t in trees(n):
            if not F[cl(t)]: continue
            occ = occurrence_types(t)
            assert occ is not None, show(t)
            ntyped += 1
            cnt = collections.Counter()
            for u, T in occ:
                per_class[cl(u)].add(T); dmax = max(dmax, depth(T))
                cnt[id(u) if u != "S" else None] += 0
            # multiplicity of types per occurrence is the number of derivation nodes on it
        alltypes = set().union(*per_class.values())
        sizes = sorted(((len(v), k) for k, v in per_class.items()), reverse=True)[:6]
        print(f"n={n}: F-terms {ntyped}; distinct types so far {len(alltypes)}; max depth {dmax}; "
              f"largest per-class type sets (size, class) {sizes}", flush=True)
