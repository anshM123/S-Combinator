"""Kinds of elements in generic loop-iteration runs (main agent). Kind letters: 0 = S-only code, a = A itself,
T = transformed (over A, S, contains A, not A), x = contains X, z = contains Z or J but not X, r = tape atom.
For every element of every list (all bodies <= NMAX leaves), record (kind, kinds of its spine arguments with runs of
code collapsed to '0+'), and every adjacent pair of list kinds. Prints the observed sets."""
import sys, collections, re
sys.setrecursionlimit(100000)
from symb import trees
import hc
NMAX, CAP = (int(sys.argv[1]), int(sys.argv[2])) if __name__ == '__main__' else (0, 0)
X, Z, A, J = -1, -2, -3, -4
memo = {}
def bits(i):
    if i in memo: return memo[i]
    if i == 0: k = 0
    elif i == X: k = 1
    elif i in (Z, J): k = 2
    elif i == A: k = 4
    elif i < 0: k = 8
    else: k = bits(hc.L[i]) | bits(hc.R[i])
    memo[i] = k; return k
def kind(i):
    if i == A: return "a"
    b = bits(i)
    if b & 8: return "r"
    if b & 1: return "x"
    if b & 2: return "z"
    if b & 4: return "T"
    return "0"
def spine_kinds(i):
    if i <= 0: return "atom" if i < 0 else "S"
    args, h = hc.spine(i)
    s = "".join(kind(e) for e in args)
    return ("h=" + ("S" if h == 0 else kind(h))) + ":" + re.sub("0+", "0+", s)
elem = collections.Counter(); pairs = collections.Counter(); lists = collections.Counter()
if __name__ == "__main__":
 for n in range(1, NMAX + 1):
     for t in trees(n):
         P = hc.from_tuple(t); stk = [-7, -6, -5, J, A, Z, X, P]
         for step in range(CAP):
             lst = stk[::-1]
             ks = [kind(e) for e in lst]
             for e, k in zip(lst, ks):
                 if k in ("x", "T", "a") or (k == "z" and e > 0): elem[(k, spine_kinds(e))] += 1
             for u, v in zip(ks, ks[1:]): pairs[u + v] += 1
             lists[re.sub("0+", "0+", "".join(ks).rstrip("r"))[:30]] += 1
             a = stk[-1]; args, h = hc.spine(a)
             if h != 0 or len(stk) < 4: break
             stk.pop(); bb = stk.pop(); cc = stk.pop()
             stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
 print("adjacent kind pairs (above, below):", sorted(pairs))
 print("element kinds with spine patterns (most common 40):")
 for (k, sp), c in elem.most_common(40): print(f"  {k}  {sp:30s} {c}")
 print("number of distinct list-kind patterns:", len(lists))
 for p, c in lists.most_common(25): print(f"  {p:32s} {c}")
