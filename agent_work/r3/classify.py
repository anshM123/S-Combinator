"""R3 agent: classify real proper position-3 phase-2 transfers for the new general argument.
usage: classify.py N            (all right combs over p with closed wrappers, <= N leaves, S-headed)
       classify.py t NK WK NT   (targeted family K.T, K <= NK, wrappers <= WK, tail <= NT)
       classify.py o N          (all S-headed ordered 1-hole contexts G[p], <= N leaves)
Classes (first that applies):
  FH    some wrapper p-/frozen-headed, or leftmost path of some wrapper reaches p/frozen (FH, FH1, FHL)
  I-V   phase 2 opens a V-prefixed element before its transfer (GCL: phase 3 has no p'-front at all)
  S-IIa single wrapper, pattern alpha (glue [c0, w, y]), no (w.y)-prefixed front in phase 2
  S-IIb single wrapper, pattern beta (glue [a1, w, y], a1 != c0), no (w.y)-prefixed front
  M-*   multi-wrapper, the same split for the innermost level Ln = vn.y (I-Ln: phase 2 opens an Ln-prefixed element)
Checks: in class I-V phase 3 must have no p'-front at all; phase 3 outcome recorded for every class."""
import sys, os, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, phase2_general as pg
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
FROZSET = set(c3.FROZ)
def pre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
def lp_reaches(t):
    while True:
        h = hm.head(t)
        if h == P or h in FROZSET: return True
        if h != 0: return False
        a, _ = hm.spine(t)
        if not a: return False
        t = a[0]
def phase3(V, budget=3000):
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    st = [Rr, Y, X, D3]; pf = 0
    for t in range(budget):
        if len(st) < 3: return "hnf", pf
        h = hm.head(st[-1])
        if h != 0:
            if h == P:
                pf += 1
                return ("p'-front PROPER" if T3.S3.proper(st[-3]) else "p'-front nonproper"), pf
            if h == C: return "reexec", pf
            return "call", pf
        hm.step(st)
    return "budget", pf
def classify(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    multi = "S" if len(ws) == 1 else "M"
    o3 = phase3(V)[0]
    if any(lp_reaches(w) for w in ws): return ("FH", multi, o3)
    if any(pre(L[-1], V) for L in hist): return ("I-V", multi, o3)
    vn = ws[-1]; Ln = hm.app(vn, Y)
    if multi == "M" and any(pre(L[-1], Ln) for L in hist): return ("M-I-Ln", multi, o3)
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == vn and L[-3] == Y]
    if not gl: return (multi + "-noglue", multi, o3)
    a1 = hist[gl[0]][-1]
    if vn <= 0: return (multi + "-vn-atom", multi, o3)
    c0 = hm.R[vn]
    if a1 == c0: return (multi + "-IIa", multi, o3)
    if hm.L[c0] == 0 and hm.R[c0] == a1: return (multi + "-IIb(c0=S.a1)", multi, o3)
    return (multi + "-IIb(other)", multi, o3)
def family(argv):
    if argv[0] == "t":
        NK, WK, NT = map(int, argv[1:4])
        Ks = [t for n in range(1, NK + 1) for t in hm.trees(n) if hm.head(t) == 0]
        wr = [t for n in range(1, WK + 1) for t in hm.trees(n)]
        tails = [P]; fr = [(P, 1)]
        while fr:
            nf = []
            for t, sz in fr:
                for d in wr:
                    if sz + hm.size(d) <= NT:
                        u = hm.app(d, t); tails.append(u); nf.append((u, sz + hm.size(d)))
            fr = nf
        for T in tails:
            if T == P: continue
            for K in Ks: yield hm.app(K, T)
    elif argv[0] == "o":
        N = int(argv[1])
        for n in range(2, N + 1):
            for G in tg.contexts(n):
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): yield D
    else:
        for D in c3.rcombs(int(argv[0])):
            if hm.head(D) == 0: yield D
if __name__ == "__main__":
    data = list(family(sys.argv[1:]))
    st = collections.Counter(); ex = collections.defaultdict(list); M0 = hm.mark()
    for D in data:
        r = classify(D)
        if r is not None:
            st[r] += 1
            if len(ex[r[0]]) < 3: ex[r[0]].append(hm.show(D))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
    print("total", sum(st.values()))
    for k in sorted(ex): print("example", k, ex[k])
