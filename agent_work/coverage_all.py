"""Combined coverage: every real proper position-3 phase-2 handler V is classified by the first machine-checked
theorem whose hypotheses it satisfies (hypotheses checked per case):
  FH  : some wrapper p-headed                       (OTD.lean fh_rcomb)
  FHL : some wrapper with leftmost path to p         (FHL.lean fhl_main)
  YD  : outermost wrapper = bare S                   (YD.lean yd_bareS)
  PA  : single wrapper, pattern alpha, guards        (PA.lean pa_main)
  PB  : single wrapper, pattern beta c0 = S.a1, guards (PA.lean pb_main)
  PAM : multi-wrapper, innermost vn pattern alpha, guards, B0 condition (PA.lean pam_main)
  open: none of the above."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def pre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
FROZSET = set(c3.FROZ)
def lp_reaches_p(t):
    """leftmost first-argument path reaches p or a frozen atom (FHL's hypothesis after p := c)"""
    while True:
        h = hm.head(t)
        if h == P or h in FROZSET: return True
        if h != 0: return False
        args, _ = hm.spine(t)
        if not args: return False
        t = args[0]
def topguard(g, wy):
    a0, _ = hm.spine(g)
    T2 = [wy, Y] + list(reversed(a0)); guard = True
    while len(T2) >= 3 and hm.head(T2[-1]) == 0:
        if pre(T2[-1], wy) or hm.app(T2[-2], T2[-3]) == wy: guard = False
        hm.step(T2)
    return guard and len(T2) >= 1 and hm.head(T2[-1]) == P

def classify(D2):
    """returns (kind, 'single'/'multi') for a real proper position-3 handler of D2, or None"""
    lst = [Rr, Y, X, D2]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])):
        return None
    V = lst[-3]
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    kind = None
    if any(hm.head(w) == P or hm.head(w) in FROZSET for w in ws): kind = "FH"
    elif any(lp_reaches_p(w) for w in ws): kind = "FHL"
    elif ws[0] == 0: kind = "YD"
    else:
        vn = ws[-1]; b0, c0 = hm.L[vn], hm.R[vn]
        gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == vn and L[-3] == Y]
        if gl and hm.head(b0) == 0 and hm.head(c0) == 0:
            a1 = hist[gl[-1]][-1]; wy = hm.app(vn, Y)
            if a1 == c0 and topguard(c0, wy):
                if len(ws) == 1: kind = "PA"
                else:
                    D3 = tg.subst(tg.subst(V, P, C), Y, P); Ln = hm.app(tg.subst(vn, P, C), P)
                    s3 = [Rr, Y, X, D3]; ok = True
                    for t in range(3000):
                        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
                        if pre(s3[-1], Ln):
                            k0 = len(hm.spine(tg.subst(vn, P, C))[0]); hm.step(s3)
                            B0 = s3[-(k0 + 2)] if len(s3) >= k0 + 2 else None
                            ok = B0 is None or B0 == Y or Y not in tg.atoms(B0)
                            break
                        hm.step(s3)
                    if ok: kind = "PAM"
            elif len(ws) == 1 and hm.L[c0] == 0 and hm.R[c0] == a1 and hm.head(a1) == 0 and topguard(a1, wy):
                kind = "PB"
    if kind is None: kind = "open"
    return (kind, "single" if len(ws) == 1 else "multi")

if __name__ == "__main__":
    if sys.argv[1] == "t":
        NK, WK, NT = map(int, sys.argv[2:5])
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
        data = [hm.app(K, T) for T in tails if T != P for K in Ks]
    else:
        data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]

    st = collections.Counter(); M0 = hm.mark(); openex = []
    for D2 in data:
        r = classify(D2)
        if r is not None:
            st[r] += 1
            if r[0] == "open" and len(openex) < 6: openex.append(hm.show(D2))
        hm.truncate(M0)
    tot = sum(st.values())
    for k in sorted(st): print(k, st[k])
    print("total", tot, " covered", tot - sum(v for k, v in st.items() if k[0] == "open"))
    for e in openex: print("open:", e)
