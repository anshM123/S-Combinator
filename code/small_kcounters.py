"""(a) small mu-ary counters: tau_mu = S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(X_mu))) — does its run reach C1(k) of the
mu-scheme (with its own base c-part) at increasing k? (b) driver with a foreign gadget: C1 with V' != V_base; which
gadgets do the successive levels built by the run carry? (main agent)"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
SS = hc.app(0, 0)
def gad(mu):
    g = hc.from_tuple(parse("SSS(SS)"))
    for _ in range(mu - 3): g = hc.app(SS, g)
    return g
def gshow(mu): return "SSS(SS)" if mu == 3 else "SS(" + gshow(mu - 1) + ")"
for mu in range(3, 9):
    src = f"S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS({gshow(mu)})))"
    t = hc.from_tuple(parse(src)); X = gad(mu); VX = hc.app(SS, X)
    # levels with the term's own base: L_0 = S(SS b' c'), b' = S(SS)(SS(SS)(SS)), c' = S(S(SS)S)(SS X)
    L = [hc.app(0, hc.app(hc.app(SS, hc.from_tuple(parse("S(SS)(SS(SS)(SS))"))), hc.app(hc.from_tuple(parse("S(S(SS)S)")), VX)))]
    for m in range(9): L.append(hc.app(0, hc.app(VX, L[-1])))
    C1 = {}
    for k in range(10):
        Q = hc.app(VX, L[k]); C1[L[k]] = (k, [L[k], Q, hc.app(hc.app(L[k], hc.app(0, L[k])), Q)])
    args, h = hc.spine(t); stk = args[::-1]; hits = []
    for s in range(1_500_000):
        if len(stk) < 3: hits.append(("hnf", s)); break
        a = stk[-1]
        if a in C1 and stk[-1:-4:-1] == C1[a][1]: hits.append((s, C1[a][0]))
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); a_args, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(a_args))
    print(f"(a) mu={mu}: {src} ({hc.size(t)} leaves): C1(k) hits (step, k) {hits[:8]}", flush=True)
# (b) foreign gadget in the configuration
for mu_b, mu_q in ((3, 4), (4, 3), (3, 5), (5, 3)):
    XB, XQ = gad(mu_b), gad(mu_q); VB, VQ = hc.app(SS, XB), hc.app(SS, XQ)
    L0 = hc.app(0, hc.app(hc.app(SS, hc.from_tuple(parse("S(SS)"))), hc.app(hc.from_tuple(parse("S(S(SS)S)")), VB)))
    L1 = hc.app(0, hc.app(VB, L0))
    stk = [-9, -8, -7, hc.app(hc.app(L1, hc.app(0, L1)), hc.app(VQ, L1)), hc.app(VQ, L1), L1]
    # record the gadget word of every new level that appears at the front as a bare call
    def word(x):
        w = []
        while True:
            if x == L0: return w
            if x <= 0 or hc.L[x] != 0: return None
            body = hc.R[x]                              # S S X L'
            if body <= 0 or hc.L[body] <= 0 or hc.L[hc.L[body]] != SS: return None
            g = hc.R[hc.L[body]]; w.append({gad(m): m for m in range(3, 9)}.get(g, "?")); x = hc.R[body]
    seen = []
    for s in range(400_000):
        a = stk[-1]; args, h = hc.spine(a)
        if h != 0 or len(stk) < 3: break
        w = word(a)
        if w is not None and len(stk) >= 3 and (not seen or len(w) > len(seen[-1])): seen.append(w)
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    print(f"(b) base gadget mu={mu_b}, configuration gadget mu={mu_q}: level words seen (outermost first): {seen[-4:]}")
