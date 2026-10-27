"""Concrete certification of Theorem K (main agent): for mu = 3..MU the term
t_mu = S L_1 (S S X L_1) (L_1 (S L_1) (S S X L_1)), X = (SS·)^(mu-3) SSS(SS), L_0 = S(SS(S(SS))(S(S(SS)S)(SSX))),
L_{m+1} = S(S S X L_m), has C1(k) on top exactly at t_k = sum_{i=1}^{k-1} (2T_i + 3T_{i+1} - 3), k = 1..K, where
T_0 = 8, T_m = mu T_{m-1} + 2mu + 4."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
MU, KMAX, CAP = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
SS = hc.app(0, 0)
for mu in range(3, MU + 1):
    X = hc.from_tuple(parse("SSS(SS)"))
    for _ in range(mu - 3): X = hc.app(SS, X)
    VX = hc.app(SS, X)
    Lv = [hc.app(0, hc.app(hc.app(SS, hc.from_tuple(parse("S(SS)"))), hc.app(hc.from_tuple(parse("S(S(SS)S)")), VX)))]
    for m in range(KMAX + 2): Lv.append(hc.app(0, hc.app(VX, Lv[-1])))
    T = [8]
    for m in range(1, KMAX + 2): T.append(mu * T[-1] + 2 * mu + 4)
    def C1(k):
        Q = hc.app(VX, Lv[k]); return [Lv[k], Q, hc.app(hc.app(Lv[k], hc.app(0, Lv[k])), Q)]
    pred = {0: 1}; t = 0
    for k in range(1, KMAX):
        t += 2 * T[k] + 3 * T[k + 1] - 3; pred[t] = k + 1
    term = hc.app(hc.app(hc.app(0, Lv[1]), hc.app(VX, Lv[1])), hc.app(hc.app(Lv[1], hc.app(0, Lv[1])), hc.app(VX, Lv[1])))
    args, h = hc.spine(term); stk = args[::-1]; ok = 0; tested = 0; last = 0
    for s in range(min(max(pred), CAP) + 1):
        if s in pred:
            tested += 1; ok += stk[-1:-4:-1] == C1(pred[s]); last = s
        if len(stk) < 3: break
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); a_args, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(a_args))
    print(f"mu={mu}: term size {hc.size(term)}; C1(k) on top at the predicted step: {ok}/{tested} (checked to step {last}); "
          f"T_1..T_4 = {T[1:5]}", flush=True)
