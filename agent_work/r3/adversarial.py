"""R3 agent: adversarial search for counterexamples to R3 on RIGHT COMBS (one occurrence of p), aimed at the
mechanism of the two-occurrence counterexample: an innermost level that transfers as soon as it is opened
(L_k = S.p, or S.(S.p), ...), outer wrappers random closed terms.  D = d1.(d2.(...(L_k))) with k-1 random closed
wrappers of up to W leaves.  usage: adversarial.py SEED W COUNT"""
import sys, os, random, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
import r3search as RS
P, Y = c3.P, c3.Y
INNER = [hm.parse("Sp") if False else None]
def inner_levels():
    Sp = hm.app(0, P)
    return [Sp, hm.app(0, Sp), hm.app(hm.app(0, 0), P), hm.app(hm.app(0, 0), Sp), hm.app(0, hm.app(hm.app(0, 0), P))]
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); W = int(sys.argv[2]); M = int(sys.argv[3])
    st = collections.Counter(); ex = []
    INN = inner_levels(); M0 = hm.mark()
    for it in range(M):
        t = random.choice(INN)
        for j in range(random.randint(1, 3)):
            t = hm.app(RS.rclosed(random.randint(1, W)), t)
        D = t
        if hm.head(D) != 0: hm.truncate(M0); continue
        st["data"] += 1
        o2, V, _ = T3.phase(D, 2000)
        if o2 != "proper3": hm.truncate(M0); continue
        st["proper transfers"] += 1
        D3 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
        o3, V3, _ = T3.phase(D3, 2000)
        st["next phase " + o3] += 1
        if o3 == "proper3" and len(ex) < 8: ex.append((hm.show(D), hm.show(V), hm.show(V3)))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
    for e in ex: print("R3 VIOLATION on a right comb:", e)
