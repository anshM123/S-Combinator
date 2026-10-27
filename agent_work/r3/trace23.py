"""R3 agent: print phase-2 and phase-3 traces for a datum (front first).  usage: trace23.py DATUM [maxsteps]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
hm.NAMES[C] = "c"
def trace(D, budget, label):
    st = [Rr, Y, X, D]
    print("---", label, hm.show(D))
    for t in range(budget):
        print("%3d" % t, hm.show_list(st, maxn=10))
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        hm.step(st)
    return st
if __name__ == "__main__":
    D = hm.parse(sys.argv[1]); B = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    st = trace(D, B, "phase 2")
    if len(st) >= 3 and hm.head(st[-1]) == P and T3.S3.proper(st[-3]):
        V = st[-3]
        D3 = tg.subst(tg.subst(V, P, C), Y, P)
        st3 = trace(D3, B, "phase 3")
