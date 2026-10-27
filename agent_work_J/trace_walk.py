"""agent_work_J/trace_walk.py -- print a leftmost walk node by node as (kind, top letters / stack letters).
usage: python trace_walk.py TERM [NODES]"""
import sys
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, parse
def letters(u):
    out = []
    while u != 0: out.append(L[u]); u = R[u]
    return out
def twh(x):
    k = 0
    while x != 0:
        if L[x] != 0: return None
        x = R[x]; k += 1
    return k
def sh(x, n=40):
    k = twh(x)
    if k is not None: return "tw%d" % k
    s = show(x); return s if len(s) <= n else s[:n] + ".."
def run(t, nodes):
    u = t
    for j in range(nodes):
        if u == 0: print(j, "LEAF S"); return
        ls = letters(u); q, v = L[u], R[u]
        st = " | ".join(sh(x, 30) for x in ls[:6]) + (" | ..(%d)" % len(ls) if len(ls) > 6 else "")
        if q == 0: kind = "POP "; nu = v
        else:
            a = spine(q)[0]
            if len(a) == 1: kind = "JUMP"; nu = a[0]
            else:
                Hq = hnf(q, 100000)
                kind = "comp"
                if Hq is not None and len(Hq) == 2:
                    K = twh(Hq[0]); kind = "K=%s c0=%s" % (K, sh(Hq[1], 25))
                H = hnf(u, max(20000, 20 * size(u)))
                if H is None: print(j, "BOT  ", "depth", len(ls), ":", st); return
                nu = H[0]
        print(j, kind, " depth", len(ls), "size", size(u), ":", st)
        u = nu
if __name__ == "__main__":
    run(parse(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 60)
