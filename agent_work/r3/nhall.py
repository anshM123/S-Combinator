"""R3 agent: multi-wrapper handlers V = v1.(...(vn.y)), v_j = b_j.c_j: does NH(c_j) hold for ALL levels j?
(Theorem NHALL candidate: then the V-run descends level by level through barrier phases and can only end in
REEXEC, a call, or a p'-front whose position 3 is y-free or the bare y.)  usage: nhall.py N | nhall.py t NK WK NT"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, fc0, cover
hm, tg, c3, T3 = CL.hm, CL.tg, CL.c3, CL.T3
P, Y = CL.P, CL.Y
def info(D):
    r = cover.classify(D)
    if r is None or r[1] != "M": return None
    lst = [CL.Rr, Y, CL.X, D]
    hm.run(lst, 1500)
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    Fs = []
    for w in ws:
        if w <= 0 or hm.head(w) != 0: Fs.append("notS"); continue
        c0 = hm.R[w]
        Fs.append(fc0.F(c0) if hm.head(c0) == 0 else ("c0 " + ("p-headed" if hm.head(c0) == P else "other")))
    allnh = all(f not in ("h1", "h2") for f in Fs)
    return (r[0], "all NH" if allnh else "some level calls a hole", r[2])
if __name__ == "__main__":
    data = list(CL.family(sys.argv[1:]))
    st = collections.Counter(); ex = collections.defaultdict(list); M0 = hm.mark()
    for D in data:
        r = info(D)
        if r is not None:
            st[r] += 1
            if len(ex[r]) < 2: ex[r].append(hm.show(D))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k], ex[k])
