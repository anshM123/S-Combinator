import sys, itertools
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
from agent_u_sim import app, apps, spine, show, parse
from symb import trees
def conv(t): return 0 if t == "S" else app(conv(t[0]), conv(t[1]))
SS = parse("SS")
bases = [conv(t) for n in range(1, 7) for t in trees(n)]
marks = [conv(t) for n in range(2, 5) for t in trees(n)]
rs = [conv(t) for n in range(1, 4) for t in trees(n)]
found = []
for B0 in bases:
    nest = [B0]
    for _ in range(12): nest.append(app(SS, nest[-1]))
    idx = {t: i for i, t in enumerate(nest)}
    for M in marks:
        for R in rs:
            report = {}
            for n in (1, 2, 3):
                st = [0, nest[0]] + [0] * n + [M, R, R]
                ev = []
                for step in range(1, 500):
                    if len(st) < 3: break
                    a, b, c = st[0], st[1], st[2]
                    st = spine(a) + [c, app(b, c)] + st[3:]
                    if st[0] == 0 and len(st) > 3 and st[1] in idx:
                        m = 0
                        while 2 + m < len(st) and st[2 + m] == 0: m += 1
                        if m >= 1 and 2 + m < len(st) and st[2 + m] == M:
                            ev.append((step, idx[st[1]], m))
                            if len(ev) >= 4: break
                report[n] = ev
            if all(any(e[1] >= 1 for e in report[n]) for n in report):
                found.append((show(B0), show(M), show(R), report))
print(len(found))
for f in found[:12]: print(f)
