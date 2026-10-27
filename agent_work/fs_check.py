"""Check Theorem FS on random single-level phase-3-shaped data W.p' (W S-headed, contains c, no p'; c- and
p'-ordered): (a) |args W| = 1 => the first step is sigma_C (front a = the single C-arg, p' glued onto y) unless a is
frozen-headed; (b) |args W| >= 2 => p' is untouched until exactly two elements lie above it, and then a C-element is
glued onto p' (a buffer), unless the phase ends first."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg, p3shape_pos3 as S3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); Wn = int(sys.argv[3])
st = collections.Counter(); M0 = hm.mark()
for it in range(N):
    W = S3.rand_term(random.randint(2, Wn), 0.2)
    if C not in tg.atoms(W) or hm.head(W) != 0 or not pg.ordered(W): hm.truncate(M0); continue
    args, _ = hm.spine(W)
    lst = [Rr, Y, X, P] + list(reversed(args))      # args(W) ++ [p', y, x.y, r] built directly
    lst = [Rr, hm.app(X, Y), Y, P] + list(reversed(args))
    if len(args) == 1:
        a = args[0]
        if hm.head(a) != 0: st["(a) front frozen-headed: stuck"] += 1
        else:
            hm.step(lst)
            ok = lst[-(len(hm.spine(a)[0]) + 1)] == Y and lst[-(len(hm.spine(a)[0]) + 2)] == hm.app(P, Y)
            st["(a) sigma_C at step 1: " + ("yes" if ok else "NO")] += 1
    else:
        res = None
        for t in range(3000):
            ip = len(lst) - 1 - lst[::-1].index(P) if P in lst else None
            if ip is None: res = "p' gone?"; break
            above = len(lst) - 1 - ip
            if len(lst) < 3 or hm.head(lst[-1]) != 0: res = "phase ended first"; break
            if above <= 2:
                if above == 2:
                    b = lst[-2]
                    isC = C in tg.atoms(b) and P not in tg.atoms(b) and Y not in tg.atoms(b) and X not in tg.atoms(b)
                    res = "two above p': step glues a C-element onto p'" if isC else "two above p': glued element NOT C (!)"
                else: res = "fewer than two above p' (!)"
                break
            hm.step(lst)
        st["(b) " + (res or "budget")] += 1
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
