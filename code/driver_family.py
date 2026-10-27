"""Driver family scan (main agent): configurations C1_G(P) = [P, S S G P, P(S P)(S S G P)] (the binary counter's C1
with W = SS replaced by a gadget G) over small G and two bases P; run the head machine with atoms below (a run that
opens an atom is reported as 'reads tape'), classify the opcode word by rand_radix.radix and by the growth of the
largest call found among frequent front elements."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, trees, show
import hc
from rand_radix import radix
N = int(sys.argv[1]); STEPS = int(sys.argv[2])
bases = {"S(SSbc)": parse("S(SS(S(SS(SS)))(S(S(SS)S)(SS(SS))))"), "SS": parse("SS")}
out = collections.Counter(); examples = collections.defaultdict(list)
for n in range(1, N + 1):
    for G in trees(n):
        for bn, B in bases.items():
            P = hc.from_tuple(B); g = hc.from_tuple(G)
            Q = hc.app(hc.app(hc.app(0, 0), g), P)
            third = hc.app(hc.app(P, hc.app(0, P)), Q)
            stk = [-5, -4, -3, third, Q, P]; ops = []; status = "ran"
            for t in range(STEPS):
                a = stk[-1]
                args, h = hc.spine(a)
                if h != 0: status = "reads tape"; break
                if len(stk) < 3: status = "hnf"; break
                stk.pop(); bb = stk.pop(); cc = stk.pop()
                ops.append(len(args)); stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
            if status != "ran": key = status
            else:
                r = radix(ops)
                key = f"base {r[0]}" if r else "no radix law"
            out[key] += 1
            if len(examples[key]) < 6: examples[key].append(f"G={show(G)} base {bn}")
print(dict(out))
for k, v in examples.items(): print(f"  {k}: {v}")
