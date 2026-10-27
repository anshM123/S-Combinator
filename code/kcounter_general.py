"""Gadget counters for ALL mu >= 4 at once (main agent). The gadget X_mu (mu >= 4) is an opaque symbol N; X_3 = SSS(SS)
is concrete; V = S S N. Extra macro (unroll lemma, induction on mu, Theorem N style): a front ((N·L(d))·Y') with >= 2
elements below becomes, after (mu-3)(T_{j+d} + 2) steps, the top three [Y, V·Y, (Y(SY))(V·Y)] with Y = (X_3·L(d))·Y'
(each of the mu-3 layers is 2 head steps, opcodes 4 0, then a level-(j+d) call; the last call's return top is the
call lemma's). The derivations must never open N."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import tern_proof as TP
N = "N"; X3 = parse("SSS(SS)")
TP.G = N; TP.V = (("S", "S"), N)
class E2(TP.Engine):
    def run(self, K, goal, cap=20000):
        for n in range(cap):
            if K[:3] == goal[:3]: return n
            if TP.JUNK in K[:3]: raise ValueError("unknown rest reached the top three")
            f = K[0]
            if (isinstance(f, tuple) and not TP.is_tok(f) and isinstance(f[0], tuple) and not TP.is_tok(f[0])
                    and f[0][0] == N and TP.is_tok(f[0][1]) and len(K) >= 3):
                d = f[0][1][1]
                if d <= self.maxlev and self.jmin + d >= 0:
                    Y = TP.mk(TP.mk(X3, TP.L(d)), f[1])
                    self.items.append(("unroll", d)); K = self.ret(Y); continue
                raise ValueError("unroll at a disallowed level")
            if TP.is_tok(f):
                d = f[1]
                if K[1] == (N, TP.L(d)) and d + 1 <= self.maxlev and self.jmin + d + 1 >= 1:
                    self.items.append(("resume", d + 1)); K = self.ret(K[2]); continue
                if d <= self.maxlev:
                    if self.jmin + d < 0: raise ValueError("call at negative level")
                    self.items.append(("call", d)); K = self.ret(TP.mk(K[1], K[2])); continue
            ch = self.open_front(f)
            self.items.append(("eng", len(ch)))
            K = ch + [K[2], TP.mk(K[1], K[2])] + K[3:]
        return None
for jmin in range(1, 5):
    E = E2(jmin, maxlev=-1); Z = ("x", "y")
    K = [TP.L(0), "x", "y", TP.JUNK]; first = E.open_front(K[0]); E.items.append(("eng", len(first)))
    K = first + [K[2], TP.mk(K[1], K[2])] + K[3:]
    try: n = E.run(K, [Z, TP.mk(TP.V, Z), TP.mk(TP.mk(Z, TP.mk("S", Z)), TP.mk(TP.V, Z))])
    except ValueError as e: print(f"call step j >= {jmin}: fails ({e})"); continue
    print(f"call step, all mu >= 4, j >= {jmin}: {'goal reached' if n is not None else 'not reached'}: {TP.trace(E.items)}")
    if n is not None: break
for jmin in range(1, 5):
    E = E2(jmin)
    def C1(d):
        Q = TP.mk(TP.mk(("S", "S"), N), TP.L(d)); return [TP.L(d), Q, TP.mk(TP.mk(TP.L(d), TP.mk("S", TP.L(d))), Q)]
    try: n = E.run(C1(0) + [TP.JUNK], C1(1))
    except ValueError as e: print(f"driver k >= {jmin}: fails ({e})"); continue
    print(f"driver, all mu >= 4, k >= {jmin}: {'C1(k) -> C1(k+1) reached' if n is not None else 'not reached'}: {TP.trace(E.items)}")
    if n is not None: break
