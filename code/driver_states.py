"""Print the symbolic states of the gadget driver C1(k) -> C1(k+1) (gadget N opaque), to see where each element of
C1(k+1) comes from (main agent)."""
import sys
sys.setrecursionlimit(100000)
import tern_proof as TP
from kcounter_general import E2, N
def nm(t):
    if TP.is_tok(t): return f"L{t[1]:+d}" if t[1] else "L"
    if t == "S": return "S"
    if isinstance(t, str): return t
    if t == (("S", "S"), N): return "V"
    f, a = t
    return nm(f) + ("(" + nm(a) + ")" if isinstance(a, tuple) else nm(a))
class E3(E2):
    def run(self, K, goal, cap=200):
        for n in range(cap):
            print(f"  {n:2d} {' | '.join(nm(e)[:46] for e in K[:5])}")
            if K[:3] == goal[:3]: return n
            before = len(self.items)
            Kn = None
            # one step of the parent engine
            f = K[0]
            if TP.is_tok(f) and K[1] == (N, TP.L(f[1])):
                self.items.append(("resume", f[1] + 1)); print(f"     -> RESUME level {f[1] + 1:+d} with Z = {nm(K[2])[:60]}")
                K = self.ret(K[2]); continue
            if TP.is_tok(f):
                self.items.append(("call", f[1])); Z = TP.mk(K[1], K[2])
                print(f"     -> CALL level {f[1]:+d}: x = {nm(K[1])[:40]}, y = {nm(K[2])[:50]}"); K = self.ret(Z); continue
            ch = self.open_front(f); self.items.append(("eng", len(ch)))
            K = ch + [K[2], TP.mk(K[1], K[2])] + K[3:]
        return None
E = E3(1)
def C1(d):
    Q = TP.mk(TP.mk(("S", "S"), N), TP.L(d)); return [TP.L(d), Q, TP.mk(TP.mk(TP.L(d), TP.mk("S", TP.L(d))), Q)]
E.run(C1(0) + [TP.JUNK], C1(1))
