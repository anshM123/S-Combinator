"""Symbolic proof for the ternary counter S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS)))) (main agent).
Levels: L_0 = S(SS b' c'), L_{m+1} = S·M_m, M_m = S S G L_m, G = SSS(SS), V' = S S G (b', c' from the term).
Tokens ('L', d) stand for L_{j+d} (j >= JMIN symbolic). Macros (each is a lemma proved by this same engine, see main):
  CALL   [L(d), x, y | ?]          -> [Z, V'·Z, (Z·(S·Z))·(V'·Z), ?]   (Z = x·y)   cost T_{j+d}
  RESUME [L(d), G·L(d), Z | ?]     -> same top three, cost T_{j+d+1} - 3   (remainder of a level-(d+1) call)
'?' marks an unknown rest of the list; a run fails if it reaches the top three.
"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
G = parse("SSS(SS)"); V = (("S", "S"), G)
L0 = parse("S(SS(S(SS)(SS(SS)(SS)))(S(S(SS)S)(SS(SSS(SS)))))")
JUNK = "?"
def L(d): return ("L", d)
def is_tok(t): return isinstance(t, tuple) and len(t) == 2 and t[0] == "L" and isinstance(t[1], int)
def M(d): return ((("S", "S"), G), L(d))
def is_M(t): return (isinstance(t, tuple) and not is_tok(t) and t[0] == (("S", "S"), G) and is_tok(t[1]))
def mk(f, a):
    if f == "S" and is_M(a): return L(a[1][1] + 1)
    return (f, a)
def spine(t):
    a = []
    while isinstance(t, tuple) and not is_tok(t): a.append(t[1]); t = t[0]
    a.reverse(); return t, a
class Engine:
    def __init__(self, jmin, maxlev=10 ** 9): self.jmin, self.maxlev, self.items = jmin, maxlev, []
    def open_front(self, e):
        h, args = spine(e)
        if h == "S": return args
        if is_tok(h):
            d = h[1]
            if self.jmin + d < 1: raise ValueError(f"level j{d:+d} may be 0")
            return [M(d - 1)] + args
        raise ValueError(f"opaque element opened: {h}")
    def ret(self, Z): return [Z, mk(V, Z), mk(mk(Z, mk("S", Z)), mk(V, Z)), JUNK]
    def run(self, K, goal, cap=20000):
        for n in range(cap):
            if K[:3] == goal[:3]: return n
            if JUNK in K[:3]: raise ValueError("unknown rest reached the top three")
            if is_tok(K[0]):
                d = K[0][1]
                if K[1] == (G, L(d)) and d + 1 <= self.maxlev and self.jmin + d + 1 >= 1:
                    self.items.append(("resume", d + 1)); K = self.ret(K[2]); continue
                if d <= self.maxlev:
                    if self.jmin + d < 0: raise ValueError("call at negative level")
                    self.items.append(("call", d)); K = self.ret(mk(K[1], K[2])); continue
            ch = self.open_front(K[0])
            self.items.append(("eng", len(ch)))
            K = ch + [K[2], mk(K[1], K[2])] + K[3:]
        return None
def trace(items): return " ".join(str(v) if k == "eng" else f"[{k} {v:+d}]" for k, v in items)
if __name__ == "__main__":
    # (1) call lemma, inductive step: macros only below level j
    for jmin in range(1, 5):
        E = Engine(jmin, maxlev=-1); Z = ("x", "y")
        K = [L(0), "x", "y", JUNK]; first = E.open_front(K[0]); E.items.append(("eng", len(first)))
        K = first + [K[2], mk(K[1], K[2])] + K[3:]
        try: n = E.run(K, [Z, mk(V, Z), mk(mk(Z, mk("S", Z)), mk(V, Z))])
        except ValueError as e: print(f"call step, j >= {jmin}: fails ({e})"); continue
        print(f"call step, j >= {jmin}: {'goal reached' if n is not None else 'not reached'}; trace: {trace(E.items)}")
        if n is not None: break
    # (2) driver cycle C1'(k) -> C1'(k+1)
    for jmin in range(1, 6):
        E = Engine(jmin)
        def C1(d): Q = mk(mk(("S", "S"), G), L(d)); return [L(d), Q, mk(mk(L(d), mk("S", L(d))), Q)]
        try: n = E.run(C1(0) + [JUNK], C1(1))
        except ValueError as e: print(f"driver, k >= {jmin}: fails ({e})"); continue
        print(f"driver, k >= {jmin}: {'C1(k) -> C1(k+1) reached' if n is not None else 'not reached'}; trace: {trace(E.items)}")
        if n is not None: break
