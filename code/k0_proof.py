"""Symbolic proof for the robust counter K0 = S(SS)S(S(S(SSS)))S (main agent).
Levels L_{m+1} = S·M_m, M_m = (S L_m)(L_m (S L_m)), L_0 = S(S(S(S(SSS)))S). Tokens ('L', d) = L_{j+d}.
Return form R'(Z) = [Z·(S·Z), S·(Z·(S·Z)), (S·Z)·(Z·(S·Z))]. Macros:
  CALL   [L(d), x, y | ?]              -> R'(x·y) + ?        (call lemma at level j+d,      cost T_{j+d})
  RESUME [L(d), L(d)·(S·L(d)), Z | ?]  -> R'(Z) + ?          (remainder of a level-(d+1) call, cost T_{j+d+1} - 2)
(1) call lemma inductive step (macros only below level j); (2) driver R'(M_{k-1}) -> R'(M_k); (3) base cases concrete."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
JUNK = "?"
def L(d): return ("L", d)
def is_tok(t): return isinstance(t, tuple) and len(t) == 2 and t[0] == "L" and isinstance(t[1], int)
def M(e): return (("S", L(e)), (L(e), ("S", L(e))))
def is_M(t):
    return (isinstance(t, tuple) and not is_tok(t) and isinstance(t[0], tuple) and not is_tok(t[0]) and t[0][0] == "S"
            and is_tok(t[0][1]) and t == M(t[0][1][1]))
def mk(f, a):
    if f == "S" and is_M(a): return L(a[0][1][1] + 1)
    return (f, a)
def R(Z):
    ZSZ = mk(Z, mk("S", Z)); return [ZSZ, mk("S", ZSZ), mk(mk("S", Z), ZSZ)]
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
            if self.jmin + h[1] < 1: raise ValueError(f"level j{h[1]:+d} may be 0")
            return [M(h[1] - 1)] + args
        raise ValueError(f"opaque element opened: {h}")
    def run(self, K, goal, cap=20000):
        for n in range(cap):
            if K[:3] == goal[:3]: return n
            if JUNK in K[:3]: raise ValueError("unknown rest reached the top three")
            if is_tok(K[0]):
                d = K[0][1]
                if K[1] == (L(d), ("S", L(d))) and d + 1 <= self.maxlev and self.jmin + d + 1 >= 1:
                    self.items.append(("resume", d + 1)); K = R(K[2]) + [JUNK]; continue
                if d <= self.maxlev:
                    if self.jmin + d < 0: raise ValueError("call at negative level")
                    self.items.append(("call", d)); K = R(mk(K[1], K[2])) + [JUNK]; continue
            ch = self.open_front(K[0]); self.items.append(("eng", len(ch)))
            K = ch + [K[2], mk(K[1], K[2])] + K[3:]
        return None
def trace(items): return " ".join(str(v) if k == "eng" else f"[{k} {v:+d}]" for k, v in items)
if __name__ == "__main__":
    for jmin in range(1, 5):
        E = Engine(jmin, maxlev=-1); Z = ("x", "y")
        K = [L(0), "x", "y", JUNK]; first = E.open_front(K[0]); E.items.append(("eng", len(first)))
        K = first + [K[2], mk(K[1], K[2])] + K[3:]
        try: n = E.run(K, R(Z))
        except ValueError as e: print(f"call step, j >= {jmin}: fails ({e})"); continue
        print(f"call step, j >= {jmin}: {'goal reached' if n is not None else 'not reached'}: {trace(E.items)}")
        if n is not None: break
    for jmin in range(1, 6):
        E = Engine(jmin)
        try: n = E.run(R(M(-1)) + [JUNK], R(M(0)))
        except ValueError as e: print(f"driver, k >= {jmin}: fails ({e})"); continue
        print(f"driver, k >= {jmin}: {'R(M_k-1) -> R(M_k) reached' if n is not None else 'not reached'}: {trace(E.items)}")
        if n is not None: break
