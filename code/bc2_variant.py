"""BC2 scheme with the variant return form R''(Z) = [Z(SZ), SS·(Z(SZ)), (SZ)(Z(SZ))] (main agent): symbolic call step and
driver with the k0_proof engine (return form swapped), then per-term checks for the census terms that showed R'':
base levels L_0 (recovered by unfolding) and L_1 return R'' on generic arguments, and the run reaches R''(M_k) states."""
import sys, collections
sys.setrecursionlimit(1000000)
import k0_proof as K
from symb import parse
import hc
def R2(Z):
    ZSZ = K.mk(Z, K.mk("S", Z)); return [ZSZ, K.mk(("S", "S"), ZSZ), K.mk(K.mk("S", Z), ZSZ)]
K.R = R2
for jmin in range(1, 5):
    E = K.Engine(jmin, maxlev=-1); Z = ("x", "y")
    Kl = [K.L(0), "x", "y", K.JUNK]; first = E.open_front(Kl[0]); E.items.append(("eng", len(first)))
    Kl = first + [Kl[2], K.mk(Kl[1], Kl[2])] + Kl[3:]
    try: n = E.run(Kl, R2(Z))
    except ValueError as e: print(f"call step j >= {jmin}: fails ({e})"); continue
    print(f"R'' call step, j >= {jmin}: {'goal reached' if n is not None else 'not reached'}: {K.trace(E.items)}")
    if n is not None: break
for jmin in range(1, 6):
    E = K.Engine(jmin)
    try: n = E.run(R2(K.M(-1)) + [K.JUNK], R2(K.M(0)))
    except ValueError as e: print(f"driver k >= {jmin}: fails ({e})"); continue
    print(f"R'' driver, k >= {jmin}: {'reached' if n is not None else 'not reached'}: {K.trace(E.items)}")
    if n is not None: break
