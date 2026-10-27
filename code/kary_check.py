"""k-ary call schemes (main agent): P_0 = SS, P_{m+1} = S·N_k(P_m), N_1(P) = P·S, N_{i+1}(P) = S P N_i(P).
Generic run of [P_m, x, y, r1..r6] (atoms): report the step at which x·y reaches the front, whether any r was ever
popped, and the element just below x·y. Predicted: T_{m+1} = k T_m + k, i.e. T_m = 2k^m + k(k^m - 1)/(k - 1)."""
import sys
sys.setrecursionlimit(1000000)
def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return a, t
def N(k, P):
    t = (P, "S")
    for _ in range(k - 1): t = (("S", P), t)
    return t
def run(P, cap=10 ** 7):
    stk = ["r6", "r5", "r4", "r3", "r2", "r1", "y", "x", P]
    floor = len(stk) - 3          # r atoms occupy stk[:floor]
    touched = False
    for t in range(cap):
        a = stk[-1]
        args, h = spine(a)
        if h != "S": return t, a == ("x", "y"), touched
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        if len(stk) < floor: touched = True; floor = len(stk)
        stk.append((bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return None, False, touched
if __name__ == "__main__":
  for k in range(1, 7):
      P = ("S", "S"); Ts = []; ok = True
      for m in range(0, 8 if k <= 3 else 6):
          T, xy, touched = run(P)
          Ts.append(T); ok &= xy and not touched
          P = ("S", N(k, P))
      pred = [2] 
      for _ in Ts[1:]: pred.append(k * pred[-1] + k)
      print(f"k={k}: T = {Ts}  predicted {pred}  match={Ts == pred}  x·y at front, tape never touched: {ok}")
