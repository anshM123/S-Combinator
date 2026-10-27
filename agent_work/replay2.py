"""Generalised replay test.  theta = (replace every occurrence of the innermost wrapper w by p', then p by c).
For each real phase-2 proper transfer (position 3) with a single wrapper V = w.y and S-headed w, check whether some
phase-3 list equals theta(some phase-2 list); report the first alignment and whether the replay then runs to the
phase-2 transfer (phase 3 REEXEC at the image of the transfer)."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
PP = hm.atom("pp")   # p' for phase 3
def theta(t, w, memo):
    if t in memo: return memo[t]
    if t == w: r = PP
    elif t == P: r = C
    elif t <= 0: r = t
    else: r = hm.app(theta(hm.L[t], w, memo), theta(hm.R[t], w, memo))
    memo[t] = r
    return r
def run_lists(st, budget):
    out = [tuple(st)]
    for t in range(budget):
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        hm.step(st); out.append(tuple(st))
    return out
if __name__ == "__main__":
  data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
  st = collections.Counter(); M0 = hm.mark(); ex = []
  for D2 in data:
      L2 = run_lists([Rr, Y, X, D2], 1500)
      last = list(L2[-1])
      if not (len(last) >= 3 and hm.head(last[-1]) == P and T3.S3.proper(last[-3])): hm.truncate(M0); continue
      V = last[-3]
      if hm.R[V] != Y: hm.truncate(M0); continue
      w = hm.L[V]
      if hm.head(w) != 0: st["w not S-headed (PH)"] += 1; hm.truncate(M0); continue
      D3 = hm.app(tg.subst(w, P, C), PP)
      L3 = run_lists([Rr, Y, X, D3], 1500)
      memo = {}
      img = {}
      for t, L in enumerate(L2):
          key = tuple(theta(e, w, memo) for e in L)
          img.setdefault(key, t)
      al = None
      for s, M in enumerate(L3):
          if M in img: al = (s, img[M]); break
      end3 = list(L3[-1]); h3 = hm.head(end3[-1]) if end3 else None
      o3 = "reexec" if h3 == C else ("p'-front" if h3 == PP else "other")
      if al is None:
          st[("no alignment", o3)] += 1
          if len(ex) < 6: ex.append((hm.show(D2), hm.show(V), o3))
      else:
          s, t = al
          # replay to the end?  phase-3 length after alignment vs phase-2 length after alignment
          st[("aligned", "replay to end" if len(L3) - s == len(L2) - t else "diverges", o3)] += 1
      hm.truncate(M0)
  for k in sorted(st, key=str): print(k, st[k])
  for e in ex: print("no alignment:", e)
