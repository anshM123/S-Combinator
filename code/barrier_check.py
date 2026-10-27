"""Sanity check of the barrier lemma (main agent): random S-terms P (5..80 leaves); generic run of [P, x, y, r1..r6] with
x, y, r atoms; the tape must never be popped before an atom-headed element is at the front."""
import random, sys
sys.setrecursionlimit(100000)
import hc
from sm_check import rand_term
rng = random.Random(9); bad = 0; stopped = 0; ran_out = 0
for it in range(3000):
    P = hc.from_tuple(rand_term(rng.randint(5, 80), rng))
    stk = [-8, -7, -6, -5, -4, -3, -2, -1, P]; floor = 6; ok = True
    for t in range(5000):
        a = stk[-1]; args, h = hc.spine(a)
        if h != 0: stopped += 1; break
        if len(stk) < 3: break
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        if len(stk) < floor: ok = False; break
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    else: ran_out += 1
    bad += not ok
print(f"3000 random P: tape popped before control passed in {bad} runs; stopped on an atom-headed front {stopped}; "
      f"still running after 5000 steps {ran_out}")
