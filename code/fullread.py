"""Exact check of the full-read principle (PROOF.md Lemma 11).

Occurrences are distinct Python objects; residuals are shared references (the head machine never copies
structure, it only shares c). Opening an element marks every node on its left spine. An argument e_i of the
initial node S e1 ... em is *fully read* if every node of e_i is marked by the end of a terminating run.
Lemma 11 claims: at most two arguments are not fully read.
"""
import random, sys
sys.setrecursionlimit(100000)

class N:
    __slots__ = ("l", "r", "mark", "orig")
    def __init__(self, l=None, r=None, orig=True):
        self.l, self.r, self.mark, self.orig = l, r, False, orig

def rand_tree(n, rng):
    if n == 1: return N()
    k = rng.randint(1, n - 1)
    return N(rand_tree(k, rng), rand_tree(n - k, rng))

def nodes(t, out):
    st = [t]
    while st:
        u = st.pop(); out.append(u)
        if u.l is not None: st.append(u.l); st.append(u.r)
    return out

def open_elem(a):
    """mark the left spine of a, return its spine arguments (top first)"""
    args = []
    while a.l is not None:
        a.mark = True; args.append(a.r); a = a.l
    a.mark = True
    args.reverse(); return args

def run(lst, budget, maxlen=400):
    st = lst[::-1]                      # top of the head-machine list = end of st
    steps = 0
    while len(st) >= 3:
        if steps >= budget or len(st) > maxlen: return None
        a = st.pop(); b = st.pop(); c = st.pop()
        st.append(N(b, c, orig=False)); st.append(c)
        st.extend(reversed(open_elem(a)))
        steps += 1
    return steps

def main(trials=200000, seed=1):
    rng = random.Random(seed)
    hist, term, viol = {}, 0, 0
    for _ in range(trials):
        m = rng.randint(3, 7)
        args = [rand_tree(rng.randint(1, 9), rng) for _ in range(m)]
        if run(list(args), 600) is None: continue
        term += 1
        unread = sum(1 for e in args if not all(u.mark for u in nodes(e, [])))
        hist[unread] = hist.get(unread, 0) + 1
        if unread > 2: viol += 1
    print("terminating runs:", term, " #not-fully-read args histogram:", dict(sorted(hist.items())), " violations:", viol)

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 200000)
