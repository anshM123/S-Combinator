"""Search closed Q (<= NMAX leaves) such that some head-run state (as a term) or leftmost-outermost reduct contains Q
as a PROPER subterm (Q ->* C[Q]).  Uses the head machine (list) and checks every list element and their subterms
(hash-consed ids) for Q's id.  Reports the step and the context size."""
import sys
from dm import *
NMAX, BUD = map(int, sys.argv[1:3])
def subterm_ids(lst, limit=200000):
    seen = set(); st = list(lst)
    while st and len(seen) < limit:
        i = st.pop()
        if i <= 0 or i in seen: continue
        seen.add(i); st.append(L[i]); st.append(R[i])
    return seen
found = 0
for n in range(3, NMAX + 1):
    for Q in trees(n):
        args, h = spine(Q)
        if len(args) < 3: continue           # must be reducible at the head
        m = mark()
        st = list(reversed(args)); hit = None
        for t in range(BUD):
            if len(st) < 3: break
            a = st[-1]; aa, hh = spine(a)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
            # spine-prefix check: does the list begin with Q's spine args (so S q1..qm is a subterm)?
            m_ = len(args)
            if len(st) > m_ and all(st[-1 - k] == args[k] for k in range(m_)):
                hit = t + 1; break
            if t % 5 == 4 or t < 20:
                if Q in subterm_ids(st):
                    hit = t + 1; break
        if hit is not None:
            found += 1
            if found <= 30: print("Q=%s (%d leaves) contains itself after %d head steps; list len %d" % (show(Q), n, hit, len(st)), flush=True)
        truncate(m)
print("found", found)
