"""Windowed transfer-lemma test (main agent): in the first N steps of the leftmost-outermost run, is every slot that is
relevant within the window (opened by step N, or merged as the head of a product relevant within the window) a normal
form whenever it waits? If so, the parallel run provably opens the same elements for N steps (transfer lemma)."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from waiting_nf import is_nf
N = int(sys.argv[1])
for src in sys.argv[2:]:
    args, h = hc.spine(hc.from_tuple(parse(src))); nid = [0]
    def new(e): nid[0] += 1; return (nid[0], e)
    stk = [new(e) for e in reversed(args)]
    waited_nonnf = set(); opened = set(); prod_b = {}; first_bad_step = None; nonnf_wait_step = {}
    for n in range(N):
        if len(stk) < 3: break
        for sid, e in stk[:-3]:
            if sid not in waited_nonnf and not is_nf(e): waited_nonnf.add(sid); nonnf_wait_step[sid] = n
        (ia, a) = stk.pop(); bsl = stk.pop(); csl = stk.pop(); opened.add(ia)
        ch, _ = hc.spine(a)
        p = new(hc.app(bsl[1], csl[1])); prod_b[p[0]] = bsl[0]
        stk.append(p); stk.append(csl); stk.extend(new(x) for x in reversed(ch))
    relevant = set(opened); changed = True
    while changed:
        changed = False
        for pp, b in prod_b.items():
            if pp in relevant and b not in relevant: relevant.add(b); changed = True
    bad = waited_nonnf & relevant
    first = min((nonnf_wait_step[s] for s in bad), default=None)
    print(f"{src}: {N} steps; relevant slots {len(relevant)}; waiting non-normal forms {len(waited_nonnf)} "
          f"(all junk: {not bad}){'' if not bad else f'; first relevant violation at step {first}'}", flush=True)
