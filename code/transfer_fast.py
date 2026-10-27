"""Efficient windowed transfer test (main agent): leftmost-outermost run with slot identities; a slot's wait status is
checked once, when it first lies at position >= 3 (terms are immutable, so normal-form status does not change);
relevance closed under both parts of relevant products. Usage: python transfer_fast.py STEPS TERM..."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from waiting_nf import is_nf
N = int(sys.argv[1])
for src in sys.argv[2:]:
    args, h = hc.spine(hc.from_tuple(parse(src)))
    sid = 0; slots = []          # stack of (id, term); top = end
    def new(e):
        global sid
        sid += 1; return (sid, e)
    stk = [new(e) for e in reversed(args)]
    waited_nonnf = set(); waited = set(); opened = set(); parts = {}
    for n in range(N):
        if len(stk) < 3: break
        (ia, a) = stk.pop(); bsl = stk.pop(); csl = stk.pop(); opened.add(ia)
        ch, hh = hc.spine(a)
        p = new(hc.app(bsl[1], csl[1])); parts[p[0]] = (bsl[0], csl[0])
        stk.append(p); stk.append(csl); stk.extend(new(x) for x in reversed(ch))
        # newly waiting slots can only be within positions 3 .. len(ch) + 3 from the top
        top = len(stk) - 1
        for pos in range(3, min(len(stk), len(ch) + 5)):
            s_id, e = stk[top - pos]
            if s_id not in waited:
                waited.add(s_id)
                if not is_nf(e): waited_nonnf.add(s_id)
    relevant = set(opened); frontier = list(opened)
    rev = {}
    # close relevance under parts of relevant products
    while frontier:
        q = frontier.pop()
        pr = parts.get(q)
        if pr:
            for r in pr:
                if r not in relevant: relevant.add(r); frontier.append(r)
    bad = waited_nonnf & relevant
    print(f"{src}: {n + 1} steps; slots that waited {len(waited)}, of them non-normal forms {len(waited_nonnf)}; "
          f"relevant non-normal waiting slots: {len(bad)}", flush=True)
