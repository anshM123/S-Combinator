"""Check Lemma R′ (the round machine for unique-redex runs) against concrete head runs (main agent, 2026-10-26).
For each term in FILE, the concrete run is cut at its opcode-0 steps (round starts [c, S c, d] ++ W); for every round the
round machine — walk c's left spine with registers (u, v) = (S c, d): type 1 (S c') gives (v, u·v), type 2 (S c' t)
pushes u·v and gives (t, v), the end needs u = S — predicts the next round start [v, S v, d'] (d' = last push, or the next
list element), which is compared with the concrete run. Usage: python ur_rounds.py FILE [ROUNDS]"""
import sys
sys.setrecursionlimit(1000000)
import hc
from symb import parse

def round_machine(c, d, W1):
    """(c', d', valid) for the round starting at [c, S c, d, W1, ...]"""
    u, v, pushed = hc.app(0, c), d, None
    x = c
    while x != 0:
        args, h = hc.spine(x)
        if len(args) == 1:                                    # type 1: x = S c'
            u, v = v, hc.app(u, v)
        else:                                                 # type 2: x = S c' t
            pushed = hc.app(u, v); u, v = args[1], v
        if len(hc.spine(u)[0]) >= 2: return None, None, False
        x = args[0]
    if u != 0: return None, None, False
    return v, (pushed if pushed is not None else W1), True

if __name__ == "__main__":
    path = sys.argv[1]; NR = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    terms = [l.split()[1] for l in open(path, encoding="utf-8") if len(l.split()) > 2 and l.split()[1].startswith("S")]
    good = total = 0; bad = []
    for src in terms:
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
        args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
        starts = []
        prev_op = None
        for n in range(20000):
            if len(stk) < 3: break
            if prev_op == 0: starts.append(list(reversed(stk[-4:])) if len(stk) >= 4 else list(reversed(stk[-3:])) + [None])
            if len(starts) > NR: break
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch)); prev_op = len(ch)
        for (c, Sc, d, W1), nxt in zip(starts, starts[1:]):
            total += 1
            c2, d2, ok = round_machine(c, d, W1)
            if ok and nxt[0] == c2 and nxt[1] == hc.app(0, c2) and nxt[2] == d2: good += 1
            else: bad.append(src)
    print(f"{path}: {len(terms)} terms, {total} rounds; round machine = concrete run for {good}/{total}")
    if bad: print("  first mismatches:", sorted(set(bad))[:5])
