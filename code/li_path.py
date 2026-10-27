"""The frozen spine of a leftmost-innermost evolution (main agent, 2026-10-26).
Each LI step contracts a redex at a path of argument indices (k = 0, 1, 2 for a1, a2, a3 of the spine). The part of the
term above the longest common prefix of all later paths never changes again. This prints, for a term, the frozen path
(as a word over 0,1,2) and at each frozen level the spine length and the sizes of the frozen siblings.
Usage: python li_path.py TERM STEPS"""
import sys
sys.setrecursionlimit(1000000)
import hc
from li_explore import has_redex, build
from symb import parse

def li_step_path(i):
    path = []; trail = []
    while True:
        args, h = hc.spine(i)
        k = next((k for k in range(min(3, len(args))) if has_redex(args[k])), None)
        if k is not None:
            path.append((h, args, k)); trail.append(k); i = args[k]; continue
        if len(args) < 3: return None
        new = hc.app(hc.app(args[0], args[2]), hc.app(args[1], args[2]))
        for x in args[3:]: new = hc.app(new, x)
        break
    for h, args, k in reversed(path):
        a2 = list(args); a2[k] = new; new = build(h, a2)
    return new, trail

if __name__ == "__main__":
    t = hc.from_tuple(parse(sys.argv[1])); STEPS = int(sys.argv[2])
    trails = []; states = [t]
    for s in range(STEPS):
        r = li_step_path(t)
        if r is None: print("normal form"); break
        t, tr = r; trails.append(tr); states.append(t)
        if hc.size(t, {}) > 2_000_000: break
    # frozen prefix after step s: common prefix of trails[s:]
    n = len(trails); suffix = trails[-1][:]
    fro = []
    for s in range(n - 1, -1, -1):
        tr = trails[s]; j = 0
        while j < min(len(tr), len(suffix)) and tr[j] == suffix[j]: j += 1
        suffix = suffix[:j]; fro.append(len(suffix))
    fro.reverse()
    print(f"{sys.argv[1]}: {n} steps; frozen depth after step s (every {max(1, n // 20)} steps):",
          [fro[s] for s in range(0, n, max(1, n // 20))])
    s0 = n // 2; suffix = trails[s0][:]
    for tr in trails[s0:]:
        j = 0
        while j < min(len(tr), len(suffix)) and tr[j] == suffix[j]: j += 1
        suffix = suffix[:j]
    print(f"frozen path word (common prefix of the paths from step {s0} on, length {len(suffix)}):",
          "".join(map(str, suffix[:200])))
    # frozen siblings along the path, read from the last state
    i = states[-1]; info = []
    for k in suffix[:60]:
        args, h = hc.spine(i)
        info.append((len(args), k, [hc.size(a, {}) if j != k else "*" for j, a in enumerate(args)]))
        i = args[k]
    for x in info[:40]: print("   ", x)
