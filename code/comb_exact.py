"""Exact form of a comb run's opcode word (main agent): after a prefix, is the word D·B^{m}·D·B^{m+1}·D·B^{m+2}⋯ for fixed
words D, B? Finds B (local period block), D (the defect word between block runs) and checks the whole window."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
N = int(sys.argv[1])
for src in sys.argv[2:]:
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []
    for n in range(N):
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(str(len(ch)))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    w = "".join(ops)
    p = max(range(1, 40), key=lambda q: sum(w[i] == w[i - q] for i in range(q, len(w))))
    # find a block B of length p occurring in long runs: take the most common length-p substring
    from collections import Counter
    B = Counter(w[i:i + p] for i in range(len(w) // 2, len(w) - p)).most_common(1)[0][0]
    # parse the tail greedily into maximal runs of B and the material between them
    i = len(w) // 4; runs = []; between = []
    # align to the next occurrence of B
    i = w.index(B, i)
    while i < len(w) - 2 * len(B):
        m = 0
        while w.startswith(B, i): i += len(B); m += 1
        j = w.find(B, i)
        if j < 0: break
        runs.append(m); between.append(w[i:j]); i = j
    Ds = set(between[1:-1]); inc = [b - a for a, b in zip(runs[1:-1], runs[2:-1])]
    print(f"{src}: block B = {B} (|B| = {p}); separators {Ds if len(Ds) <= 3 else str(len(Ds)) + ' distinct'}; "
          f"run lengths {runs[1:6]} … {runs[-6:-1]}; increments {set(inc)}")
