"""Independent check of parallel loop certificates (main agent, 2026-10-26): for each certified term, the concrete lazy
parallel word over N passes is cut at the certified cycle starts — first cycle (s, n); consecutive anchors are
alpha·n + beta apart and the anchor of cycle n lies a1·n + be1 after its start, so cycle starts are alpha·n + beta − a1
apart — and every cycle word must arise from the previous one by inserting at most m contiguous chunks (m = number of
loops used by the certificate): each loop gains a constant number of iterations per cycle and nothing else changes.
Usage: python par_cert_check.py TSV N"""
import sys, re, collections
sys.setrecursionlimit(1000000)
import lazy_par as lz

def inserts(a, b, m):
    """b arises from a by inserting at most m contiguous chunks"""
    if len(b) < len(a): return False
    if len(b) == len(a): return a == b
    if m == 0: return False
    p = 0
    while p < len(a) and a[p] == b[p]: p += 1
    a, b = a[p:], b[p:]
    return any(inserts(a, b[L:], m - 1) for L in range(1, len(b) - len(a) + 1))

def word(src, N):
    lz.reset(); return "".join(chr(48 + o) for o in lz.par_ops(src, N))

if __name__ == "__main__":
    path, N = sys.argv[1], int(sys.argv[2])
    ok = bad = 0
    for line in open(path, encoding="utf-8"):
        if "PROVED" not in line: continue
        term = line.split("\t", 1)[1].split(": parallel run ")[0]
        m = re.search(r"B = (\S+), (\d+) loop.*cycle length (\d+)·n \+ (-?\d+).*first cycle \((\d+), (\d+)\)", line)
        B, q, a, b, s, n = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6))
        an = re.search(r"anchor (-?\d+)·n \+ (-?\d+)", line)
        a1 = int(an.group(1)) if an else 0             # anchors are alpha·n + beta apart, cycle starts alpha·n + beta − a1
        b -= a1
        w = word(term, N)
        starts = []
        while s < len(w): starts.append((s, n)); s += a * n + b; n += 1
        mac = int(re.search(r"(\d+) macro", line).group(1)); budget = max(q, mac)
        words = [w[s1:s2] for (s1, n1), (s2, n2) in zip(starts, starts[1:]) if s2 <= len(w)]
        good = len(words) > 2 and all(inserts(u, v, budget) for u, v in zip(words, words[1:]))
        ok += good; bad += not good
        print(f"{'ok ' if good else 'BAD'} {term:34s} {len(words):4d} cycles to pass {starts[len(words)][0]}, each the previous "
              f"one with at most {budget} chunk(s) inserted", flush=True)
    print(f"{ok} consistent, {bad} not")
