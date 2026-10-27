"""Opcode words of nested-loop runs, read off the Theorem NL certificate (main agent, 2026-10-26).
For a term proved by nest_prover.py the symbolic cycle run M(n) ->* M(n+1) records the opcode of every step and every loop
macro it applies (a macro of n+b blocks contributes its block's opcode word n+b times; inner macros inside a block
likewise). So the opcode word of the run from the first anchor on is  prod_{n >= n1} C(n)  with C(n) an explicit
nested-loop expression — proved for all n by the certificate, not observed. This script prints C(n), checks the expansion
against the concrete run (a test of the bookkeeping, not part of the proof), and prints the run's word in compressed form.
Usage: python nest_words.py TERM [cycles]"""
import sys
import nest_prover as np_
from loop_prover import run

def expand(word, n):
    out = []
    for x in word:
        if isinstance(x, int): out.append(x)
        elif x[0] == "L": out += expand(x[1].word, n) * (n + x[1][2])
        else: out += expand(x[1].word, n) * x[2]          # ("J", mac, j): j blocks
    return out

def show(word):
    s = []
    for x in word:
        if isinstance(x, int): s.append(str(x))
        elif x[0] == "L":
            b = x[1][2]; s.append("(" + show(x[1].word) + ")^(n" + (f"{b:+d}" if b else "") + ")")
        else: s.append("(" + show(x[1].word) + f")^{x[2]}")
    return "".join(s)

if __name__ == "__main__":
    src = sys.argv[1]; K = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    r = np_.prove(src)
    if r["status"] != "PROVED": print(src, r["status"]); sys.exit(1)
    s1, n1 = r["first_cycle"]; t1 = s1 + np_.peval(r["to_anchor"], n1)
    print(f"{src}: PROVED, cycle length {np_.pshow(r['cycle'])}; anchor M({n1}) at step {t1}")
    print("C(n) =", show(r["word"]))
    pred = []
    for n in range(n1, n1 + K): pred += expand(r["word"], n)
    ops, _ = run(src, t1 + len(pred) + 1)
    real = list(ops[t1:t1 + len(pred)])
    lens = [len(expand(r["word"], n)) == np_.peval(r["cycle"], n) for n in range(n1, n1 + K)]
    print(f"|C(n)| = cycle length for n = {n1}..{n1 + K - 1}: {all(lens)}")
    print(f"expansion of C({n1}) C({n1 + 1}) ... C({n1 + K - 1}) equals the concrete opcode word from step {t1} "
          f"({len(pred)} steps): {pred == real}")
    if len(sys.argv) > 3:
        # sanity test of the hypothesis of Lemma S for a marker word beta on the expansion (the proof is by hand, PROOF.md):
        # occurrences of beta per cycle, and the factors between consecutive occurrences — each must occur in one cycle only
        beta = sys.argv[3]; w = "".join(map(str, pred)); starts = []; pos = 0
        for n in range(n1, n1 + K): starts.append((pos, n)); pos += len(expand(r["word"], n))
        cyc = lambda p: max(n for s, n in starts if s <= p)
        occ = [i for i in range(len(w) - len(beta) + 1) if w.startswith(beta, i)]
        per = {}
        for p in occ: per[cyc(p)] = per.get(cyc(p), 0) + 1
        where = {}
        for p, q in zip(occ, occ[1:]): where.setdefault(w[p:q + len(beta)], set()).add(cyc(p))
        print(f"occurrences of {beta} per cycle n: " + ", ".join(f"{n}:{c}" for n, c in sorted(per.items())))
        print(f"factors between consecutive occurrences: {len(where)} distinct; each confined to one cycle: "
              f"{all(len(v) == 1 for v in where.values())}")
