"""Combine the parallel loop prover censuses (values: par_loop_prover.py; lazy representation: par_loop_prover2.py)
(main agent, 2026-10-26). A term counts as certified if either sound variant certifies it.
Usage: python par_census_union.py FILE [FILE ...]"""
import sys, collections

def load(path):
    out = {}
    for line in open(path, encoding="utf-8"):
        prover, rest = line.rstrip("\n").split("\t", 1)
        term, status = rest.split(": parallel run ", 1)
        out[term] = (prover, status)
    return out

if __name__ == "__main__":
    runs = [(p, load(p)) for p in sys.argv[1:]]
    terms = []
    for _, d in runs:
        for t in d:
            if t not in terms: terms.append(t)
    proved = [t for t in terms if any(d.get(t, ("", ""))[1].startswith("PROVED") for _, d in runs)]
    by_prover = collections.Counter(next(d[t][0] for _, d in runs if t in d) for t in terms)
    ok_by_prover = collections.Counter(next(d[t][0] for _, d in runs if t in d) for t in proved)
    for p, d in runs:
        c = collections.Counter(s.split(" (")[0].split("  ")[0] for _, s in d.values())
        print(f"{p}: {len(d)} terms — " + ", ".join(f"{v} {k}" for k, v in c.most_common()))
    print(f"union: {len(proved)} of {len(terms)} certified — " +
          ", ".join(f"{pr}: {ok_by_prover[pr]}/{n}" for pr, n in by_prover.items()))
    for t in terms:
        if t not in proved:
            print("  not certified: " + t + "  [" + " | ".join(d.get(t, ("", "missing"))[1][:60] for _, d in runs) + "]")
