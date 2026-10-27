"""Parallel re-run of the three provers on the saved larger-term endpoints (main agent, 2026-10-26).
Reads the endpoints of ../data/sample_large_<NMIN>_<NMAX>_firstrun.tsv (from sample_large.py), runs call -> comb -> loop
prover per endpoint in WORKERS parallel processes (same acceptance rule as sample_large.py: PROVED and every numerical
cross-check complete), writes ../data/sample_large_<NMIN>_<NMAX>.tsv in the original order.
Usage: python sample_large_par.py NMIN NMAX WORKERS"""
import sys, os, collections
from concurrent.futures import ThreadPoolExecutor
os.environ["PYTHONIOENCODING"] = "utf-8"
from sample_large import verdict

def chain(s):
    res = []
    for script in ("auto_prover.py", "comb_prover.py", "loop_prover.py"):
        st, ok = verdict(script, s, 120)
        res.append((script, st, ok))
        if ok: break
    return res

if __name__ == "__main__":
    nmin, nmax, workers = map(int, sys.argv[1:4])
    src = f"../data/sample_large_{nmin}_{nmax}_firstrun.tsv"
    ends = [l.split("\t")[0] for l in open(src, encoding="utf-8") if l.strip()]
    with ThreadPoolExecutor(max_workers=workers) as ex:          # threads only wait on subprocesses
        results = list(ex.map(chain, ends))
    tally = collections.Counter()
    with open(f"../data/sample_large_{nmin}_{nmax}.tsv", "w", encoding="utf-8") as out:
        for s, res in zip(ends, results):
            win = next((sc for sc, st, ok in res if ok), None)
            tally[win or "unproved"] += 1
            out.write(s + "\t" + " | ".join(f"{sc}: {st[:120]}" for sc, st, ok in res) + "\n")
    print(f"{len(ends)} endpoints from random terms with {nmin}-{nmax} leaves (current provers): " +
          ", ".join(f"{k} {v}" for k, v in tally.most_common()))
