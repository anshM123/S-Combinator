"""Hunt for new head-run mechanisms beyond the census (main agent, 2026-10-26).
Uniformly random S-terms with NMIN..NMAX leaves (Rémy), followed leftmost-outermost through their Böhm trees to an
hnf-free endpoint as in the census; the first K distinct endpoints go to the call, comb and loop provers (WORKERS in
parallel, 120 s each, a proof counts only with complete numerical cross-checks). Unproved endpoints are the candidates
for mechanisms the provers do not know (or for non-morphic runs). Small sample, not a census.
Usage: python sample_hunt.py NMIN NMAX K SEED WORKERS  ->  ../data/sample_hunt_<NMIN>_<NMAX>.tsv"""
import sys, random, os, collections
from concurrent.futures import ThreadPoolExecutor
sys.setrecursionlimit(1000000)
os.environ["PYTHONIOENCODING"] = "utf-8"
from symb import show
from lo_bt import normalises
from lo_census import endpoint
from sample_large import remy, verdict

def chain(s):
    res = []
    for script, tmo in (("loop_prover.py", 120), ("comb_prover.py", 120), ("auto_prover.py", 120), ("nest_prover.py", 300)):
        st, ok = verdict(script, s, tmo)                                    # fast prover first; nested loops last
        res.append((script, st, ok))
        if ok: break
    return res

if __name__ == "__main__":
    nmin, nmax, K, seed, workers = map(int, sys.argv[1:6])
    random.seed(seed); seen = []; tried = 0
    while len(seen) < K and tried < 60 * K:
        tried += 1
        t = remy(random.randint(nmin, nmax))
        try:
            if normalises(t): continue
            how, u, lvl = endpoint(t, 12)
        except (RecursionError, MemoryError):
            continue
        if how != "bottom": continue
        s = show(u)
        if s not in seen and len(s) < 4000: seen.append(s)
    with ThreadPoolExecutor(max_workers=workers) as ex:
        results = list(ex.map(chain, seen))
    tally = collections.Counter()
    with open(f"../data/sample_hunt_{nmin}_{nmax}.tsv", "w", encoding="utf-8") as out:
        for s, res in zip(seen, results):
            win = next((sc for sc, st, ok in res if ok), None)
            tally[win or "unproved"] += 1
            out.write(s + "\t" + (win or "unproved") + "\t" + " | ".join(f"{sc}: {st[:100]}" for sc, st, ok in res) + "\n")
    print(f"{len(seen)} distinct endpoints from {tried} random terms with {nmin}-{nmax} leaves: " +
          ", ".join(f"{k} {v}" for k, v in tally.most_common()))
