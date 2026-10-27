"""Robustness of the three exact-structure provers beyond the 12-leaf census (main agent, 2026-10-26).
Uniformly random S-terms with NMIN..NMAX leaves (Rémy's algorithm), followed leftmost-outermost through their Böhm tree
to an hnf-free endpoint exactly as in the census (lo_census.endpoint); the first K distinct endpoints are given to the call
prover (auto_prover.py), the comb prover (comb_prover.py) and the loop prover (loop_prover.py). Small sample, not a census.
Usage: python sample_large.py NMIN NMAX K SEED   ->  ../data/sample_large_<NMIN>_<NMAX>.tsv"""
import sys, random, subprocess, os, re, collections
sys.setrecursionlimit(1000000)
os.environ["PYTHONIOENCODING"] = "utf-8"
from symb import show
from lo_bt import normalises
from lo_census import endpoint

def remy(n):
    """uniform random binary tree with n leaves (Rémy): pick a uniform node x, move its content to a new node, and make x
    an application of that node and a new leaf (on a random side)"""
    root = ["L"]; nodes = [root]
    for _ in range(n - 1):
        x = random.choice(nodes)
        old = list(x); leaf = ["L"]
        x[:] = ["A", old, leaf] if random.random() < 0.5 else ["A", leaf, old]
        nodes.append(old); nodes.append(leaf)
    def conv(x): return "S" if x[0] == "L" else (conv(x[1]), conv(x[2]))
    return conv(root)

def verdict(script, src, tmo):
    try:
        r = subprocess.run([sys.executable, "-u", script, src], capture_output=True, text=True, timeout=tmo,
                           encoding="utf-8", errors="replace").stdout.strip()
    except subprocess.TimeoutExpired:
        return "timeout", False
    first = r.splitlines()[0] if r else "no output"
    st = first.split(": ", 1)[1] if ": " in first else first
    if not st.startswith("PROVED"): return st, False
    cc = re.findall(r"cross-check:? (\d+)/(\d+)", r)
    ok = all(a == b and int(b) > 0 for a, b in cc) if cc else True
    return st, ok

if __name__ == "__main__":
    nmin, nmax, K, seed = map(int, sys.argv[1:5])
    random.seed(seed); seen = []; tried = 0
    if len(sys.argv) > 5 and sys.argv[5] == "rerun":          # same endpoints as the saved run, current provers
        seen = [l.split("\t")[0] for l in open(f"../data/sample_large_{nmin}_{nmax}.tsv", encoding="utf-8") if l.strip()][:K]
        tried = -1
    while len(seen) < K and tried < 50 * K:
        tried += 1
        t = remy(random.randint(nmin, nmax))
        if normalises(t): continue
        how, u, lvl = endpoint(t, 12)
        if how != "bottom": continue
        s = show(u)
        if s not in seen: seen.append(s)
    out = open(f"../data/sample_large_{nmin}_{nmax}.tsv", "w", encoding="utf-8"); tally = collections.Counter()
    for s in seen:
        res = []
        for script in ("auto_prover.py", "comb_prover.py", "loop_prover.py"):
            st, ok = verdict(script, s, 120)
            res.append((script, st, ok))
            if ok: break
        winner = next((sc for sc, st, ok in res if ok), None)
        tally[winner or "unproved"] += 1
        out.write(s + "\t" + " | ".join(f"{sc}: {st[:120]}" for sc, st, ok in res) + "\n"); out.flush()
    print(f"{len(seen)} distinct endpoints from {tried} random terms with {nmin}-{nmax} leaves: " +
          ", ".join(f"{k} {v}" for k, v in tally.most_common()))
