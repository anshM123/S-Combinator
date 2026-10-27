"""Whole-list certificates for the endpoints of data/sample_hunt_<NMIN>_<NMAX>.tsv (main agent, 2026-10-26): loop-prover
runs via loop_prover.py's whole-list line, call-prover runs via call_residue.py; the endpoint left unproved by the hunt is
retried with the loop prover. WORKERS in parallel. Output: ../data/wholelist_hunt_<NMIN>_<NMAX>.tsv and a tally."""
import sys, os, re, subprocess, collections
from concurrent.futures import ThreadPoolExecutor
os.environ["PYTHONIOENCODING"] = "utf-8"

def one(item):
    src, win = item
    script = "call_residue.py" if win == "auto_prover.py" else "loop_prover.py"
    try:
        r = subprocess.run([sys.executable, "-u", script, src], capture_output=True, text=True, timeout=900,
                           encoding="utf-8", errors="replace").stdout
    except subprocess.TimeoutExpired:
        return "timeout"
    if script == "call_residue.py":
        m = re.search(r"whole list certified .*checked at (\d+)/(\d+) events", r)
    else:
        if not re.search(r": PROVED .*cross-check (\d+)/\1", r): return "loop proof failed"
        m = re.search(r"first 30 entries checked at (\d+)/(\d+) anchors", r)
    return "certified" if m and m.group(1) == m.group(2) and int(m.group(2)) > 0 else "not certified"

if __name__ == "__main__":
    nmin, nmax, workers = sys.argv[1], sys.argv[2], int(sys.argv[3])
    rows = [l.rstrip("\n").split("\t") for l in open(f"../data/sample_hunt_{nmin}_{nmax}.tsv", encoding="utf-8") if l.strip()]
    items = [(r[0], r[1]) for r in rows]
    with ThreadPoolExecutor(max_workers=workers) as ex:
        res = list(ex.map(one, items))
    tally = collections.Counter(res)
    with open(f"../data/wholelist_hunt_{nmin}_{nmax}.tsv", "w", encoding="utf-8") as out:
        for (src, win), st in zip(items, res): out.write(f"{src}\t{win}\t{st}\n")
    print(f"{len(items)} endpoints: " + ", ".join(f"{k} {v}" for k, v in tally.most_common()))
