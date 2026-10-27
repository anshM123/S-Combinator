"""Whole-list certificates (call_residue.py) for every call-certified term (main agent, 2026-10-26): the 145 proved counters
(data/census_auto.txt), the call-prover terms of data/sample_union_150.tsv and of data/sample_large_13_16.tsv.
WORKERS parallel processes. Output: ../data/wholelist_calls.tsv and a tally."""
import sys, os, subprocess, collections, re
from concurrent.futures import ThreadPoolExecutor
os.environ["PYTHONIOENCODING"] = "utf-8"

def terms():
    out = []
    for l in open("../data/census_auto.txt", encoding="utf-8"):
        if l.endswith(": PROVED\n") and not l.startswith(" "): out.append(("counters", l.split(": ")[0]))
    for l in open("../data/sample_union_150.tsv", encoding="utf-8"):
        f = l.rstrip("\n").split("\t")
        if len(f) >= 2 and f[1] == "auto_prover.py": out.append(("census sample", f[0]))
    for l in open("../data/sample_large_13_16.tsv", encoding="utf-8"):
        f = l.rstrip("\n").split("\t")
        if len(f) >= 2 and f[1].startswith("auto_prover.py: PROVED"): out.append(("13-16 sample", f[0]))
    return out

def one(src):
    try:
        r = subprocess.run([sys.executable, "-u", "call_residue.py", src], capture_output=True, text=True, timeout=600,
                           encoding="utf-8", errors="replace").stdout.strip()
    except subprocess.TimeoutExpired:
        return "timeout"
    return r.splitlines()[0].split(": ", 1)[1] if r and ": " in r else "no output"

if __name__ == "__main__":
    T = terms(); workers = int(sys.argv[1])
    with ThreadPoolExecutor(max_workers=workers) as ex:
        res = list(ex.map(lambda t: one(t[1]), T))
    tally = collections.Counter()
    with open("../data/wholelist_calls.tsv", "w", encoding="utf-8") as out:
        for (grp, src), st in zip(T, res):
            m = re.search(r"checked at (\d+)/(\d+) events", st)
            good = st.startswith("whole list certified") and m and m.group(1) == m.group(2) and int(m.group(2)) > 0
            tally[(grp, "certified" if good else re.sub(r"\(.*", "", st)[:60].strip())] += 1
            out.write(f"{grp}\t{src}\t{st}\n")
    for k, v in sorted(tally.items()): print(k, v)
