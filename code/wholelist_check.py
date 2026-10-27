"""Whole-list certificates (Corollary LP′) for the loop- and comb-certified terms of the two samples (main agent, 2026-10-26).
Runs loop_prover.py (with its residue pass) on every term that data/sample_union_150.tsv or data/sample_large_13_16.tsv
lists as certified by the comb or loop prover, WORKERS in parallel; reports how many get a whole-list certificate whose
30-entry numerical test passes at every anchor. Output: ../data/wholelist_check.tsv"""
import sys, os, re, subprocess, collections
from concurrent.futures import ThreadPoolExecutor
os.environ["PYTHONIOENCODING"] = "utf-8"

def terms():
    out = []
    for l in open("../data/sample_union_150.tsv", encoding="utf-8"):
        f = l.rstrip("\n").split("\t")
        if len(f) >= 2 and f[1] in ("loop_prover.py", "comb_prover.py"): out.append(("census", f[0]))
    for l in open("../data/sample_large_13_16.tsv", encoding="utf-8"):
        f = l.rstrip("\n").split("\t")
        if len(f) >= 2:
            win = None
            for p in f[1].split(" | "):
                sc, st = p.split(": ", 1)
                if st.startswith("PROVED"): win = sc; break
            if win in ("loop_prover.py", "comb_prover.py"): out.append(("13-16", f[0]))
    return out

def one(src):
    try:
        r = subprocess.run([sys.executable, "-u", "loop_prover.py", src], capture_output=True, text=True, timeout=300,
                           encoding="utf-8", errors="replace").stdout
    except subprocess.TimeoutExpired:
        return "timeout", None
    lines = r.strip().splitlines()
    st = lines[0].split(": ", 1)[1] if lines and ": " in lines[0] else "no output"
    m = re.search(r"cross-check (\d+)/(\d+)", st)
    if not st.startswith("PROVED") or not m or m.group(1) != m.group(2): return "not proved: " + st[:60], None
    w = re.search(r"residue of (\d+) items per cycle; first 30 entries checked at (\d+)/(\d+) anchors", r)
    if not w: return "PROVED, whole list not determined", None
    return "PROVED", (int(w.group(1)), int(w.group(2)), int(w.group(3)))

if __name__ == "__main__":
    T = terms(); workers = int(sys.argv[1])
    with ThreadPoolExecutor(max_workers=workers) as ex:
        res = list(ex.map(lambda t: one(t[1]), T))
    tally = collections.Counter()
    with open("../data/wholelist_check.tsv", "w", encoding="utf-8") as out:
        for (grp, src), (st, kw) in zip(T, res):
            good = st == "PROVED" and kw is not None and kw[1] == kw[2] and kw[2] > 0
            tally[(grp, "whole list certified" if good else st[:40])] += 1
            out.write(f"{grp}\t{src}\t{st}\t{kw}\n")
    for k, v in sorted(tally.items()): print(k, v)
