"""Run the automatic prover on every counter-type endpoint of the 12-leaf census (main agent)."""
import sys, collections, subprocess
rows = [l.rstrip("\n").split("\t") for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l]
stat = collections.Counter(); out = open("../data/census_auto.txt", "w", encoding="utf-8")
for cls_, src, *_ in rows:
    try:
        r = subprocess.run([sys.executable, "-u", "auto_prover.py", src], capture_output=True, text=True, timeout=120).stdout
    except subprocess.TimeoutExpired:
        r = f"{src}: timeout"
    first = r.strip().splitlines()[0] if r.strip() else f"{src}: no output"
    st = first.split(": ", 1)[1] if ": " in first else first
    if st == "PROVED":
        cc = [l for l in r.splitlines() if "cross-check" in l]
        st = "PROVED, cross-check " + (cc[0].split(": ")[1].split(" ")[0] if cc else "missing")
    stat[(cls_, st)] += 1
    out.write(r.strip() + "\n"); out.flush()
for k, v in sorted(stat.items()): print(f"{k[0]:16s} {k[1]:60s} {v}")
