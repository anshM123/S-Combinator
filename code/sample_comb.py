"""Comb prover on the same random sample of 150 non-counter census endpoints (main agent); combined with the call-based
auto-prover verdicts (re-run) to report total coverage."""
import sys, random, collections, subprocess, os
os.environ["PYTHONIOENCODING"] = "utf-8"
terms = [l.strip() for l in open("../data/endpoints_12.txt", encoding="utf-8") if l.strip()]
counters = {l.split("\t")[1] for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l}
rest = [t for t in terms if t not in counters]
random.seed(1); sample = random.sample(rest, int(sys.argv[1]))
def verdict(script, src, tmo):
    try: r = subprocess.run([sys.executable, "-u", script, src], capture_output=True, text=True, timeout=tmo, encoding="utf-8", errors="replace").stdout
    except subprocess.TimeoutExpired: return "timeout", ""
    first = r.strip().splitlines()[0] if r.strip() else "no output"
    st = first.split(": ", 1)[1] if ": " in first else first
    return st, r
both = collections.Counter(); comb_st = collections.Counter()
for src in sample:
    a, ra = verdict("auto_prover.py", src, 60)
    a_ok = a.startswith("PROVED") and ("cross-check" not in ra or all(x.split(": ")[1].split(" ")[0].split("/")[0] == x.split(": ")[1].split(" ")[0].split("/")[1] for x in ra.splitlines() if "cross-check" in x))
    c, rc = verdict("comb_prover.py", src, 60)
    c_ok = c.startswith("PROVED")
    if c_ok:
        cc = c[c.index("cross-check ") + 12:].rstrip(")").split("/")
        c_ok = cc[0] == cc[1] and int(cc[1]) > 0
    comb_st[c.split("  ")[0]] += 1
    both["call prover" if a_ok else ("comb prover" if c_ok else "neither")] += 1
print(f"sample {len(sample)}: proved by the call prover {both['call prover']}, additionally by the comb prover {both['comb prover']}, neither {both['neither']}")
print("comb prover verdicts:", dict(comb_st))
