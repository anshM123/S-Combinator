"""List the sampled non-counter census endpoints that neither automatic prover handles, with both verdicts (main agent).
Same sample as sample_comb.py (seed 1). Output: ../data/sample_neither_<n>.tsv (term, call-prover verdict, comb verdict)."""
import sys, random, subprocess, os
os.environ["PYTHONIOENCODING"] = "utf-8"
terms = [l.strip() for l in open("../data/endpoints_12.txt", encoding="utf-8") if l.strip()]
counters = {l.split("\t")[1] for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l}
rest = [t for t in terms if t not in counters]
n = int(sys.argv[1]); random.seed(1); sample = random.sample(rest, n)
def verdict(script, src, tmo):
    try: r = subprocess.run([sys.executable, "-u", script, src], capture_output=True, text=True, timeout=tmo, encoding="utf-8", errors="replace").stdout
    except subprocess.TimeoutExpired: return "timeout", ""
    first = r.strip().splitlines()[0] if r.strip() else "no output"
    return (first.split(": ", 1)[1] if ": " in first else first), r
out = open(f"../data/sample_neither_{n}.tsv", "w", encoding="utf-8")
for src in sample:
    a, ra = verdict("auto_prover.py", src, 60)
    a_ok = a.startswith("PROVED") and all(x.split(": ")[1].split(" ")[0].split("/")[0] == x.split(": ")[1].split(" ")[0].split("/")[1] for x in ra.splitlines() if "cross-check" in x)
    if a_ok: continue
    c, rc = verdict("comb_prover.py", src, 60)
    if c.startswith("PROVED"): continue
    out.write(f"{src}\t{a}\t{c}\n"); out.flush()
print("done")
