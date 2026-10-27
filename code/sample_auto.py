"""Auto-prover on a sample of non-counter census endpoints (main agent)."""
import sys, random, collections, subprocess
terms = [l.strip() for l in open("../data/endpoints_12.txt", encoding="utf-8") if l.strip()]
counters = {l.split("\t")[1] for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l}
rest = [t for t in terms if t not in counters]
random.seed(1); sample = random.sample(rest, int(sys.argv[1]))
st = collections.Counter(); ex = collections.defaultdict(list)
for src in sample:
    try: r = subprocess.run([sys.executable, "-u", "auto_prover.py", src], capture_output=True, text=True, timeout=60).stdout
    except subprocess.TimeoutExpired: r = f"{src}: timeout"
    first = r.strip().splitlines()[0] if r.strip() else f"{src}: no output"
    k = first.split(": ", 1)[1] if ": " in first else first
    if k == "PROVED":
        cc = [l for l in r.splitlines() if "cross-check" in l]
        if cc:
            a, b = cc[0].split(": ")[1].split(" ")[0].split("/")
            k = "PROVED, cross-check passed" if a == b and int(b) > 0 else ("PROVED, cross-check FAILED" if a != b else "PROVED, no cross-check data")
        else: k = "PROVED, no cross-check data"
    st[k] += 1
    if len(ex[k]) < 3: ex[k].append(src)
print(f"{len(rest)} non-counter endpoints; sample of {len(sample)}: {dict(st)}")
for k, v in ex.items(): print("  ", k, v)
