"""All three exact-structure provers on the random sample of non-counter census endpoints (main agent, 2026-10-26).
Same sample as sample_auto.py / sample_comb.py (seed 1). Per term: call prover (auto_prover.py), then comb prover, then
loop prover; a proof counts only if it is PROVED and its numerical cross-check passes completely (a/a, a > 0).
Output: ../data/sample_union_<n>.tsv (term, winning prover or 'unproved', verdicts) and a summary line."""
import sys, random, subprocess, os, re, collections
os.environ["PYTHONIOENCODING"] = "utf-8"
terms = [l.strip() for l in open("../data/endpoints_12.txt", encoding="utf-8") if l.strip()]
counters = {l.split("\t")[1] for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l}
rest = [t for t in terms if t not in counters]
n = int(sys.argv[1]); random.seed(1); sample = random.sample(rest, n)

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
    return st, bool(cc) and all(a == b and int(b) > 0 for a, b in cc)

out = open(f"../data/sample_union_{n}.tsv", "w", encoding="utf-8"); tally = collections.Counter()
for src in sample:
    res = []
    for script, tmo in (("auto_prover.py", 120), ("comb_prover.py", 60), ("loop_prover.py", 180)):
        st, ok = verdict(script, src, tmo); res.append((script, st, ok))
        if ok: break
    win = next((sc for sc, st, ok in res if ok), "unproved")
    tally[win] += 1
    out.write(src + "\t" + win + "\t" + " | ".join(f"{sc}: {st[:110]}" for sc, st, ok in res) + "\n"); out.flush()
print(f"sample of {n} non-counter endpoints: " + ", ".join(f"{k} {v}" for k, v in tally.most_common()))
