"""Loop prover (loop_prover.py) on the sampled census endpoints that neither the call prover nor the comb prover proves
(data/sample_neither_<n>.tsv, from sample_neither.py) — main agent. Output: data/sample_loop_<n>.tsv and a summary."""
import sys, subprocess, os, collections, re
os.environ["PYTHONIOENCODING"] = "utf-8"
n = sys.argv[1]
rows = [l.rstrip("\n").split("\t") for l in open(f"../data/sample_neither_{n}.tsv", encoding="utf-8") if l.strip()]
out = open(f"../data/sample_loop_{n}.tsv", "w", encoding="utf-8"); cnt = collections.Counter()
for src, *_ in rows:
    try:
        r = subprocess.run([sys.executable, "-u", "loop_prover.py", src], capture_output=True, text=True, timeout=180,
                           encoding="utf-8", errors="replace").stdout.strip()
    except subprocess.TimeoutExpired:
        r = f"{src}: timeout"
    st = r.splitlines()[0].split(": ", 1)[1] if r and ": " in r.splitlines()[0] else "no output"
    ok = st.startswith("PROVED")
    if ok:
        m = re.search(r"cross-check (\d+)/(\d+)", st)
        ok = m is not None and m.group(1) == m.group(2) and int(m.group(2)) > 0
    cnt["PROVED" if ok else st.split(" (")[0]] += 1
    out.write(f"{src}\t{st}\n"); out.flush()
print(f"{len(rows)} terms: " + ", ".join(f"{k} {v}" for k, v in cnt.most_common()))
