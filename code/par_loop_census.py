"""Run the parallel loop prover on the loop/comb runs of the census sample, one process per term, WORKERS at a time
(main agent, 2026-10-26). Usage: python par_loop_census.py [TIMEOUT] [WORKERS] [OUT] [PROVERS] [SCRIPT] [INPUT_TSV]"""
import sys, subprocess, os
from concurrent.futures import ThreadPoolExecutor
TO = int(sys.argv[1]) if len(sys.argv) > 1 else 240
WORKERS = int(sys.argv[2]) if len(sys.argv) > 2 else 4
OUT = sys.argv[3] if len(sys.argv) > 3 else "../data/par_loop_census.tsv"
PROVERS = sys.argv[4].split(",") if len(sys.argv) > 4 else ["loop_prover.py", "comb_prover.py"]
SCRIPT = sys.argv[5] if len(sys.argv) > 5 else "par_loop_prover.py"
INPUT = sys.argv[6] if len(sys.argv) > 6 else "../data/sample_union_150.tsv"
rows = [l.rstrip("\n").split("\t") for l in open(INPUT, encoding="utf-8") if l.strip()]
terms = [(r[0], r[1]) for r in rows if r[1] in PROVERS]
env = dict(os.environ, PYTHONIOENCODING="utf-8")
def one(item):
    src, prover = item
    try:
        out = subprocess.run([sys.executable, "-u", SCRIPT, src], capture_output=True, text=True,
                             timeout=TO, env=env, encoding="utf-8", errors="replace").stdout.strip()
        line = out.splitlines()[-1] if out else f"{src}: parallel run no output"
    except subprocess.TimeoutExpired:
        line = f"{src}: parallel run timeout"
    return f"{prover}\t{line}"
with open(OUT, "w", encoding="utf-8") as f, ThreadPoolExecutor(WORKERS) as ex:
    for line in ex.map(one, terms):
        f.write(line + "\n"); f.flush(); print(line, flush=True)
