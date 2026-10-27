"""Try every head-run prover on a list of terms (main agent, 2026-10-26): loop, nested-loop, call and comb provers, in
that order, each in its own process with a timeout; the first PROVED wins. Reports the terms no prover certifies.
Usage: python prove_any.py TERMS_FILE [TIMEOUT]   (TERMS_FILE: one term per line; other text after the term is ignored)"""
import sys, subprocess, os
PROVERS = ["loop_prover.py", "nest_prover.py", "auto_prover.py", "comb_prover.py"]
TO = int(sys.argv[2]) if len(sys.argv) > 2 else 300
terms = []
for line in open(sys.argv[1], encoding="utf-8"):
    parts = line.split()
    if parts and parts[0].startswith("S") and parts[0] not in terms: terms.append(parts[0])
env = dict(os.environ, PYTHONIOENCODING="utf-8")
unproved = []
for t in terms:
    verdict = None
    for p in PROVERS:
        try:
            out = subprocess.run([sys.executable, "-u", p, t], capture_output=True, text=True, timeout=TO, env=env,
                                 encoding="utf-8", errors="replace").stdout
        except subprocess.TimeoutExpired:
            continue
        if "PROVED" in out.split("\n")[0] or f"{t}: PROVED" in out:
            verdict = p; break
    print(f"{t:45s} {('PROVED by ' + verdict) if verdict else 'NOT PROVED'}", flush=True)
    if verdict is None: unproved.append(t)
print(f"{len(terms) - len(unproved)}/{len(terms)} proved; unproved: {unproved}")
