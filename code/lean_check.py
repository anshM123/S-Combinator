"""Compile the Lean 4 formalisation (main agent, 2026-10-26) and report whether every theorem is free of `sorry`.
Uses an installed elan toolchain directly (no network, no change to the elan default).
Usage: python lean_check.py [FILE]   (default ../lean/URCore.lean)"""
import sys, os, subprocess, glob, re
path = sys.argv[1] if len(sys.argv) > 1 else os.path.join("..", "lean", "URCore.lean")
cands = sorted(glob.glob(os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean*")))
lean = next((c for c in cands if os.path.basename(c) in ("lean", "lean.exe")), None)
if lean is None:
    print("LEAN NOT FOUND"); sys.exit(1)
out = subprocess.run([lean, path], capture_output=True, text=True, encoding="utf-8", errors="replace")
text = out.stdout + out.stderr
errors = [l for l in text.splitlines() if ": error" in l]
axioms = re.findall(r"'(\w+)' depends on axioms: \[([^\]]*)\]", text)
axioms += [(name, "(none)") for name in re.findall(r"'(\w+)' does not depend on any axioms", text)]
bad = [name for name, ax in axioms if "sorryAx" in ax]
print(f"exit {out.returncode}, {len(errors)} errors, {len(axioms)} theorems checked, axioms used: "
      f"{sorted({a.strip() for _, ax in axioms for a in ax.split(',')})}")
for name, ax in axioms: print(f"  {name}: {ax}")
print("LEAN OK: no errors, no sorry" if out.returncode == 0 and not errors and not bad and axioms else "LEAN CHECK FAILED")
