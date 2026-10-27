"""Generate lean/NStar.lean = lean/BarrierJ.lean (without its #print lines) + code/nstar_tail.lean.txt (main agent,
2026-10-27). Usage: python gen_nstar.py"""
import re
s = open("../lean/BarrierJ.lean", encoding="utf-8").read()
s = re.sub(r"#print axioms \w+\n", "", s)
s = s.replace("Lemma 8 (data conservation), its corollary, and Theorem J (global writes) — machine-checked",
              "Theorem N* (potential bound for counters), on top of Lemma 8 and Theorem J — machine-checked")
s = s + open("nstar_tail.lean.txt", encoding="utf-8").read()
open("../lean/NStar.lean", "w", encoding="utf-8").write(s)
print("lean/NStar.lean written,", s.count("\n"), "lines")
