"""Generate lean/ReadCost.lean = lean/BarrierJ.lean (without its #print lines) + code/readcost_tail.lean.txt (main agent,
2026-10-27): Lemma 11 (full-read principle) and Lemma 12 (right-depth cost). Usage: python gen_readcost.py"""
import re
s = open("../lean/BarrierJ.lean", encoding="utf-8").read()
s = re.sub(r"#print axioms \w+\n", "", s)
s = s.replace("Lemma 8 (data conservation), its corollary, and Theorem J (global writes) — machine-checked",
              "Lemmas 11 (full-read principle) and 12 (right-depth cost), on top of Lemma 8 and Theorem J — machine-checked")
s = s + open("readcost_tail.lean.txt", encoding="utf-8").read()
open("../lean/ReadCost.lean", "w", encoding="utf-8").write(s)
print("lean/ReadCost.lean written,", s.count("\n"), "lines")
