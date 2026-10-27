"""Generate lean/TheoremT.lean = lean/Confluence.lean (without its #print lines) + code/theoremT_tail.lean.txt (main agent,
2026-10-27): Church's theorem for S (F3), finite multiway graphs, Theorem T. Usage: python gen_theoremT.py"""
import re
s = open("../lean/Confluence.lean", encoding="utf-8").read()
s = re.sub(r"#print axioms \w+\n", "", s)
s = s.replace("Confluence of S-reduction and Proposition MW(d),(e) — machine-checked",
              "Theorem T (termination is all-or-nothing; Church's theorem F3 for S; finite multiway graphs), on top of confluence and Proposition MW(e) — machine-checked")
s = s + open("theoremT_tail.lean.txt", encoding="utf-8").read()
open("../lean/TheoremT.lean", "w", encoding="utf-8").write(s)
print("lean/TheoremT.lean written,", s.count("\n"), "lines")
