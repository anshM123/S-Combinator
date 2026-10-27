"""Generate lean/BTInv.lean = lean/Standard.lean (without its #print lines) + code/btinv_tail.lean.txt (main agent,
2026-10-27): F5, Böhm trees are invariant under reduction. Usage: python gen_btinv.py"""
import re
s = open("../lean/Standard.lean", encoding="utf-8").read()
s = re.sub(r"#print axioms \w+\n", "", s)
s = s.replace("Proposition CF and the head normalisation theorem — machine-checked",
              "F5 (Böhm trees are invariant under reduction), on top of confluence, Proposition CF and the head normalisation theorem — machine-checked")
s = s + open("btinv_tail.lean.txt", encoding="utf-8").read()
open("../lean/BTInv.lean", "w", encoding="utf-8").write(s)
print("lean/BTInv.lean written,", s.count("\n"), "lines")
