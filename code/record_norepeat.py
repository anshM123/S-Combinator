"""Record lean/NoRepeat.lean (main agent, 2026-10-27 evening). Run once from code/: python record_norepeat.py"""
import sys

root = ".."


def edit(fn, old, new):
    p = root + "/" + fn
    s = open(p, encoding="utf-8").read()
    if old not in s:
        sys.exit("anchor not found in %s: %r" % (fn, old[:80]))
    s = s.replace(old, new, 1)
    open(p, "w", encoding="utf-8").write(s)


old = ' ("E108 descents: one-redex evolutions with descents into arguments, 9 leaves (two descend once, one for ever)",'
new = (' ("Lean 4: leftmost walks never repeat a node, under Waldmann\'s no-spiral theorem as an explicit hypothesis",\n'
       '  ["lean_check.py", "../lean/NoRepeat.lean"], [r"LEAN OK: no errors, no sorry", r"no_repeat: propext, Classical.choice, Quot.sound", r"no_periodic: propext, Classical.choice, Quot.sound"], 600),\n' + old)
edit("code/verify_all.py", old, new)

old = ("PROVED (hand; relies on the cited "
       "no-spiral theorem; not machine-checked). Conjecture J itself remains OPEN |")
new = ("PROVED and MACHINE-CHECKED with the no-spiral theorem as an explicit hypothesis (lean/NoRepeat.lean: `lchild_red`, "
       "`no_repeat`, `no_periodic`; Waldmann's theorem itself is cited, not formalised). Conjecture J itself remains OPEN |")
edit("STATUS.md", old, new)

old = ("cited, not machine-checked): no leftmost walk repeats a node, so no infinite leftmost walk is eventually periodic.\n"
       "The J agent was stopped by the usage limit before it could go further.")
new = ("cited): no leftmost walk repeats a node, so no infinite leftmost walk is eventually periodic. The J agent was stopped\n"
       "by the usage limit; the main agent then MACHINE-CHECKED the argument with the no-spiral theorem as an explicit\n"
       "hypothesis `NoSpiral` (lean/NoRepeat.lean: `lchild_red` — every leftmost step reduces the node to a non-trivial\n"
       "context of the child, with at least one step at computed nodes; `no_repeat`; `no_periodic`).")
edit("PROOF.md", old, new)

old = "| Leftmost-path finite half reduced to Conjecture J | `AgentEMA.lean` |"
new = ("| No repeated node on leftmost walks (given Waldmann's no-spiral theorem) | `NoRepeat.lean` | a leftmost Böhm-tree "
       "walk never visits the same node twice, so no infinite leftmost walk is eventually periodic; the no-spiral theorem "
       "(published, BEKW Theorem 14) is an explicit hypothesis |\n" + old)
edit("RESULTS.md", old, new)
print("recorded")
