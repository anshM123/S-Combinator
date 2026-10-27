"""Record the partial results of the two agents stopped by the weekly usage limit at about 12:46 EDT
(main agent, 2026-10-27, 17:20 EDT). Run once from code/: python record_stopped_agents.py"""
import sys, os

root = ".."


def edit(fn, old, new):
    p = root + "/" + fn
    s = open(p, encoding="utf-8").read()
    if old not in s:
        sys.exit("anchor not found in %s: %r" % (fn, old[:80]))
    s = s.replace(old, new, 1)
    open(p, "w", encoding="utf-8").write(s)


if not os.path.exists(root + "/lean/AgentBilinear.lean"):
    sys.exit("missing lean/AgentBilinear.lean")

old = ' ("E108 descents: one-redex evolutions with descents into arguments, 9 leaves (two descend once, one for ever)",'
new = (' ("Lean 4 (race agent): Theorem B2, the ReplaceAll normalisation time of n-bar m-bar S is exactly nm + 2n - 2",\n'
       '  ["lean_check.py", "../lean/AgentBilinear.lean"], [r"LEAN OK: no errors, no sorry", r"theoremB2: propext, Classical.choice, Quot.sound"], 900),\n' + old)
edit("code/verify_all.py", old, new)

old = "| R103 | **Leftmost-path finite half reduced to Conjecture J"
new = ("| R105 | **No leftmost walk repeats a node (J agent, stopped early by the usage limit):** every leftmost step makes the "
       "next node a proper subterm of a reduct of the current one, so a repeated node would be a spiral M ->+ C[M], which "
       "Waldmann's no-spiral theorem (2000; BEKW Theorem 14) excludes. Hence no infinite leftmost walk is eventually periodic, "
       "and the jump targets of a walk with infinitely many jumps are pairwise distinct | PROVED (hand; relies on the cited "
       "no-spiral theorem; not machine-checked). Conjecture J itself remains OPEN |\n"
       "| R104 | **Exact bilinear ReplaceAll clock and a race family (race agent, stopped early by the usage limit; "
       "lean/AgentBilinear.lean):** Theorem B2 — under ReplaceAll, n-bar m-bar S becomes normal at exactly pass nm + 2n - 2 "
       "(`theoremB2`, with `lemmaU`, `num_S_time`). The terms S (S N_12 (n-bar m-bar S)) (k-bar k-bar S) form a family whose "
       "root pattern fires exactly when nm + 2n < k^2 + 2k, a non-separable comparison (COMPUTATIONALLY CERTIFIED for all "
       "n, m, k <= 11). This is one term per parameter triple, NOT the single generating term Theorem RR needs | "
       "MACHINE-CHECKED (B2) / COMPUTATIONALLY CERTIFIED (family) / RR hypothesis OPEN |\n" + old)
edit("STATUS.md", old, new)

old = "* **Reading.** Choosing ReplaceAll only re-times the leftmost-outermost skeleton and changes syntax inside list"
new = ("* **Race material, partial (race agent, stopped by the usage limit at about 12:46):** Theorem B2 is MACHINE-CHECKED\n"
       "  (lean/AgentBilinear.lean, `theoremB2`): under ReplaceAll, n-bar m-bar S becomes normal at exactly pass nm + 2n - 2,\n"
       "  a bilinear clock. The family S (S N_12 (n-bar m-bar S)) (k-bar k-bar S) gives a race whose root pattern fires\n"
       "  exactly when nm + 2n < k^2 + 2k (COMPUTATIONALLY CERTIFIED for n, m, k <= 11, race_family.py). It is a family of\n"
       "  closed terms, one per parameter triple; Theorem RR needs one term whose single run creates such races for all\n"
       "  tuples, which remains OPEN. A finite scan (weight_scan.py) found that front-wrapping layers other than the numeral\n"
       "  layer have tied or non-affine weights, a hint that data-blind code cannot weight parameters independently.\n" + old)
edit("PROOF.md", old, new)

old = ("(EXPERIMENTALLY SUPPORTED: no late jump among all 58,786 terms with 12 leaves and 240,000 random compositions; no\n"
       "periodic leftmost walk found).")
new = ("(EXPERIMENTALLY SUPPORTED: no late jump among all 58,786 terms with 12 leaves and 240,000 random compositions; no\n"
       "periodic leftmost walk found). PROVED (J agent, 12:47, relying on Waldmann's no-spiral theorem, BEKW Theorem 14,\n"
       "cited, not machine-checked): no leftmost walk repeats a node, so no infinite leftmost walk is eventually periodic.\n"
       "The J agent was stopped by the usage limit before it could go further.")
edit("PROOF.md", old, new)

old = "## The EM agent's result (12:27 EDT)"
new = ("## How the day ended\n"
       "At about 12:46 EDT the user's weekly usage limit was reached. The two running agents (Conjecture J; race material for\n"
       "Theorem RR) stopped mid-task, and the main agent could not act until the limit reset at 17:00, so the planned 16:30\n"
       "final integration happened at 17:20 instead. The auto-save loop had pushed everything up to 13:16. Partial results\n"
       "of the two stopped agents: Theorem B2, an exact bilinear ReplaceAll clock (machine-checked), plus a certified race\n"
       "family (STATUS R104); and 'no leftmost walk repeats a node', a hand proof that relies on Waldmann's no-spiral theorem\n"
       "(R105). Conjecture J and Theorem RR's hypothesis remain open.\n\n" + old)
edit("SESSION_SUMMARY_2026-10-27.md", old, new)

old = "* **EM agent (12:27 EDT):**"
new = ("* **End of the run (17:20 EDT):** the weekly usage limit stopped the last two agents at about 12:46. Partial results:\n"
       "  an exact bilinear ReplaceAll clock (Theorem B2, machine-checked) with a certified race family, and a proof that no\n"
       "  leftmost walk repeats a node (relying on Waldmann's no-spiral theorem). Open as before: Conjecture J (the last step\n"
       "  to decidable leftmost-path finiteness) and Theorem RR's hypothesis (the last step to a ReplaceAll universality\n"
       "  construction).\n" + old)
edit("PRIZE_ASSESSMENT.md", old, new)
print("recorded")
