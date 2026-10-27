"""Add the 10:12 agent results to PRIZE_ASSESSMENT.md and the session summary (main agent, 2026-10-27).
Run once from code/: python record_final_agents2.py"""
import sys

root = ".."


def edit(fn, old, new):
    p = root + "/" + fn
    s = open(p, encoding="utf-8").read()
    if old not in s:
        sys.exit("anchor not found in %s: %r" % (fn, old[:80]))
    s = s.replace(old, new, 1)
    open(p, "w", encoding="utf-8").write(s)


old = "* **Work in progress (3 workers until 16:30 EDT):**"
new = ("* **Final agent results (10:12 EDT):** (1) R3 is machine-checked without conditions for every single-wrapper handler\n"
       "  of ordered data with one occurrence of the predecessor, so the two-transfer chain bound holds for every chain whose\n"
       "  second transfer is single-wrapper or FH (all observed chains); multi-wrapper R3 is open. (2) The leftmost-path finite\n"
       "  half (and the rightmost one) is reduced in Lean to one conjecture, EM: every infinite leftmost walk is eventually\n"
       "  monotone (finitely many pops, jumps and returns). Proving EM would make leftmost-path finiteness decidable via the\n"
       "  36-class model (the other half is Proposition Q″), settling detector class (D2′) for that path.\n" + old)
edit("PRIZE_ASSESSMENT.md", old, new)

old = "## Experiments and negative results this session"
new = ("## The last two agents' results (10:11 and 10:12 EDT)\n"
       "* S1 agent (lean/AgentR3G.lean, 8,375 lines): R3 machine-checked without conditions for every single-wrapper handler\n"
       "  of ordered data with at most one occurrence of the predecessor (`r3_single_unc`, `r3_rc_unc`), via Theorem S1,\n"
       "  Lemma YT and the barrier order. The chain bound (at most 2 proper transfers) now holds whenever the second transfer\n"
       "  is single-wrapper or FH, which covers every chain observed. Multi-wrapper handlers: machine-checked in classes only.\n"
       "* Universality agent (lean/AgentFiniteHalfGen.lean, 6,146 lines): no universal construction. On the leftmost-path\n"
       "  finite half: Omega and reload families with any second component are excluded from flag-0 classes, and the whole\n"
       "  finite half is reduced to Conjecture EM (every infinite leftmost walk is eventually monotone); the same for the\n"
       "  rightmost path under EM_R.\n\n" + old)
edit("SESSION_SUMMARY_2026-10-27.md", old, new)
print("recorded")
