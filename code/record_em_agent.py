"""Record the EM agent's final result (main agent, 2026-10-27, 12:30 EDT). Run once from code/: python record_em_agent.py"""
import sys, os

root = ".."


def edit(fn, old, new):
    p = root + "/" + fn
    s = open(p, encoding="utf-8").read()
    if old not in s:
        sys.exit("anchor not found in %s: %r" % (fn, old[:80]))
    s = s.replace(old, new, 1)
    open(p, "w", encoding="utf-8").write(s)


if not os.path.exists(root + "/lean/AgentEMA.lean"):
    sys.exit("missing lean/AgentEMA.lean")

old = ' ("E108 descents: one-redex evolutions with descents into arguments, 9 leaves (two descend once, one for ever)",'
new = (' ("Lean 4 (EM agent): leftmost-path finite half reduced to Conjecture J (finitely many jumps); cases (a\') and (b) of EM closed",\n'
       '  ["lean_check.py", "../lean/AgentEMA.lean"], [r"LEAN OK: no errors, no sorry", r"SC.finite_half_of_J: propext, Classical.choice, Quot.sound", r"SC.EM_deep: propext, Classical.choice, Quot.sound", r"CA.depth_to_infinity: propext, Classical.choice, Quot.sound"], 2400),\n' + old)
edit("code/verify_all.py", old, new)

old = ("do the same for R19 under Conjecture EM_R. OPEN: EM itself; it can fail only through (a') a jump-free walk returning\n"
       "infinitely often to nodes q·S with infinitely many T3/T4 steps, (b) unbounded depth with infinitely many pops or\n"
       "returns, or (c) infinitely many jumps.")
new = ("do the same for R19 under Conjecture EM_R. OPEN at 10:12: EM itself; it can fail only through (a') a jump-free walk\n"
       "returning infinitely often to nodes q·S with infinitely many T3/T4 steps, (b) unbounded depth with infinitely many pops\n"
       "or returns, or (c) infinitely many jumps.\n"
       "**Cases (a') and (b) CLOSED, MACHINE-CHECKED (EM agent, 12:27; lean/AgentEMA.lean, 8,480 lines, 65 theorems, re-compiled\n"
       "by the main agent):** `CA.chain_T2` (every infinite chain of T1–T4 return steps is eventually T2-only), `CA.no_caseA`\n"
       "(case (a') is impossible from a flag-0 term), `CA.depth_to_infinity` (a jump-free infinite leftmost walk from a flag-0\n"
       "term has right-spine depth tending to infinity), `SC.EM_deep` (every jump-free infinite leftmost walk whose depth\n"
       "tends to infinity is eventually monotone; no flag hypothesis), `SC.NT_holds` and the reading lemma `DP.gamma_walk`.\n"
       "Hence **`SC.finite_half_of_J`: an infinite leftmost walk from an L36-flag-0 term makes infinitely many jumps** (nodes\n"
       "S p τ). So Conjecture J (every infinite leftmost walk makes only finitely many jumps) implies the leftmost-path finite\n"
       "half for every flag-0 class, and with Proposition Q″ L36 would decide leftmost-path finiteness of S-terms. J is OPEN\n"
       "(EXPERIMENTALLY SUPPORTED: no late jump among all 58,786 terms with 12 leaves and 240,000 random compositions; no\n"
       "periodic leftmost walk found).")
edit("PROOF.md", old, new)

old = "| R100 | **Every evaluation order re-times the head run"
new = ("| R103 | **Leftmost-path finite half reduced to Conjecture J (EM agent; lean/AgentEMA.lean):** cases (a') and (b) of "
       "Conjecture EM are closed in Lean — a jump-free infinite leftmost walk from a flag-0 term has unbounded depth "
       "(`CA.depth_to_infinity`) and every jump-free deep walk is eventually monotone (`SC.EM_deep`) — so an infinite leftmost "
       "walk from a flag-0 term must make infinitely many jumps (`SC.finite_half_of_J`). Conjecture J (finitely many jumps on "
       "every infinite leftmost walk) would make leftmost-path finiteness of S-terms decidable via L36 | MACHINE-CHECKED "
       "(reduction) / J CONJECTURAL (experimentally supported) |\n" + old)
edit("STATUS.md", old, new)

old = "| Leftmost/rightmost-path finite halves reduced to Conjecture EM | `AgentFiniteHalfGen.lean` |"
new = ("| Leftmost-path finite half reduced to Conjecture J | `AgentEMA.lean` | an infinite leftmost walk from a term in a "
       "flag-0 class of the 36-class model must make infinitely many 'jumps' (nodes S p τ); so if every infinite leftmost walk "
       "makes only finitely many jumps (Conjecture J, unrefuted in all tests), leftmost-path finiteness of S-terms is decidable |\n" + old)
edit("RESULTS.md", old, new)
old = ("   leftmost half the problem is now reduced in Lean to one conjecture, EM (every infinite leftmost walk is eventually\n"
       "   monotone; R98), and the same holds for the rightmost path under EM_R.")
new = ("   leftmost half the problem is now reduced in Lean to one conjecture, J (every infinite leftmost walk makes only\n"
       "   finitely many jumps; R103), after EM's other cases were closed; the rightmost path is reduced to EM_R (R98).")
edit("RESULTS.md", old, new)
old = ("* **What a full disproof still needs:** decidability of Böhm-tree properties (open even for productivity, BEKW Question 5,\n"
       "  and leftmost-path finiteness), regularity of all head runs (R″_PUP), and a definitional argument about Wolfram's\n"
       "  \"non-universal decoder\" (see \"Open\" below).")
new = ("* **Closest to a new decidability theorem:** leftmost-path finiteness of S-terms. Everything is machine-checked except\n"
       "  one conjecture (J: an infinite leftmost walk makes only finitely many 'jumps'); with J, the 36-class model decides it.\n"
       "* **What a full disproof still needs:** decidability of Böhm-tree properties (open even for productivity, BEKW Question 5,\n"
       "  and, pending J, leftmost-path finiteness), regularity of all head runs (R″_PUP), and a definitional argument about\n"
       "  Wolfram's \"non-universal decoder\" (see \"Open\" below).")
edit("RESULTS.md", old, new)

old = "* **Parallel-evaluation agent (11:28 EDT):**"
new = ("* **EM agent (12:27 EDT):** two of the three open cases of Conjecture EM are closed in Lean, so the leftmost-path finite\n"
       "  half now rests on one conjecture, J (every infinite leftmost walk makes only finitely many jumps). With J, the 36-class\n"
       "  model would decide leftmost-path finiteness of S-terms — a decidable Böhm-tree property beyond head normalisation.\n" + old)
edit("PRIZE_ASSESSMENT.md", old, new)

old = "## The parallel-evaluation agent's result (11:28 EDT)"
new = ("## The EM agent's result (12:27 EDT)\n"
       "Cases (a') and (b) of Conjecture EM closed and machine-checked (lean/AgentEMA.lean, 8,480 lines, 65 theorems):\n"
       "`CA.depth_to_infinity`, `SC.EM_deep`, `SC.finite_half_of_J`. The leftmost-path finite half now reduces to Conjecture\n"
       "J (every infinite leftmost walk makes only finitely many jumps), which is open but unrefuted in every test.\n\n" + old)
edit("SESSION_SUMMARY_2026-10-27.md", old, new)
print("recorded")
