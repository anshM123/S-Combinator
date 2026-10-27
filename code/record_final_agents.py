"""Record the final results of the S1 agent and the universality agent (main agent, 2026-10-27, 10:20 EDT).
Run once from code/: python record_final_agents.py"""
import sys

root = ".."


def edit(fn, old, new):
    p = root + "/" + fn
    s = open(p, encoding="utf-8").read()
    if old not in s:
        sys.exit("anchor not found in %s: %r" % (fn, old[:80]))
    s = s.replace(old, new, 1)
    open(p, "w", encoding="utf-8").write(s)


# verify_all entries
old = ' ("E108 descents: one-redex evolutions with descents into arguments, 9 leaves (two descend once, one for ever)",'
new = (' ("Lean 4 (S1 agent): R3 for every single-wrapper handler of ordered data with at most one predecessor (no conditions)",\n'
       '  ["lean_check.py", "../lean/AgentR3G.lean"], [r"LEAN OK: no errors, no sorry", r"r3_single_unc: propext, Classical.choice, Quot.sound", r"r3_rc_unc: propext, Classical.choice, Quot.sound", r"s1_core: propext, Classical.choice, Quot.sound"], 2400),\n'
       ' ("Lean 4 (universality agent): leftmost/rightmost-path finite halves reduced to Conjectures EM / EM_R",\n'
       '  ["lean_check.py", "../lean/AgentFiniteHalfGen.lean"], [r"LEAN OK: no errors, no sorry", r"EM.finite_half_of_EM: propext, Classical.choice, Quot.sound", r"FM.finite_half_monotone_all: propext, Classical.choice, Quot.sound", r"FG.finite_half_general_families: propext, Classical.choice, Quot.sound"], 2400),\n' + old)
edit("code/verify_all.py", old, new)

# PROOF.md: chain bound section
old = "* **Chain bound** (a Church chain makes at most 2 proper transfers): not refuted — after the first transfer every datum"
new = ("* **R3 for single-wrapper handlers — MACHINE-CHECKED without conditions** (S1 agent, 2026-10-27; lean/AgentR3G.lean):\n"
       "  `r3_single_unc` / `r3_single_all_unc` — for an ordered S-headed datum D free of x, y, r with at most one occurrence of\n"
       "  p, if the run of [D, x, y, r] reaches a p-headed front with a single-wrapper handler (b0·c0)·y at position 3 (b0·c0\n"
       "  free of x, y, r), the next phase of (b0·c0)·y is safe: every p-headed front has a y-free element or the bare y at\n"
       "  position 3. `r3_rc_unc` — the same for every right comb over p with closed wrappers. Route: Theorem S1 (`s1_core`:\n"
       "  in pattern beta c0 ran on (w, y) before the glue), Lemma YT, Lemma AB, the barrier order (`beta_class`,\n"
       "  `beta_front`) and BF-NK1 (`bform_nk1g`, `paxb_main`); non-vacuity examples `r3_single_unc_example`,\n"
       "  `r3_single_example`. Multi-wrapper handlers: machine-checked in classes (FH, MWA2, IL-ATOM/IL-NH/IL-GEN, IGEN,\n"
       "  NHALL, and the replay criteria `replay_pf`, `replay_pf2` that ignore the outer wrappers); OPEN in general.\n"
       "  COMPUTATIONALLY CERTIFIED: every proper transfer of S-headed ordered one-occurrence data up to 13 leaves (28,316) and\n"
       "  of right combs up to 13 leaves (10,161) lies in a machine-checked class; of 53,459 random transfers (4-22 leaves) one\n"
       "  is uncovered (three wrappers, bare-S middle wrapper).\n" + old)
edit("PROOF.md", old, new)
old = ("  is a right comb over p with one occurrence of p (step (1)), so it needs only R3-RC. MACHINE-CHECKED for every chain\n"
       "  whose second transfer falls in one of the classes above;")
new = ("  is a right comb over p with one occurrence of p (step (1)), so it needs only R3-RC. MACHINE-CHECKED (each step; the\n"
       "  assembly is by hand) for every chain whose second transfer has a single-wrapper handler (unconditionally, by\n"
       "  `r3_rc_unc`) or an FH handler, and for every chain whose second transfer falls in one of the classes above;")
edit("PROOF.md", old, new)

# PROOF.md: leftmost finite half section
old = ("OPEN: Conjecture SF (every infinite leftmost walk eventually uses only tail calls and canonical Omega steps) and Omega\n"
       "steps with a second component other than S(SS) (none among 954 Omega steps in known infinite walks).")
new = ("Final (universality agent, 10:12; lean/AgentFiniteHalfGen.lean, 6,146 lines, 31 theorems, re-compiled by the main agent):\n"
       "`FG.finite_half_Omega_general`, `FG.finite_half_general_families` exclude Omega and reload families with ANY second\n"
       "component from flag-0 classes (`RG.finite_half_right_general` for R19); `FM.fib_step` (Lemma Fib: over a non-tower\n"
       "bottom every computed step has H(Q) = S (tw K) c0 and its leftmost child is a Fibonacci word); `SA.no_TT_chain` (no\n"
       "infinite tower-headed chain); `SA3.fuel_is_S`, `SA3.scenarioA_depth_one`, `SA4.return_types_S`, `SA4.caseA_needs_T34`;\n"
       "and the REDUCTION `EM.finite_half_of_EM` / `FM.finite_half_monotone_all`: no infinite leftmost walk from an\n"
       "L36-flag-0 term is eventually monotone (from some node on, every node has >= 3 arguments and no child equals the\n"
       "node's last argument). So Conjecture EM (every infinite leftmost walk is eventually monotone) implies the\n"
       "leftmost-path finite half for every flag-0 class; `EM.finite_half_right_of_EMR` / `RM.finite_half_right_monotone_all`\n"
       "do the same for R19 under Conjecture EM_R. OPEN: EM itself; it can fail only through (a') a jump-free walk returning\n"
       "infinitely often to nodes q·S with infinitely many T3/T4 steps, (b) unbounded depth with infinitely many pops or\n"
       "returns, or (c) infinitely many jumps. EXPERIMENTALLY SUPPORTED: after burn-in all 37,657,000 steps of 13,151 long\n"
       "flag-1 walks are pushes; no case (a') among 780,000 depth-1 returns.")
edit("PROOF.md", old, new)

# STATUS.md
old = "| R97 | **Leftmost-path finite half: the known infinite mechanisms are excluded"
new = ("| R99 | **R3 for single-wrapper handlers, unconditional (S1 agent; lean/AgentR3G.lean, re-compiled by the main agent):** "
       "for every ordered datum with at most one occurrence of the predecessor, a proper transfer by a single-wrapper handler "
       "is never followed by a proper transfer (`r3_single_unc`, `r3_rc_unc`; via Theorem S1, Lemma YT, the barrier order). "
       "Hence the chain bound (<= 2 proper transfers) holds for every chain whose second transfer is single-wrapper or FH; "
       "multi-wrapper R3 is machine-checked in classes and open in general (every observed second transfer is single-wrapper "
       "or FH) | MACHINE-CHECKED (steps; assembly by hand) / multi-wrapper OPEN |\n"
       "| R98 | **Leftmost-path finite half reduced to one conjecture (universality agent; lean/AgentFiniteHalfGen.lean):** no "
       "infinite leftmost walk from an L36-flag-0 term is eventually monotone (`EM.finite_half_of_EM`), and Omega/reload "
       "families with any second component are excluded (`FG.finite_half_general_families`); so Conjecture EM (every infinite "
       "leftmost walk is eventually monotone) implies the finite half for all flag-0 classes, including (14,28), (14,26). Same "
       "for the rightmost path (R19) under EM_R | MACHINE-CHECKED (reduction) / EM CONJECTURAL (experimentally supported) |\n" + old)
edit("STATUS.md", old, new)
edit("STATUS.md", "and non-canonical Omega steps (never observed) | MACHINE-CHECKED (reduction) / finite half OPEN |",
     "and non-canonical Omega steps (now covered, R98) | MACHINE-CHECKED (reduction) / finite half OPEN (see R98) |")

# RESULTS.md
old = "| Leftmost-path finite half: known mechanisms excluded | `AgentFiniteHalf.lean` |"
new = ("| Leftmost/rightmost-path finite halves reduced to Conjecture EM | `AgentFiniteHalfGen.lean` | no infinite leftmost "
       "walk from a flag-0 term is eventually monotone, so the finite half of the leftmost-path model (and of the "
       "rightmost-path model, under EM_R) follows from one conjecture: every infinite leftmost walk is eventually monotone "
       "(finitely many pops, jumps and returns) |\n" + old)
edit("RESULTS.md", old, new)
old = "| Conjecture R3 refuted; guard-free R3 theorems | `AgentR3F.lean` |"
new = ("| R3 for single-wrapper handlers (unconditional) | `AgentR3G.lean` | for ordered data with at most one occurrence of "
       "the predecessor, a single-wrapper transfer is never followed by a proper transfer; so the chain bound (at most 2 "
       "proper transfers) holds whenever the second transfer is single-wrapper or FH, which covers every chain ever "
       "observed; multi-wrapper handlers are machine-checked in classes |\n" + old)
edit("RESULTS.md", old, new)
old = ("   leftmost half the two known infinite mechanisms are now excluded from flag-0 classes (machine-checked, R97);\n"
       "   what is left is Conjecture SF.")
new = ("   leftmost half the problem is now reduced in Lean to one conjecture, EM (every infinite leftmost walk is eventually\n"
       "   monotone; R98), and the same holds for the rightmost path under EM_R.")
edit("RESULTS.md", old, new)
old = ("   non-universality agents' phase programme (agent_work/) bounds Church chains by two transfers in the covered cases;\n"
       "   still open: R3 for one occurrence of the predecessor in general (R3 for several occurrences is refuted), \"re-execution\n"
       "   is call-like\" (D3), and the phase decomposition as a theorem about all head runs.")
new = ("   non-universality agents' phase programme (agent_work/) bounds Church chains by two transfers whenever the second\n"
       "   transfer is single-wrapper or FH (all observed chains); still open: multi-wrapper R3 (R3 for several occurrences of\n"
       "   the predecessor is refuted), \"re-execution is call-like\" (D3), and the phase decomposition as a theorem about all\n"
       "   head runs.")
edit("RESULTS.md", old, new)
print("recorded")
