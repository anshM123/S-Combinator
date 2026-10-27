"""Record the parallel-evaluation universality agent's final results (main agent, 2026-10-27, 11:35 EDT).
Run once from code/: python record_parallel_agent.py"""
import sys, os

root = ".."


def edit(fn, old, new):
    p = root + "/" + fn
    s = open(p, encoding="utf-8").read()
    if old not in s:
        sys.exit("anchor not found in %s: %r" % (fn, old[:80]))
    s = s.replace(old, new, 1)
    open(p, "w", encoding="utf-8").write(s)


for f in ["lean/AgentParTime.lean", "lean/AgentLemma10Any.lean"]:
    if not os.path.exists(root + "/" + f):
        sys.exit("missing " + f)

old = ' ("E108 descents: one-redex evolutions with descents into arguments, 9 leaves (two descend once, one for ever)",'
new = (' ("Lean 4 (parallel agent): Theorems PT and PT-all, transfer principle, Lemma PJ, BC-par (every order re-times the head run)",\n'
       '  ["lean_check.py", "../lean/AgentParTime.lean"], [r"LEAN OK: no errors, no sorry", r"theoremPT_all: propext, Quot.sound", r"transfer_principle_replaceAll: propext, Classical.choice, Quot.sound", r"lemmaPJ: propext, Classical.choice, Quot.sound"], 1500),\n'
       ' ("Lean 4 (parallel agent): Lemma 10 in every evaluation order",\n'
       '  ["lean_check.py", "../lean/AgentLemma10Any.lean"], [r"LEAN OK: no errors, no sorry", r"lemma10_any: propext, Classical.choice, Quot.sound"], 900),\n' + old)
edit("code/verify_all.py", old, new)

anchor = "## Lazy parallel evaluation (Lemma LZ) and an exact parallel loop (Theorem PL) (main agent, 2026-10-26)"
new = ("## Every evaluation order re-times the head run (parallel-evaluation agent, 2026-10-27; re-verified by the main agent)\n"
       "MACHINE-CHECKED (lean/AgentParTime.lean, lean/AgentLemma10Any.lean; Lean 4.35 core, no sorry, standard axioms):\n"
       "* **Theorem PT** (`theoremPT`, `parallel_time_change`, `pass_head_step`): after n ReplaceAll passes the term has the head\n"
       "  and spine length of the k-th head reduct w (unique), its spine arguments are position-wise reducts of w's, and k >= n\n"
       "  while no earlier pass reached a head normal form.\n"
       "* **PT-all and the transfer principle** (`factorization`, `theoremPT_all`, `factorization_mono`, `transfer_principle`,\n"
       "  `transfer_monotone`): every reduct of t, in ANY order and on any path of the multiway system, is an internal reduct\n"
       "  of a head-run state of t, with the same head, arity and data per spine position, reached monotonically. So every\n"
       "  property of (head, data per spine position) that holds along the head run holds in every order. This extends\n"
       "  Proposition CF from head-normal-form events to whole (infinite) head runs.\n"
       "* **Lemma PJ** (`lemmaPJ`, `passN_ext`): waiting elements age on their own; opening one is a max-plus join with its own\n"
       "  clock (its hnf reaches the front 1 + max(0, h - w) passes after opening; leftmost-outermost pays the sum).\n"
       "  **Corollary PT-V** (`corollaryPT_data`): data placement is order-independent. **Corollary PT-F**\n"
       "  (`corollaryPT_fast`): ReplaceAll reaches a head normal form no later than leftmost-outermost. **Theorem BC-par**\n"
       "  (`replaceAll_reveals`, `passN_HN_exact`): ReplaceAll reveals every Böhm-tree node.\n"
       "* **Lemma 10 in every order** (`lemma10_any`, `lemma10_replaceAll`): no junk-free rotation for any reduct.\n"
       "* Hand (from the above): the transfer table — Lemma 8, Corollary 8(ii), Lemma 9(a), Theorem J at the hnf, Lemma 10,\n"
       "  Theorem U* and the Böhm-tree-level barriers hold in every order; the cost lemmas (11, 12, Theorem O) transfer only\n"
       "  to re-timed head-step counts. The clock channel acts only as a time shift (a clock opened at age w delivers the\n"
       "  spine of P^max(w,h)(W)); normalising clocks saturate, but age-injective clocks exist (5 of the 2,056 terms with at\n"
       "  most 9 leaves, horizon 40 passes).\n"
       "* **Theorem RR (race reduction) — PROVED as a conditional reduction (MRDP cited):** if a computable family of terms\n"
       "  creates, for every parameter tuple y, a recognisable race node S A_y B_y whose two parts have ReplaceAll hnf times\n"
       "  c + P(y) and c + Q(y) for prescribed polynomials, then S is universal under ReplaceAll with a linear-time\n"
       "  tree-pattern detector (and configuration-level R″_PUP fails for ReplaceAll). OPEN: such race material for two or\n"
       "  more parameters; probes found none (agent_work_P/numeral_products.py, junk_processes.py).\n"
       "* **Reading.** Choosing ReplaceAll only re-times the leftmost-outermost skeleton and changes syntax inside list\n"
       "  elements; control-level universality is the same question in every order. A ReplaceAll emulation would have to\n"
       "  work through the detector (timing races), which Theorem RR makes precise.\n\n")
edit("PROOF.md", anchor, new + anchor)
edit("PROOF.md", "| configuration R″_PUP, parallel and other orders | open; 86/150 parallel runs certified per term (Theorem LP-par) |",
     "| configuration R″_PUP, parallel and other orders | open, but reduced (2026-10-27, parallel agent): every order re-times the head run (Theorem PT-all, machine-checked), so for ReplaceAll it splits into the head-run skeleton, the max-plus re-timing (Lemma PJ) and the autonomous runs of list elements; 86/150 parallel runs certified per term (Theorem LP-par) |")

old = "| R99 | **R3 for single-wrapper handlers, unconditional"
new = ("| R100 | **Every evaluation order re-times the head run (parallel agent; lean/AgentParTime.lean):** a ReplaceAll run is the "
       "head run, re-timed monotonically, with each list element replaced by a reduct (Theorem PT); the same for every order and "
       "every multiway path (PT-all, transfer principle); waiting elements age and opening is a max-plus join (Lemma PJ); data "
       "placement is order-independent; ReplaceAll reaches hnfs no later and reveals every Böhm-tree node | MACHINE-CHECKED |\n"
       "| R101 | **Lemma 10 in every evaluation order (lean/AgentLemma10Any.lean)**, and by the transfer principle Lemmas 8, 9(a), "
       "Theorem J, Theorem U* and the Böhm-tree barriers hold in every order (transfer table: hand step) | MACHINE-CHECKED / "
       "PROVED |\n"
       "| R102 | **Theorem RR (race reduction):** race nodes S A_y B_y with prescribed polynomial ReplaceAll hnf times for every "
       "parameter tuple would make S universal under ReplaceAll with a linear-time detector (MRDP); no such race material is "
       "known for two or more parameters | PROVED (conditional reduction) / hypothesis OPEN |\n" + old)
edit("STATUS.md", old, new)

old = "| Proposition CF, head normalisation theorem | `CF.lean`, `Standard.lean` |"
new = ("| Theorems PT, PT-all, transfer principle, Lemma PJ, BC-par | `AgentParTime.lean` | every evaluation order (ReplaceAll, any "
       "order, any multiway path) is the head run re-timed, with list elements replaced by reducts: data placement and the "
       "head-run barriers carry over to every order; under ReplaceAll waiting elements age and opening is a max-plus join |\n"
       "| Lemma 10 in every order | `AgentLemma10Any.lean` | no junk-free rotation for any reduct, in any order |\n" + old)
edit("RESULTS.md", old, new)
old = ("**For \"S is universal\":** an explicit emulation. Every design pattern tried so far is blocked by a proved barrier or\n"
       "failed in bounded searches.")
new = ("**For \"S is universal\":** an explicit emulation. Every design pattern tried so far is blocked by a proved barrier or\n"
       "failed in bounded searches. The sharpest remaining lead is Theorem RR: under ReplaceAll, race nodes with prescribed\n"
       "polynomial timing for every parameter tuple would give universality with a linear-time detector; no such races are\n"
       "known.")
edit("RESULTS.md", old, new)

old = "* **Final agent results (10:12 EDT):**"
new = ("* **Parallel-evaluation agent (11:28 EDT):** no universal construction under ReplaceAll. Machine-checked: every\n"
       "  evaluation order is the head run re-timed (Theorems PT, PT-all), so the head-run barriers transfer to every order\n"
       "  and the choice of order changes only timing and syntax inside elements. The remaining universality lead is precise:\n"
       "  Theorem RR — timing races with prescribed polynomial durations would give universality under ReplaceAll with a\n"
       "  linear-time detector; no such races are known.\n" + old)
edit("PRIZE_ASSESSMENT.md", old, new)

old = "## Experiments and negative results this session"
new = ("## The parallel-evaluation agent's result (11:28 EDT)\n"
       "No universal construction under ReplaceAll. Machine-checked (lean/AgentParTime.lean, AgentLemma10Any.lean): a\n"
       "ReplaceAll run, and every other evaluation order, is the head run re-timed with list elements replaced by reducts\n"
       "(Theorems PT, PT-all, transfer principle); waiting elements age and opening is a max-plus join (Lemma PJ); Lemma 10\n"
       "holds in every order. Proved as a conditional reduction: Theorem RR (timing races with prescribed polynomial durations\n"
       "would make S universal under ReplaceAll). Open: such races for two or more parameters.\n\n" + old)
edit("SESSION_SUMMARY_2026-10-27.md", old, new)
print("recorded")
