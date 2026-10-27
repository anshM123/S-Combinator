"""Prepend a 'resume here' section to NEXT_STEPS.md (main agent, 2026-10-27 evening). Run once from code/."""
fn = "../NEXT_STEPS.md"
s = open(fn, encoding="utf-8").read()
head = "# NEXT STEPS (resume here)\n"
assert s.startswith(head)
new = head + """
## Resume here — state at the end of 2026-10-27 (main agent, 17:45 EDT)
The challenge is NOT solved. Every result below is labelled in STATUS.md (R1–R105) and summarised in RESULTS.md; all
116 checks of code/verify_all.py passed at 17:41. The weekly usage limit stopped the last two agents at about 12:46.
Open lines, closest first:
1. **Conjecture J** (agent_work_J/, stopped early): every infinite leftmost Böhm-tree walk makes only finitely many jumps
   (nodes S p τ). With it, `SC.finite_half_of_J` (lean/AgentEMA.lean) + Proposition Q″ make leftmost-path finiteness
   decidable via L36. Known: jump sources over non-tower stacks (DP.jump_child; EM LOG 11:54, 12:10: discard jumps,
   delayed discards, S letters, K = 3 with c0 = S); jumps into towers end the path; no repeated nodes and no periodic
   walks (lean/NoRepeat.lean, given Waldmann's no-spiral theorem). Next: show 'stack' jumps end the walk in the deep
   regime and 'code' jumps recur only finitely often.
2. **Theorem RR's hypothesis** (agent_work_RR/, stopped early): one closed term whose ReplaceAll run creates, for every
   parameter tuple, race nodes with prescribed polynomial durations. Available: Theorem B2 (exact bilinear clock,
   lean/AgentBilinear.lean) and a certified race FAMILY (one term per triple). Missing: the generator.
3. **Multi-wrapper R3** (agent_work/, R99): R3 is unconditional for single-wrapper handlers; multi-wrapper handlers are
   machine-checked in classes (FH, MWA2, IL-*, IGEN, NHALL, replay_pf2). Then D3 ('re-execution is call-like').
4. **EM_R** for the rightmost path (lean/AgentFiniteHalfGen.lean, R98) and the C6 completeness half (BEKW Question 5).
5. **Theorem O's residual walk** (hand proof; its potential half is machine-checked in lean/NStar.lean).
Agents: brief new agents per memory 'subagent-small-steps'; pace them (the weekly limit ran out today with 2–3 Opus
agents running for about 11 hours); keep code/autosave.sh running and push often.

"""
s = new + s[len(head):]
open(fn, "w", encoding="utf-8").write(s)
print("NEXT_STEPS updated")
