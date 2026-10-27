/-
  agent_work/lean/R3A.lean  (R3 agent, 2026-10-27).  = PA.lean (verbatim, lines 1-1574) + new sections at the end:
  GUARD-FREE replay by atom substitution (asub_step, asub_run), two-hole barriers (nHB_run, nHB_stop),
  THEOREM PAF (paf_main: single wrapper w = b0.c0; if the abstract run of args(c0) ++ [h1, h2] never calls h1 / h2,
  the next phase never makes a proper transfer - hypothesis on the handler only), GCL (gcl: two images of one
  abstract run), THEOREM IGEN (igen_main: if the earlier phase lays out args(V) before its transfer, the next phase
  has no p'-front at all), THEOREM ALPHA (alpha_main: single-wrapper pattern alpha with NO replay hypothesis).
  Plain Lean 4 core.
-/
