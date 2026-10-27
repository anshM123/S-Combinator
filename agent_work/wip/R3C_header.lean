/-
  agent_work/lean/R3C.lean  (R3 agent, 2026-10-27).  Consolidated file: PA.lean lines 1-1574 (verbatim) + all R3-agent
  sections.  Guard-free replay by atom substitution (asub_run), two-hole barriers (nHB_stop), GCL (gcl).
  Structural theorems (runs from ANY list, no replay guard):  alpha_main (single wrapper, pattern alpha),
  pbt_main (pattern beta, c0 = S.a1), beta_main (c0 run on (w, y) + residual H1ok of c0), igen_main (earlier phase
  lays out args(V)).  Handler-only theorems: paf_main, pax_main, pamf_main, ln0_main.
  Counterexample to R3 as stated for all ordered data: r3_cx_ordered, r3_cx_phase2, r3_cx_next, r3_cx_phase3.
  Plain Lean 4 core.
-/
