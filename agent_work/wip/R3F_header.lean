/-
  agent_work/lean/R3F.lean  (R3 agent, 2026-10-27).  FINAL consolidated file: PA.lean lines 1-1574 (verbatim) + all
  R3-agent sections (R3A-R3E.lean are earlier checkpoints whose theorems are all contained here).
  Guard-free replay by atom substitution (asub_run), two-hole barriers (nHB_stop), GCL (gcl).
  Structural theorems (the earlier phase is ANY run from ANY list that later reaches a p-front; no replay guard):
    igen_main (earlier phase lays out args(V): the next phase has no p'-front at all),
    alpha_main (single wrapper, glue [c0, w, y]), closedglue_main (glue [a1, w, y] with a1 free of p),
    pbt_main (pattern beta, front (S.a1).w over y with c0 = S.a1), beta_main (c0 run on (w, y) + H1ok of c0).
  pah_main (single wrapper whose c-code is atom-headed).
  Handler-only theorems: paf_main, pax_main, pamf_main, ln0_main, nhall_main (any number of wrappers).
  Counterexample to R3 as stated for all ordered data: r3_cx_ordered, r3_cx_phase2, r3_cx_next, r3_cx_phase3.
  Plain Lean 4 core.
-/
