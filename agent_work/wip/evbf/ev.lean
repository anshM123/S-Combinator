/-
  agent_work/lean/R3G.lean  (S1 agent, 2026-10-27).  = R3F.lean (verbatim, first 3,470 lines) + new sections.
  NEW (S1 agent):
    THEOREM S1 (`s1_core`): structural claim (S1) for runs with ONE occurrence of p - if a run from a rank-sorted
      start list with at most one p reaches a list whose third element contains x/y/r, every glue list
      a1 :: w :: y :: R0 with w = b0.c0 a P-term and a1 a P-term != c0 is preceded by args(c0) ++ w :: y :: B.
      Supporting: seg_run (rank-sorted segment invariant, = OTD in rank form), ab3_bound (Lemma AB in rank form),
      ic_step (Claim C), iw_step (X-sequence), ia_step (GOOD creations), ib_step, s1_inv, s1_base.
    THEOREM R3-SINGLE (`r3_single`): for an S-headed ordered (ordT) datum D free of x, y, r with at most one p, if
      phase 2 transfers the single-wrapper handler w.y (b0, c0 S-headed) and c0 satisfies H1ok, the next phase
      never makes a proper transfer.  Cases: alpha_main / closedglue_main / (s1_core + beta_main).
    `r3_single_example`: non-vacuity (all hypotheses discharged for the pattern-beta datum S(S(SS))S(S(Sp))).
    THEOREM PAXB (`paxb_main`, handler-only): if b0's two-hole run never calls its first hole, the next phase of
      w.y is safe (no phase-2 hypothesis).  THEOREM R3-SINGLE' (`r3_single2`): r3_single with the condition
      'H1ok(c0) OR b0 never calls its first hole'.
    LEMMA YT (`yt_chain`, `yt_main`): a P-pair [U, V] under closed code with Y-top Yt evolves by chain steps until
      [E_j, E_{j+1}, Yt | R] is reached, and opening E_j before the transfer forces j <= 3.
    THEOREM MW-ALPHA2 (`mw_alpha2`): two wrappers glued in nested pattern alpha - unless the earlier phase
      re-opens L2 = v2.y after the inner glue (case I-L2), the next phase never makes a proper transfer (both
      c-codes never call their holes -> NHALL, or the earlier phase lays out args(V) -> IGEN).
    THEOREM IL-ATOM (`il_atom`): any number of wrappers; if the innermost c-code is atom-headed (head not y) and the
      earlier phase re-opens the innermost level (lays out args(vn.y)), the next phase has no p'-front at all.
    THEOREM IL-NH (`il_nh`): any number of wrappers; if the innermost c-code never calls its holes (NHc) and
      the earlier phase re-opens the innermost level, the next phase has no p'-front at all (no bottom condition).
    THEOREM IL-GEN (`il_gen`): IL-NH with the condition 'NHc(cn) OR bn never calls its first hole'.
    R3-RC SINGLE (`r3_rc_single`): r3_single2 for every S-headed right comb over p with closed wrappers
      (frozen atoms allowed), ordT and the single occurrence of p derived from the comb shape.
    `il_atom_example`: non-vacuity of il_atom (two-wrapper handler of S(S(S(S(SS))S))(S(SS)p), checked by decide).
    `mw_alpha2_example`: non-vacuity of mw_alpha2 (nested alpha handler of SSS(S(SS(SS)(Sp))), checked by decide).
    THEOREM S1-LAMBDA (`s1_coreL`, with GoodL/IAL/IBL/ia_stepL/ib_stepL/s1_invL): s1_core with the bare y replaced by any
      fixed rank-2 term (S1 at the outer levels of multi-wrapper handlers).
    THEOREM R3-SINGLE-ALL (`r3_single_all`): every single-wrapper handler (b0, c0 arbitrary) of an ordered
      single-occurrence datum; the condition 'H1ok(c0) OR NK1(b0)' is needed only when b0, c0 are both S-headed.
  Plain Lean 4 core.
-/
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
/-
  agent_work/lean/PA.lean  (non-universality agent, 2026-10-27).  THEOREM PA (`pa_main`): a single-wrapper phase-2
  handler V = w.y whose wrapper w = b0.c0 was glued onto y in pattern alpha (step [c0, w, y] ++ R0) never leads to a
  proper transfer in the next phase, provided the phase-2 continuation from the glue (top part args c0 ++ [y, w.y])
  reaches its TRANSFER under the replay guards.  Proof: barrier phase (two barriers, c0'-prefixed and p'-headed
  elements, keep y, x.y, r untouched; a p'-front there has a y-free element or the bare y at position 3), then at
  the first c0'-prefixed front the replay rho = (y -> e1, w.y -> e2, p -> c) of phase 2's continuation, which ends
  in a c-headed front (re-execution).  Built on REPLAY.lean (copied verbatim above Part 1).  Plain Lean 4 core.
  Also THEOREM PB (`pb_main`, pattern beta with c0 = S.a1: glue step [a1, w, y]), via the reusable `post_replay`
  (phase 2 continuation from args g ++ [y, w.y] replayed after the first c0'-prefixed front) and `pa_core`; and
  THEOREM PAM (`pam_main`): the same for MULTI-WRAPPER handlers at the innermost level (guarded phase until the
  innermost level vn[p:=c].p' is opened, then the generalised core `pa_core_g` from args(b0') ++ [c0', p'] ++ B);
  `reexec_replays_transfer` (the re-executed frozen value receives the replayed arguments) and
  `replayed_handler_trivial` / `trivH_next` (the replayed handler cannot start a further Church iteration).
-/

inductive T where
  | S : T
  | var : Nat → T
  | app : T → T → T
deriving DecidableEq, Repr

namespace T

def args : T → List T
  | S => []
  | var _ => []
  | app f x => args f ++ [x]

def head : T → T
  | S => S
  | var n => var n
  | app f _ => head f

def size : T → Nat
  | S => 1
  | var _ => 1
  | app f x => size f + size x + 1

end T

open T

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

def exBD : T := app (app (app S (app S (app S S))) (app S S)) (app (app S (app S (app S S))) (app S (app S (var 0))))

def firstP : Nat → Nat → List T → Option (Nat × List T)
  | 0, _, _ => none
  | fuel + 1, k, L => match L with
    | a :: _ => if head a = var 0 then some (k, L) else
        match step L with
        | some L' => firstP fuel (k + 1) L'
        | none => none
    | [] => none

#eval firstP 300 0 [exBD, var 1, var 2, var 3]
