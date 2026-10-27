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

/-- replace w by var q and the live atom var 0 by var c -/
def th (w : T) (q c : Nat) : T → T
  | S => if S = w then var q else S
  | var n => if var n = w then var q else (if n = 0 then var c else var n)
  | app f x => if app f x = w then var q else app (th w q c f) (th w q c x)

/-- substitution of the live atom only: p := c -/
def sb (c : Nat) : T → T
  | S => S
  | var n => if n = 0 then var c else var n
  | app f x => app (sb c f) (sb c x)

/-- some left-spine prefix equals w -/
def wpre (w : T) : T → Prop
  | S => S = w
  | var n => var n = w
  | app f x => app f x = w ∨ wpre w f

theorem th_args (w : T) (q c : Nat) : ∀ a : T, ¬ wpre w a → args (th w q c a) = (args a).map (th w q c)
  | S, h => by
    have : S ≠ w := fun e => h e
    simp [th, this, args]
  | var n, h => by
    have : var n ≠ w := fun e => h e
    simp only [th, this, ite_false]
    split <;> simp [args]
  | app f x, h => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [th, h1, ite_false, args]
    rw [th_args w q c f h2]
    simp

theorem th_headS (w : T) (q c : Nat) : ∀ a : T, ¬ wpre w a → head a = S → head (th w q c a) = S
  | S, h, _ => by
    have : S ≠ w := fun e => h e
    simp [th, this, head]
  | var n, _, hS => by simp [head] at hS
  | app f x, h, hS => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [th, h1, ite_false, head]
    exact th_headS w q c f h2 (by simpa [head] using hS)

theorem th_head0 (w : T) (q c : Nat) : ∀ a : T, ¬ wpre w a → head a = var 0 → head (th w q c a) = var c
  | S, _, hS => by simp [head] at hS
  | var n, h, hS => by
    have : var n ≠ w := fun e => h e
    simp [head] at hS; subst hS
    simp [th, this, head]
  | app f x, h, hS => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [th, h1, ite_false, head]
    exact th_head0 w q c f h2 (by simpa [head] using hS)

/-- **Replay lemma (one step).** -/
theorem replay_step (w : T) (q c : Nat) (a b d : T) (R : List T) (hS : head a = S) (hG : ¬ wpre w a)
    (hne : app b d ≠ w) :
    step ((a :: b :: d :: R).map (th w q c)) = some ((args a ++ d :: app b d :: R).map (th w q c)) := by
  simp only [List.map_cons, step, th_headS w q c a hG hS, ite_true, th_args w q c a hG, List.map_append]
  simp [th, hne]

/-- the guard: front not w-prefixed and the glued node is not w -/
def G (w : T) : List T → Prop
  | a :: b :: d :: _ => ¬ wpre w a ∧ app b d ≠ w
  | _ => True

def runOK (w : T) : Nat → List T → Prop
  | 0, _ => True
  | k + 1, L => G w L ∧ (match step L with
    | some L' => runOK w k L'
    | none => True)

/-- **Replay lemma (runs).** -/
theorem replay_run (w : T) (q c : Nat) : ∀ (k : Nat) (L L' : List T), runOK w k L → run k L = some L' →
    run k (L.map (th w q c)) = some (L'.map (th w q c))
  | 0, L, L', _, h => by simp [run] at h; subst h; simp [run]
  | k + 1, L, L', hok, h => by
    match L, hok, h with
    | a :: b :: d :: R, hok, h =>
      obtain ⟨⟨hG, hne⟩, hrest⟩ := hok
      simp only [run] at h
      by_cases hS : head a = S
      · have hs : step (a :: b :: d :: R) = some (args a ++ d :: app b d :: R) := by simp [step, hS]
        rw [hs] at h hrest
        simp only at h hrest
        have ih := replay_run w q c k _ L' hrest h
        simp only [run]
        rw [replay_step w q c a b d R hS hG hne]
        exact ih
      · have hs : step (a :: b :: d :: R) = none := by simp [step, hS]
        rw [hs] at h; simp at h
    | [], _, h => simp [run, step] at h
    | [_], _, h => simp [run, step] at h
    | [_, _], _, h => simp [run, step] at h

theorem size_pos : ∀ t : T, 0 < size t
  | S => by simp [size]
  | var _ => by simp [size]
  | app f x => by simp [size]

theorem size_args : ∀ t : T, ∀ s ∈ args t, size s < size t
  | S, s, hs => by simp [args] at hs
  | var _, s, hs => by simp [args] at hs
  | app f x, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · have := size_args f s hs; simp [size]; omega
    · subst hs; have := size_pos f; simp [size]; omega

/-- on terms smaller than w, th is just the substitution p := c -/
theorem th_small (w : T) (q c : Nat) : ∀ t : T, size t < size w → th w q c t = sb c t
  | S, h => by
    have : S ≠ w := fun e => by subst e; simp at h
    simp [th, this, sb]
  | var n, h => by
    have : var n ≠ w := fun e => by subst e; simp at h
    simp [th, this, sb]
  | app f x, h => by
    have h1 : app f x ≠ w := fun e => by subst e; simp at h
    have hf : size f < size w := by simp [size] at h; omega
    have hx : size x < size w := by simp [size] at h; omega
    simp [th, h1, sb, th_small w q c f hf, th_small w q c x hx]

theorem sb_head : ∀ (c : Nat) (t : T), head t = S → head (sb c t) = S
  | _, S, _ => by simp [sb, head]
  | _, var _, h => by simp [head] at h
  | c, app f x, h => by simp only [sb, head]; exact sb_head c f (by simpa [head] using h)

theorem sb_args : ∀ (c : Nat) (t : T), head t = S → args (sb c t) = (args t).map (sb c)
  | _, S, _ => by simp [sb, args]
  | _, var _, h => by simp [head] at h
  | c, app f x, h => by
    simp only [sb, args]
    rw [sb_args c f (by simpa [head] using h)]
    simp

theorem wpre_head (w : T) (hw : head w = S) (n : Nat) : ∀ a : T, head a = var n → ¬ wpre w a
  | S, h, _ => by simp [head] at h
  | var m, h, hp => by simp [wpre] at hp; subst hp; simp [head] at hw
  | app f x, h, hp => by
    rcases hp with hp | hp
    · subst hp; rw [hw] at h; simp at h
    · exact wpre_head w hw n f (by simpa [head] using h) hp

theorem th_self (w : T) (q c : Nat) : th w q c w = var q := by
  cases w <;> simp [th]

/-- **Corollary (replay of a transfer as a re-execution).**  Let w be S-headed.  If the generic run of the list
    args w ++ [w, y, x.y, r] reaches, after k guarded steps, a list whose front is p-headed (a TRANSFER), then the
    generic run of [w[p:=c].q, x, y, r] (the next phase's datum, with q the new predecessor) reaches after k + 1
    steps the th-image of that list, whose front is c-headed (a REEXEC). -/
theorem replay_reexec (w : T) (q c : Nat) (hw : head w = S) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args w ++ [w, var 2, app (var 1) (var 2), var 3]) = some (a' :: rest))
    (hok : runOK w k (args w ++ [w, var 2, app (var 1) (var 2), var 3]))
    (hp : head a' = var 0) :
    run (k + 1) [app (sb c w) (var q), var 1, var 2, var 3] = some ((a' :: rest).map (th w q c)) ∧
      head (th w q c a') = var c := by
  have hna : ¬ wpre w a' := wpre_head w hw 0 a' hp
  refine ⟨?_, th_head0 w q c a' hna hp⟩
  have hw2 : var 2 ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have hw3 : var 3 ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have hw1 : var 1 ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have hwxy : app (var 1) (var 2) ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have himg : (args w ++ [w, var 2, app (var 1) (var 2), var 3]).map (th w q c) =
      args (sb c w) ++ [var q, var 2, app (var 1) (var 2), var 3] := by
    rw [sb_args c w hw]
    simp only [List.map_append, List.map_cons, List.map_nil]
    have hargs : (args w).map (th w q c) = (args w).map (sb c) := by
      apply List.map_congr_left
      intro s hs
      exact th_small w q c s (size_args w s hs)
    rw [hargs, th_self w q c]
    simp [th, hw1, hw2, hw3, hwxy]
  have hstep : step [app (sb c w) (var q), var 1, var 2, var 3] =
      some (args (sb c w) ++ [var q, var 2, app (var 1) (var 2), var 3]) := by
    simp [step, head, sb_head c w hw, args]
  have h1 := replay_run w q c k _ _ hok hrun
  rw [himg] at h1
  simp only [run]
  rw [hstep]
  exact h1


/-! ### prefix replay: the part of the list below the active top is never touched -/

theorem run_append : ∀ (k : Nat) (T1 T2 B : List T), run k T1 = some T2 → run k (T1 ++ B) = some (T2 ++ B)
  | 0, T1, T2, B, h => by simp [run] at h; subst h; simp [run]
  | k + 1, T1, T2, B, h => by
    match T1, h with
    | a :: b :: d :: R, h =>
      simp only [run] at h
      by_cases hS : head a = S
      · have hs : step (a :: b :: d :: R) = some (args a ++ d :: app b d :: R) := by simp [step, hS]
        rw [hs] at h; simp only at h
        have hs2 : step (a :: b :: d :: R ++ B) = some (args a ++ d :: app b d :: (R ++ B)) := by
          simp [step, hS]
        simp only [run]
        rw [hs2]
        have := run_append k _ T2 B h
        simpa using this
      · have hs : step (a :: b :: d :: R) = none := by simp [step, hS]
        rw [hs] at h; simp at h
    | [], h => simp [run, step] at h
    | [_], h => simp [run, step] at h
    | [_, _], h => simp [run, step] at h

/-- **Corollary (replay at the glue step).**  Let the innermost single wrapper be w = S.c0, glued onto y in a step
    [c0, w, y] ++ R0 (pattern alpha of the creation lemma).  If the run of the top part [c0, w, y] reaches after k
    guarded steps a p-headed front (by `run_append` this is exactly what the phase-2 run does above R0: the
    TRANSFER), then the phase-3 datum w[p:=c].q reaches after k + 1 steps the th-image of that top part above
    [x.y, r], with a c-headed front (REEXEC). -/
theorem replay_glue (c0 : T) (q c : Nat) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k [c0, app S c0, var 2] = some (a' :: rest))
    (hok : runOK (app S c0) k [c0, app S c0, var 2])
    (hp : head a' = var 0) :
    run (k + 1) [app (sb c (app S c0)) (var q), var 1, var 2, var 3] =
        some ((a' :: rest).map (th (app S c0) q c) ++ [app (var 1) (var 2), var 3]) ∧
      head (th (app S c0) q c a') = var c := by
  have hw : head (app S c0) = S := by simp [head]
  have hna : ¬ wpre (app S c0) a' := wpre_head (app S c0) hw 0 a' hp
  refine ⟨?_, th_head0 (app S c0) q c a' hna hp⟩
  have himg : [c0, app S c0, var 2].map (th (app S c0) q c) = [sb c c0, var q, var 2] := by
    have h1 : th (app S c0) q c c0 = sb c c0 := th_small _ q c c0 (by simp [size]; omega)
    have h2 : th (app S c0) q c (app S c0) = var q := th_self _ q c
    have h3 : th (app S c0) q c (var 2) = var 2 := by
      have : var 2 ≠ app S c0 := by intro h; cases h
      simp [th, this]
    simp [h1, h2, h3]
  have hstep : step [app (sb c (app S c0)) (var q), var 1, var 2, var 3] =
      some [sb c c0, var q, var 2, app (var 1) (var 2), var 3] := by
    simp [step, head, sb, args]
  have h1 := replay_run (app S c0) q c k _ _ hok hrun
  rw [himg] at h1
  have h2 := run_append k _ _ [app (var 1) (var 2), var 3] h1
  simp only [run]
  rw [hstep]
  simpa using h2


/-! ### general replay maps: replace w by a term tw and substitute atoms by terms -/

/-- rho w tw sg: replace (outermost) occurrences of w by tw, and every atom var n by sg n -/
def rho (w tw : T) (sg : Nat → T) : T → T
  | S => if S = w then tw else S
  | var n => if var n = w then tw else sg n
  | app f x => if app f x = w then tw else app (rho w tw sg f) (rho w tw sg x)

theorem rho_args (w tw : T) (sg : Nat → T) : ∀ a : T, ¬ wpre w a → head a = S →
    args (rho w tw sg a) = (args a).map (rho w tw sg)
  | S, h, _ => by
    have : S ≠ w := fun e => h e
    simp [rho, this, args]
  | var n, _, hS => by simp [head] at hS
  | app f x, h, hS => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [rho, h1, ite_false, args]
    rw [rho_args w tw sg f h2 (by simpa [head] using hS)]
    simp

theorem rho_headS (w tw : T) (sg : Nat → T) : ∀ a : T, ¬ wpre w a → head a = S → head (rho w tw sg a) = S
  | S, h, _ => by
    have : S ≠ w := fun e => h e
    simp [rho, this, head]
  | var n, _, hS => by simp [head] at hS
  | app f x, h, hS => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [rho, h1, ite_false, head]
    exact rho_headS w tw sg f h2 (by simpa [head] using hS)

/-- the head of the image of an atom-headed term is the head of the atom's image -/
theorem rho_headvar (w tw : T) (sg : Nat → T) (n : Nat) : ∀ a : T, ¬ wpre w a → head a = var n →
    head (rho w tw sg a) = head (sg n)
  | S, _, hS => by simp [head] at hS
  | var m, h, hS => by
    have : var m ≠ w := fun e => h e
    simp [head] at hS; subst hS
    simp [rho, this]
  | app f x, h, hS => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [rho, h1, ite_false, head]
    exact rho_headvar w tw sg n f h2 (by simpa [head] using hS)

theorem replay_step_gen (w tw : T) (sg : Nat → T) (a b d : T) (R : List T) (hS : head a = S)
    (hG : ¬ wpre w a) (hne : app b d ≠ w) :
    step ((a :: b :: d :: R).map (rho w tw sg)) = some ((args a ++ d :: app b d :: R).map (rho w tw sg)) := by
  simp only [List.map_cons, step, rho_headS w tw sg a hG hS, ite_true, rho_args w tw sg a hG hS,
    List.map_append]
  simp [rho, hne]

/-- **General replay lemma (runs).** -/
theorem replay_run_gen (w tw : T) (sg : Nat → T) : ∀ (k : Nat) (L L' : List T), runOK w k L →
    run k L = some L' → run k (L.map (rho w tw sg)) = some (L'.map (rho w tw sg))
  | 0, L, L', _, h => by simp [run] at h; subst h; simp [run]
  | k + 1, L, L', hok, h => by
    match L, hok, h with
    | a :: b :: d :: R, hok, h =>
      obtain ⟨⟨hG, hne⟩, hrest⟩ := hok
      simp only [run] at h
      by_cases hS : head a = S
      · have hs : step (a :: b :: d :: R) = some (args a ++ d :: app b d :: R) := by simp [step, hS]
        rw [hs] at h hrest
        simp only at h hrest
        have ih := replay_run_gen w tw sg k _ L' hrest h
        simp only [run]
        rw [replay_step_gen w tw sg a b d R hS hG hne]
        exact ih
      · have hs : step (a :: b :: d :: R) = none := by simp [step, hS]
        rw [hs] at h; simp at h
    | [], _, h => simp [run, step] at h
    | [_], _, h => simp [run, step] at h
    | [_, _], _, h => simp [run, step] at h

/-- on terms smaller than w, rho is the atom substitution -/
def asub (sg : Nat → T) : T → T
  | S => S
  | var n => sg n
  | app f x => app (asub sg f) (asub sg x)

theorem rho_small (w tw : T) (sg : Nat → T) : ∀ t : T, size t < size w → rho w tw sg t = asub sg t
  | S, h => by
    have : S ≠ w := fun e => by subst e; simp at h
    simp [rho, this, asub]
  | var n, h => by
    have : var n ≠ w := fun e => by subst e; simp at h
    simp [rho, this, asub]
  | app f x, h => by
    have h1 : app f x ≠ w := fun e => by subst e; simp at h
    have hf : size f < size w := by simp [size] at h; omega
    have hx : size x < size w := by simp [size] at h; omega
    simp [rho, h1, asub, rho_small w tw sg f hf, rho_small w tw sg x hx]

theorem rho_self (w tw : T) (sg : Nat → T) : rho w tw sg w = tw := by
  cases w <;> simp [rho]

/-- psi = (w -> y, y -> q.y, p -> c, other atoms fixed) -/
def psiS (q c : Nat) : Nat → T := fun n => if n = 0 then var c else if n = 2 then app (var q) (var 2) else var n

/-- **Corollary (pattern beta replay).**  Let the innermost single wrapper be w = S.(S.a1) with a1 free of y, glued
    in a step [a1, w, y] ++ R0.  If the run of the top part [a1, w, y] reaches after k guarded steps a p-headed front
    (the phase-2 TRANSFER), then the phase-3 datum w[p:=c].q, after two steps (opening and the sigma_C step
    [S.a1', q, y] -> [a1', y, q.y]) and k more, reaches the psi-image of that top part above [x.y, r], whose front is
    c-headed: REEXEC. -/
theorem replay_beta (a1 : T) (q c : Nat) (ha1 : asub (psiS q c) a1 = sb c a1) (k : Nat) (a' : T) (rest : List T)
    (hS1 : head a1 = S)
    (hrun : run k [a1, app S (app S a1), var 2] = some (a' :: rest))
    (hok : runOK (app S (app S a1)) k [a1, app S (app S a1), var 2])
    (hp : head a' = var 0) :
    run (k + 2) [app (sb c (app S (app S a1))) (var q), var 1, var 2, var 3] =
        some ((a' :: rest).map (rho (app S (app S a1)) (var 2) (psiS q c)) ++ [app (var 1) (var 2), var 3]) ∧
      head (rho (app S (app S a1)) (var 2) (psiS q c) a') = var c := by
  have hw : head (app S (app S a1)) = S := by simp [head]
  have hna : ¬ wpre (app S (app S a1)) a' := wpre_head _ hw 0 a' hp
  refine ⟨?_, ?_⟩
  · have himg : [a1, app S (app S a1), var 2].map (rho (app S (app S a1)) (var 2) (psiS q c)) =
        [sb c a1, var 2, app (var q) (var 2)] := by
      have h1 : rho (app S (app S a1)) (var 2) (psiS q c) a1 = sb c a1 := by
        rw [rho_small _ _ _ a1 (by simp [size]; omega)]; exact ha1
      have h2 := rho_self (app S (app S a1)) (var 2) (psiS q c)
      have h3 : rho (app S (app S a1)) (var 2) (psiS q c) (var 2) = app (var q) (var 2) := by
        have : var 2 ≠ app S (app S a1) := by intro h; cases h
        simp [rho, this, psiS]
      simp [h1, h2, h3]
    have hS1' : head (sb c a1) = S := sb_head c a1 hS1
    have hstep1 : step [app (sb c (app S (app S a1))) (var q), var 1, var 2, var 3] =
        some [app S (sb c a1), var q, var 2, app (var 1) (var 2), var 3] := by
      simp [step, head, sb, args]
    have hstep2 : step [app S (sb c a1), var q, var 2, app (var 1) (var 2), var 3] =
        some [sb c a1, var 2, app (var q) (var 2), app (var 1) (var 2), var 3] := by
      simp [step, head, args]
    have h1 := replay_run_gen (app S (app S a1)) (var 2) (psiS q c) k _ _ hok hrun
    rw [himg] at h1
    have h2 := run_append k _ _ [app (var 1) (var 2), var 3] h1
    simp only [run]
    rw [hstep1]
    simp only
    rw [hstep2]
    simpa using h2
  · rw [rho_headvar _ _ _ 0 a' hna hp]
    simp [psiS, head]


/-- occurrences of y = var 2 -/
def occ2 : T → Nat
  | S => 0
  | var n => if n = 2 then 1 else 0
  | app f x => occ2 f + occ2 x

theorem occ2_args : ∀ t : T, occ2 t = 0 → ∀ s ∈ args t, occ2 s = 0
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp only [occ2] at h
    simp [args] at hs
    rcases hs with hs | hs
    · exact occ2_args f (by omega) s hs
    · subst hs; omega

theorem wpre_headeq (w : T) : ∀ a : T, wpre w a → head a = head w
  | S, h => by simp [wpre] at h; rw [← h]
  | var _, h => by simp [wpre] at h; rw [← h]
  | app f x, h => by
    rcases h with h | h
    · rw [h]
    · simp only [head]; exact wpre_headeq w f h

/-- the map of the buffer-cycle replay: p -> c, y -> q, other atoms fixed -/
def sgq (q c : Nat) : Nat → T := fun n => if n = 0 then var c else if n = 2 then var q else var n

theorem asub_sgq_of_noy (q c : Nat) : ∀ t : T, occ2 t = 0 → asub (sgq q c) t = sb c t
  | S, _ => by simp [asub, sb]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, sgq]
    · have h2 : n ≠ 2 := by intro e; subst e; simp [occ2] at h
      simp [asub, sb, sgq, h0, h2]
  | app f x, h => by
    simp only [occ2] at h
    simp [asub, sb, asub_sgq_of_noy q c f (by omega), asub_sgq_of_noy q c x (by omega)]

/-- **Corollary (buffer-cycle replay, case (b)).**  Let w = b0.c0 be the innermost single wrapper, glued in the
    phase-2 step [c0, w, y] ++ R0, so that phase 2 continues from the top part args c0 ++ [y, w.y].  Suppose that
    in phase 3 the opened buffer c0'.q (c0' = c0[p:=c]) reaches the front, with s, t below it.  If the phase-2 top
    part reaches a p-headed front (the TRANSFER) after k guarded steps, then phase 3 reaches, k + 1 steps later, the
    image of that list under rho = (w.y -> t, y -> q, p -> c), whose front is c-headed: REEXEC. -/
theorem replay_cycle (b0 c0 s t : T) (B : List T) (q c : Nat) (hS : head c0 = S) (hy : occ2 c0 = 0)
    (hb0 : head b0 ≠ var 0)
    (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args c0 ++ [var 2, app (app b0 c0) (var 2)]) = some (a' :: rest))
    (hok : runOK (app (app b0 c0) (var 2)) k (args c0 ++ [var 2, app (app b0 c0) (var 2)]))
    (hp : head a' = var 0) :
    run (k + 1) (app (sb c c0) (var q) :: s :: t :: B) =
        some ((a' :: rest).map (rho (app (app b0 c0) (var 2)) t (sgq q c)) ++ (app s t :: B)) ∧
      head (rho (app (app b0 c0) (var 2)) t (sgq q c) a') = var c := by
  have hw : head (app (app b0 c0) (var 2)) = head b0 := by simp [head]
  refine ⟨?_, ?_⟩
  · have hc0S : head (sb c c0) = S := sb_head c c0 hS
    have hstep : step (app (sb c c0) (var q) :: s :: t :: B) =
        some (args (sb c c0) ++ [var q, t, app s t] ++ B) := by
      simp [step, head, hc0S, args]
    have himg : (args c0 ++ [var 2, app (app b0 c0) (var 2)]).map (rho (app (app b0 c0) (var 2)) t (sgq q c)) =
        args (sb c c0) ++ [var q, t] := by
      rw [sb_args c c0 hS]
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hargs : (args c0).map (rho (app (app b0 c0) (var 2)) t (sgq q c)) = (args c0).map (sb c) := by
        apply List.map_congr_left
        intro e he
        have hsz : size e < size (app (app b0 c0) (var 2)) := by
          have := size_args c0 e he
          simp [size]; omega
        rw [rho_small _ _ _ e hsz]
        exact asub_sgq_of_noy q c e (occ2_args c0 hy e he)
      rw [hargs, rho_self]
      have h2 : rho (app (app b0 c0) (var 2)) t (sgq q c) (var 2) = var q := by
        have : var 2 ≠ app (app b0 c0) (var 2) := by intro h; cases h
        simp [rho, this, sgq]
      simp [h2]
    have h1 := replay_run_gen (app (app b0 c0) (var 2)) t (sgq q c) k _ _ hok hrun
    rw [himg] at h1
    have h2 := run_append k _ _ (app s t :: B) h1
    simp only [run]
    rw [hstep]
    simpa using h2
  · have hna : ¬ wpre (app (app b0 c0) (var 2)) a' := by
      intro hw'
      -- a p-headed term is never prefixed by the S- or b0-headed w.y unless b0 is p-headed
      have := wpre_headeq _ a' hw'
      rw [hp, hw] at this
      exact hb0 this.symm
    rw [rho_headvar _ _ _ 0 a' hna hp]
    simp [sgq, head]


/-! ## Theorem PA (pattern alpha): a single-wrapper handler glued in pattern alpha never leads to a proper transfer
    in the next phase, given the phase-2 guards.  Part 1: the barrier phase. -/

def wpreB (w : T) : T → Bool
  | S => decide (S = w)
  | var n => decide (var n = w)
  | app f x => decide (app f x = w) || wpreB w f

theorem wpreB_iff (w : T) : ∀ t : T, wpreB w t = true ↔ wpre w t
  | S => by simp [wpreB, wpre]
  | var n => by simp [wpreB, wpre]
  | app f x => by simp [wpreB, wpre, wpreB_iff w f]

/-- barrier elements: prefixed by c0' (the opaque first argument) or headed by the live atom var 0 -/
def barB (c0' : T) (t : T) : Bool := wpreB c0' t || decide (head t = var 0)

def nbar (c0' : T) : List T → Nat
  | [] => 0
  | e :: L => (if barB c0' e = true then 1 else 0) + nbar c0' L

theorem nbar_append (c0' : T) : ∀ A B : List T, nbar c0' (A ++ B) = nbar c0' A + nbar c0' B
  | [], B => by simp [nbar]
  | e :: A, B => by simp [nbar, nbar_append c0' A B]; omega

theorem barB_app (c0' b d : T) (h : barB c0' b = true) : barB c0' (app b d) = true := by
  simp only [barB, Bool.or_eq_true, decide_eq_true_eq] at *
  rcases h with h | h
  · left; rw [wpreB_iff] at *; exact Or.inr h
  · right; simpa [head] using h

def BOT : List T := [var 2, app (var 1) (var 2), var 3]

def BI (c0' : T) (L : List T) : Prop :=
  ∃ Tp : List T, L = Tp ++ BOT ∧ (∀ e ∈ Tp, occ2 e = 0) ∧ 2 ≤ nbar c0' Tp

theorem bi_shape (c0' : T) (a : T) (L : List T) (hI : BI c0' (a :: L)) (hna : barB c0' a = false) :
    ∃ b d R', a :: L = a :: b :: d :: R' ++ BOT ∧ (∀ e ∈ a :: b :: d :: R', occ2 e = 0) ∧
      2 ≤ nbar c0' (b :: d :: R') := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbar] at hn
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, hn =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    simp [nbar, hna] at hn; split at hn <;> omega
  | a1 :: b1 :: d1 :: R1, hL, hy, hn =>
    simp at hL; obtain ⟨rfl, hL2⟩ := hL
    refine ⟨b1, d1, R1, by rw [hL2]; simp [BOT], hy, ?_⟩
    simp [nbar, hna] at hn ⊢; omega

theorem bi_step (c0' : T) (a b d : T) (R : List T) (hI : BI c0' (a :: b :: d :: R)) (_hS : head a = S)
    (hna : barB c0' a = false) : BI c0' (args a ++ d :: app b d :: R) := by
  obtain ⟨b1, d1, R1, hL, hy, hn⟩ := bi_shape c0' a _ hI hna
  simp at hL
  obtain ⟨rfl, rfl, hR⟩ := hL
  refine ⟨args a ++ d :: app b d :: R1, by rw [hR]; simp, ?_, ?_⟩
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact occ2_args a (hy a (by simp)) e he
    · rw [he]; exact hy d (by simp)
    · rw [he]; simp only [occ2]; have := hy b (by simp); have := hy d (by simp); omega
    · exact hy e (by simp [he])
  · rw [nbar_append]
    have hbd : (if barB c0' b = true then 1 else 0) ≤ (if barB c0' (app b d) = true then 1 else 0) := by
      by_cases hb : barB c0' b = true
      · simp [hb, barB_app c0' b d hb]
      · simp [hb]
    simp only [nbar] at hn ⊢
    omega

/-- at a p'-front during the barrier phase, position 3 is y-free or the bare y: no proper transfer -/
theorem bi_x2 (c0' : T) (a b d : T) (R : List T) (hI : BI c0' (a :: b :: d :: R)) :
    occ2 d = 0 ∨ d = var 2 := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbar] at hn
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, _ => simp [BOT] at hL; right; exact hL.2.2.1
  | a1 :: b1 :: d1 :: R1, hL, hy, _ =>
    simp at hL; obtain ⟨_, _, rfl, _⟩ := hL
    left; exact hy d (by simp)

theorem args_wpre (w : T) (hw : head w = S) : ∀ f : T, wpre w f → ∃ us, args f = args w ++ us
  | S, h => by simp [wpre] at h; subst h; exact ⟨[], by simp⟩
  | var n, h => by simp [wpre] at h; subst h; simp [head] at hw
  | app g x, h => by
    rcases h with h | h
    · rw [h]; exact ⟨[], by simp⟩
    · obtain ⟨us, hus⟩ := args_wpre w hw g h
      exact ⟨us ++ [x], by simp [args, hus]⟩

/-- opening the first c0'-prefixed front exposes c0''s arguments followed by at least two further elements -/
theorem x1_open (c0' f b d : T) (R : List T) (hw : head c0' = S) (hf : wpre c0' f) :
    ∃ e1 e2 B', step (f :: b :: d :: R) = some (args c0' ++ e1 :: e2 :: B') := by
  have hfS : head f = S := by rw [wpre_headeq c0' f hf]; exact hw
  obtain ⟨us, hus⟩ := args_wpre c0' hw f hf
  have hs : step (f :: b :: d :: R) = some (args c0' ++ (us ++ d :: app b d :: R)) := by
    simp [step, hfS, hus]
  match us, hs with
  | [], hs => exact ⟨d, app b d, R, by simpa using hs⟩
  | [u], hs => exact ⟨u, d, app b d :: R, by simpa using hs⟩
  | u1 :: u2 :: us', hs => exact ⟨u1, u2, us' ++ d :: app b d :: R, by simpa using hs⟩

/-! Part 2: run arithmetic and guard bookkeeping -/

theorem run_add : ∀ (k i : Nat) (L : List T), run (k + i) L = (run k L).bind (fun L' => run i L')
  | 0, i, L => by simp [run]
  | k + 1, i, L => by
    have : k + 1 + i = (k + i) + 1 := by omega
    rw [this]
    simp only [run]
    cases step L with
    | none => simp
    | some L' => simp [run_add k i L']

theorem run_prefix (k j : Nat) (L L' : List T) (h : run k L = some L') (hj : j ≤ k) :
    ∃ Lj, run j L = some Lj ∧ run (k - j) Lj = some L' := by
  have h2 := run_add j (k - j) L
  rw [show j + (k - j) = k by omega, h] at h2
  cases hr : run j L with
  | none => rw [hr] at h2; simp at h2
  | some Lj => rw [hr] at h2; exact ⟨Lj, rfl, by simpa using h2.symm⟩

theorem runOK_after (w : T) : ∀ (j k : Nat) (L Lj : List T), runOK w k L → run j L = some Lj → j ≤ k →
    runOK w (k - j) Lj
  | 0, k, L, Lj, hok, h, _ => by simp [run] at h; subst h; simpa using hok
  | j + 1, k, L, Lj, hok, h, hj => by
    match k, hok with
    | k' + 1, hok =>
      obtain ⟨_, hrest⟩ := hok
      simp only [run] at h
      cases hs : step L with
      | none => rw [hs] at h; simp at h
      | some L1 =>
        rw [hs] at h hrest
        simp only at h hrest
        have := runOK_after w j k' L1 Lj hrest h (by omega)
        simpa [show k' + 1 - (j + 1) = k' - j by omega] using this

theorem runOK_G (w : T) (k : Nat) (L : List T) (hok : runOK w (k + 1) L) : G w L := hok.1

/-- the substitution of the replay at the x1-front: p -> c, y -> e1 -/
def sgE (c : Nat) (e1 : T) : Nat → T := fun n => if n = 0 then var c else if n = 2 then e1 else var n

theorem asub_sgE_noy (c : Nat) (e1 : T) : ∀ t : T, occ2 t = 0 → asub (sgE c e1) t = sb c t
  | S, _ => by simp [asub, sb]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, sgE]
    · have h2 : n ≠ 2 := by intro e; subst e; simp [occ2] at h
      simp [asub, sb, sgE, h0, h2]
  | app f x, h => by
    simp only [occ2] at h
    simp [asub, sb, asub_sgE_noy c e1 f (by omega), asub_sgE_noy c e1 x (by omega)]

theorem pa_image (b0 c0 e1 e2 : T) (c : Nat) (hS : head c0 = S) (hy : occ2 c0 = 0) :
    (args c0 ++ [var 2, app (app b0 c0) (var 2)]).map (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) =
      args (sb c c0) ++ [e1, e2] := by
  rw [sb_args c c0 hS]
  simp only [List.map_append, List.map_cons, List.map_nil]
  have hargs : (args c0).map (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) = (args c0).map (sb c) := by
    apply List.map_congr_left
    intro e he
    have hsz : size e < size (app (app b0 c0) (var 2)) := by
      have := size_args c0 e he
      simp [size]; omega
    rw [rho_small _ _ _ e hsz]
    exact asub_sgE_noy c e1 e (occ2_args c0 hy e he)
  rw [hargs, rho_self]
  have h2 : rho (app (app b0 c0) (var 2)) e2 (sgE c e1) (var 2) = e1 := by
    have : var 2 ≠ app (app b0 c0) (var 2) := by intro h; cases h
    simp [rho, this, sgE]
  simp [h2]

theorem step_head_ne (x : T) (L : List T) (h : head x ≠ S) : step (x :: L) = none := by
  match L with
  | [] => simp [step]
  | [_] => simp [step]
  | _ :: _ :: R => simp [step, h]

/-! Part 3: the phase invariant and Theorem PA -/

theorem runOK_mono (w : T) : ∀ (k j : Nat) (L : List T), runOK w k L → j ≤ k → runOK w j L
  | _, 0, _, _, _ => trivial
  | 0, j + 1, _, _, hj => by omega
  | k + 1, j + 1, L, hok, hj => by
    obtain ⟨hG, hrest⟩ := hok
    refine ⟨hG, ?_⟩
    cases hs : step L with
    | none => trivial
    | some L' => rw [hs] at hrest; exact runOK_mono w k j L' hrest (by omega)

theorem wpre_self (w : T) : wpre w w := by
  cases w <;> simp [wpre]

theorem sb_occ2 (c : Nat) (hc2 : c ≠ 2) : ∀ t : T, occ2 t = 0 → occ2 (sb c t) = 0
  | S, _ => by simp [sb, occ2]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [sb, occ2, hc2]
    · simp [sb, h0]; simpa [occ2] using h
  | app f x, h => by
    simp only [occ2] at h
    simp only [sb, occ2]
    rw [sb_occ2 c hc2 f (by omega), sb_occ2 c hc2 x (by omega)]

theorem pa_phase (c0' : T) (L0 : List T) (h0 : BI c0' L0) : ∀ (m : Nat) (L : List T), run m L0 = some L →
    BI c0' L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre c0' f) ∧ run (m - m1) L1 = some L
  | 0, L, h => by simp [run] at h; subst h; exact Or.inl h0
  | m + 1, L, h => by
    have hadd := run_add m 1 L0
    rw [h] at hadd
    cases hm : run m L0 with
    | none => rw [hm] at hadd; simp at hadd
    | some Lm =>
      rw [hm] at hadd
      have h1 : run 1 Lm = some L := by simpa using hadd.symm
      have hstep : step Lm = some L := by
        simp only [run] at h1
        cases hs : step Lm with
        | none => rw [hs] at h1; simp at h1
        | some L' => rw [hs] at h1; simp at h1; rw [h1]
      rcases pa_phase c0' L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          simp only [step] at hstep
          split at hstep
          · rename_i hfS
            by_cases hb : barB c0' f = true
            · right
              have hwp : wpre c0' f := by
                simp only [barB, Bool.or_eq_true, decide_eq_true_eq] at hb
                rcases hb with hb | hb
                · exact (wpreB_iff c0' f).1 hb
                · rw [hfS] at hb; simp at hb
              refine ⟨m, f :: b :: d :: R, by omega, hm, ⟨f, b, d, R, rfl, hwp⟩, ?_⟩
              simpa using h1
            · left
              have hbf : barB c0' f = false := by simpa using hb
              injection hstep with hstep; subst hstep
              exact bi_step c0' f b d R hB hfS hbf
          · exact absurd hstep (by simp)
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

/-- **Theorem PA.**  Let the innermost single wrapper of a phase-2 handler be w = b0.c0 (b0, c0 S-headed and free
    of y), glued onto y in pattern alpha, i.e. by the step [c0, w, y] ++ R0, after which phase 2 continues from the
    top part args c0 ++ [y, w.y].  Assume this top part reaches a p-headed front (the TRANSFER) after k steps
    under the replay guards (no (w.y)-prefixed front, w.y never re-created).  Then in the generic run of the next
    phase's datum w[p:=c].p' (here p' = var 0 and c a frozen atom) every p'-headed front has at position 3 a
    y-free element or the bare y: the next phase NEVER makes a proper transfer. -/
theorem pa_main (b0 c0 : T) (c : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args c0 ++ [var 2, app (app b0 c0) (var 2)]) = some (a' :: rest))
    (hok : runOK (app (app b0 c0) (var 2)) k (args c0 ++ [var 2, app (app b0 c0) (var 2)]))
    (hp : head a' = var 0) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hstep0 : step [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] =
      some ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    simp [step, head, hb0', args, BOT]
  have hBI : BI (sb c c0) ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    refine ⟨args (sb c b0) ++ [sb c c0, var 0], rfl, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB (sb c c0) (sb c c0) = true := by
        simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB (sb c c0) (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  match m, hm with
  | 0, hm =>
    simp [run] at hm
    obtain ⟨hf0, _⟩ := hm
    rw [← hf0] at hf; simp [head, hb0'] at hf
  | m' + 1, hm =>
    simp only [run] at hm
    rw [hstep0] at hm
    simp only at hm
    rcases pa_phase (sb c c0) _ hBI m' _ hm with hB | ⟨m1, L1, hlt, _, ⟨f1, b1, d1, R1, hL1, hwp⟩, hrest⟩
    · exact bi_x2 (sb c c0) f b d R hB
    · exfalso
      obtain ⟨e1, e2, B', hs1⟩ := x1_open (sb c c0) f1 b1 d1 R1 hc0' hwp
      subst hL1
      have hj : m' - m1 = (m' - m1 - 1) + 1 := by omega
      rw [hj] at hrest
      simp only [run] at hrest
      rw [hs1] at hrest
      simp only at hrest
      have himg := pa_image b0 c0 e1 e2 c hc0S hy1
      have hM0 : args (sb c c0) ++ e1 :: e2 :: B' =
          (args c0 ++ [var 2, app (app b0 c0) (var 2)]).map (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) ++ B' := by
        rw [himg]; simp
      rw [hM0] at hrest
      have hwyS : head (app (app b0 c0) (var 2)) = S := by simp [head, hb0S]
      have hna' : ¬ wpre (app (app b0 c0) (var 2)) a' := by
        intro hw; have := wpre_headeq _ a' hw; rw [hp, hwyS] at this; simp at this
      have hca' : head (rho (app (app b0 c0) (var 2)) e2 (sgE c e1) a') = var c := by
        rw [rho_headvar _ _ _ 0 a' hna' hp]; simp [sgE, head]
      by_cases hjk : m' - m1 - 1 ≤ k
      · obtain ⟨Pj, hPj, hPk⟩ := run_prefix k (m' - m1 - 1) _ _ hrun hjk
        have hokj := runOK_mono _ k (m' - m1 - 1) _ hok hjk
        have hrep := replay_run_gen (app (app b0 c0) (var 2)) e2 (sgE c e1) (m' - m1 - 1) _ _ hokj hPj
        have happ := run_append (m' - m1 - 1) _ _ B' hrep
        rw [hrest] at happ
        injection happ with happ
        match Pj, happ, hPk, hPj with
        | [], happ, hPk, _ =>
          cases hkj : k - (m' - m1 - 1) with
          | zero => rw [hkj] at hPk; simp [run] at hPk
          | succ n => rw [hkj] at hPk; simp [run, step] at hPk
        | pj :: pjs, happ, hPk, hPj =>
          simp at happ
          obtain ⟨hfj, _⟩ := happ
          by_cases hjk' : m' - m1 - 1 = k
          · have h0k : k - (m' - m1 - 1) = 0 := by omega
            rw [h0k] at hPk; simp [run] at hPk
            obtain ⟨hpj, _⟩ := hPk
            rw [hpj] at hfj
            rw [hfj, hca'] at hf
            injection hf with hf; exact hc hf
          · have hok2 := runOK_after _ (m' - m1 - 1) k _ _ hok hPj hjk
            have hk1 : k - (m' - m1 - 1) = (k - (m' - m1 - 1) - 1) + 1 := by omega
            rw [hk1] at hok2 hPk
            have hG := runOK_G _ _ _ hok2
            simp only [run] at hPk
            match pjs, hG, hPk with
            | q1 :: q2 :: qs, hG, hPk =>
              obtain ⟨hnw, _⟩ := hG
              by_cases hpS : head pj = S
              · have := rho_headS _ e2 (sgE c e1) pj hnw hpS
                rw [← hfj, hf] at this; simp at this
              · simp [step, hpS] at hPk
            | [], _, hPk => simp [step] at hPk
            | [_], _, hPk => simp [step] at hPk
      · have hrep := replay_run_gen (app (app b0 c0) (var 2)) e2 (sgE c e1) k _ _ hok hrun
        have happ := run_append k _ _ B' hrep
        have hsplit := run_add (k + 1) ((m' - m1 - 1) - (k + 1)) ((args c0 ++ [var 2, app (app b0 c0) (var 2)]).map
          (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) ++ B')
        rw [show k + 1 + ((m' - m1 - 1) - (k + 1)) = m' - m1 - 1 by omega, hrest] at hsplit
        have hk1 := run_add k 1 ((args c0 ++ [var 2, app (app b0 c0) (var 2)]).map
          (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) ++ B')
        rw [happ] at hk1
        have hstuck : run 1 (List.map (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) (a' :: rest) ++ B') = none := by
          have hne : head (rho (app (app b0 c0) (var 2)) e2 (sgE c e1) a') ≠ S := by rw [hca']; simp
          simp only [List.map_cons, List.cons_append, run]
          rw [step_head_ne _ _ hne]
        have hk1' : run (k + 1) ((args c0 ++ [var 2, app (app b0 c0) (var 2)]).map
            (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) ++ B') = none := by
          rw [hk1]; simpa using hstuck
        rw [hk1'] at hsplit
        simp at hsplit


/-! ## Theorem PB (pattern beta with c0 = S.a1) and the reusable pieces: post-x1 replay for a general first code g,
    and the barrier phase with an abstract post-x1 safety hypothesis. -/

theorem pa_image_gen (wy g e1 e2 : T) (c : Nat) (hS : head g = S) (hy : occ2 g = 0)
    (hsz : size g < size wy) (hwy2 : var 2 ≠ wy) :
    (args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) = args (sb c g) ++ [e1, e2] := by
  rw [sb_args c g hS]
  simp only [List.map_append, List.map_cons, List.map_nil]
  have hargs : (args g).map (rho wy e2 (sgE c e1)) = (args g).map (sb c) := by
    apply List.map_congr_left
    intro e he
    have hsz' : size e < size wy := by
      have := size_args g e he
      omega
    rw [rho_small _ _ _ e hsz']
    exact asub_sgE_noy c e1 e (occ2_args g hy e he)
  rw [hargs, rho_self]
  have h2 : rho wy e2 (sgE c e1) (var 2) = e1 := by
    simp [rho, hwy2, sgE]
  simp [h2]

/-- **Post-x1 replay.**  If the phase-2 top part args g ++ [y, wy] reaches a p-headed front after k guarded steps,
    then no run from args(g[p:=c]) ++ [e1, e2, ...] ever reaches a front headed by var 0 (it replays phase 2 and
    stops at a c-headed front). -/
theorem post_replay (wy g : T) (c : Nat) (hc : c ≠ 0) (hgS : head g = S) (hgy : occ2 g = 0)
    (hsz : size g < size wy) (hwy2 : var 2 ≠ wy) (hwyh : head wy ≠ var 0)
    (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args g ++ [var 2, wy]) = some (a' :: rest))
    (hok : runOK wy k (args g ++ [var 2, wy])) (hp : head a' = var 0) :
    ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args (sb c g) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0 := by
  intro e1 e2 B' j f L hrest hf
  have himg := pa_image_gen wy g e1 e2 c hgS hgy hsz hwy2
  have hM0 : args (sb c g) ++ e1 :: e2 :: B' = (args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B' := by
    rw [himg]; simp
  rw [hM0] at hrest
  have hna' : ¬ wpre wy a' := by
    intro hw; have := wpre_headeq _ a' hw; rw [hp] at this; exact hwyh this.symm
  have hca' : head (rho wy e2 (sgE c e1) a') = var c := by
    rw [rho_headvar _ _ _ 0 a' hna' hp]; simp [sgE, head]
  by_cases hjk : j ≤ k
  · obtain ⟨Pj, hPj, hPk⟩ := run_prefix k j _ _ hrun hjk
    have hokj := runOK_mono _ k j _ hok hjk
    have hrep := replay_run_gen wy e2 (sgE c e1) j _ _ hokj hPj
    have happ := run_append j _ _ B' hrep
    rw [hrest] at happ
    injection happ with happ
    match Pj, happ, hPk, hPj with
    | [], happ, hPk, _ =>
      cases hkj : k - j with
      | zero => rw [hkj] at hPk; simp [run] at hPk
      | succ n => rw [hkj] at hPk; simp [run, step] at hPk
    | pj :: pjs, happ, hPk, hPj =>
      simp at happ
      obtain ⟨hfj, _⟩ := happ
      by_cases hjk' : j = k
      · have h0k : k - j = 0 := by omega
        rw [h0k] at hPk; simp [run] at hPk
        obtain ⟨hpj, _⟩ := hPk
        rw [hpj] at hfj
        rw [hfj, hca'] at hf
        injection hf with hf; exact hc hf
      · have hok2 := runOK_after _ j k _ _ hok hPj hjk
        have hk1 : k - j = (k - j - 1) + 1 := by omega
        rw [hk1] at hok2 hPk
        have hG := runOK_G _ _ _ hok2
        simp only [run] at hPk
        match pjs, hG, hPk with
        | q1 :: q2 :: qs, hG, hPk =>
          obtain ⟨hnw, _⟩ := hG
          by_cases hpS : head pj = S
          · have := rho_headS _ e2 (sgE c e1) pj hnw hpS
            rw [← hfj, hf] at this; simp at this
          · simp [step, hpS] at hPk
        | [], _, hPk => simp [step] at hPk
        | [_], _, hPk => simp [step] at hPk
  · have hrep := replay_run_gen wy e2 (sgE c e1) k _ _ hok hrun
    have happ := run_append k _ _ B' hrep
    have hsplit := run_add (k + 1) (j - (k + 1)) ((args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B')
    rw [show k + 1 + (j - (k + 1)) = j by omega, hrest] at hsplit
    have hk1 := run_add k 1 ((args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B')
    rw [happ] at hk1
    have hstuck : run 1 (List.map (rho wy e2 (sgE c e1)) (a' :: rest) ++ B') = none := by
      have hne : head (rho wy e2 (sgE c e1) a') ≠ S := by rw [hca']; simp
      simp only [List.map_cons, List.cons_append, run]
      rw [step_head_ne _ _ hne]
    have hk1' : run (k + 1) ((args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B') = none := by
      rw [hk1]; simpa using hstuck
    rw [hk1'] at hsplit
    simp at hsplit

/-- **Barrier phase with an abstract post-x1 safety.**  For the next-phase datum (b0'.c0').p', if no run from
    args(c0') ++ [e1, e2, ...] ever reaches a p'-headed front, then every p'-headed front of the phase has a y-free
    element or the bare y at position 3. -/
theorem pa_core (b0 c0 : T) (c : Nat) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args (sb c c0) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hstep0 : step [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] =
      some ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    simp [step, head, hb0', args, BOT]
  have hBI : BI (sb c c0) ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    refine ⟨args (sb c b0) ++ [sb c c0, var 0], rfl, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB (sb c c0) (sb c c0) = true := by
        simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB (sb c c0) (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  match m, hm with
  | 0, hm =>
    simp [run] at hm
    obtain ⟨hf0, _⟩ := hm
    rw [← hf0] at hf; simp [head, hb0'] at hf
  | m' + 1, hm =>
    simp only [run] at hm
    rw [hstep0] at hm
    simp only at hm
    rcases pa_phase (sb c c0) _ hBI m' _ hm with hB | ⟨m1, L1, hlt, _, ⟨f1, b1, d1, R1, hL1, hwp⟩, hrest⟩
    · exact bi_x2 (sb c c0) f b d R hB
    · exfalso
      obtain ⟨e1, e2, B', hs1⟩ := x1_open (sb c c0) f1 b1 d1 R1 hc0' hwp
      subst hL1
      have hj : m' - m1 = (m' - m1 - 1) + 1 := by omega
      rw [hj] at hrest
      simp only [run] at hrest
      rw [hs1] at hrest
      simp only at hrest
      exact hpost e1 e2 B' _ f _ hrest hf

/-- **Theorem PB (pattern beta, c0 = S.a1).**  If the single wrapper is w = b0.(S.a1) and it was glued onto y by the
    step [a1, w, y] (a1 released just above w), and the phase-2 continuation from that glue (top part
    args a1 ++ [y, w.y]) reaches a p-headed front after k guarded steps, then the next phase never makes a proper
    transfer. -/
theorem pb_main (b0 a1 : T) (c : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hb0S : head b0 = S) (ha1S : head a1 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 a1 = 0) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args a1 ++ [var 2, app (app b0 (app S a1)) (var 2)]) = some (a' :: rest))
    (hok : runOK (app (app b0 (app S a1)) (var 2)) k (args a1 ++ [var 2, app (app b0 (app S a1)) (var 2)]))
    (hp : head a' = var 0) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c (app S a1))) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  have hc0S : head (app S a1) = S := by simp [head]
  have hy1' : occ2 (app S a1) = 0 := by simp [occ2]; exact hy1
  apply pa_core b0 (app S a1) c hc2 hb0S hc0S hy0 hy1'
  intro e1 e2 B' j f L hrun' hf
  have ha1' : head (sb c a1) = S := sb_head c a1 ha1S
  have hargs : args (sb c (app S a1)) = [sb c a1] := by simp [sb, args]
  rw [hargs] at hrun'
  match j, hrun' with
  | 0, hrun' =>
    simp [run] at hrun'
    obtain ⟨hf0, _⟩ := hrun'
    rw [← hf0, ha1'] at hf; simp at hf
  | j' + 1, hrun' =>
    have hs : step (sb c a1 :: e1 :: e2 :: B') = some (args (sb c a1) ++ e2 :: app e1 e2 :: B') := by
      simp [step, ha1']
    simp only [List.singleton_append, run] at hrun'
    rw [hs] at hrun'
    simp only at hrun'
    have hwy2 : var 2 ≠ app (app b0 (app S a1)) (var 2) := by intro h; cases h
    have hwyh : head (app (app b0 (app S a1)) (var 2)) ≠ var 0 := by simp [head, hb0S]
    have hsz : size a1 < size (app (app b0 (app S a1)) (var 2)) := by simp [size]; omega
    exact post_replay _ a1 c hc ha1S hy1 hsz hwy2 hwyh k a' rest hrun hok hp e2 (app e1 e2) B' j' f _ hrun' hf


/-! ## Theorem PAM: Theorem PA for MULTI-WRAPPER handlers, at the innermost level.
    p' occurs in the next datum only inside copies of its innermost level Ln = vn'.p'; until an Ln-prefixed
    element is opened every element is 'guarded' (no p'-front); the first such opening yields
    args(b0') ++ [c0', p'] ++ B, and from there the barrier phase and the post-x1 replay of phase 2's continuation from
    vn's glue step apply exactly as in Theorem PA, provided the element B0 right below p' is y-free or the bare y. -/

def guarded (Lv : T) : T → Prop
  | S => True
  | var n => n ≠ 0
  | app f x => app f x = Lv ∨ (guarded Lv f ∧ guarded Lv x)

theorem guarded_head (Lv : T) (hL : head Lv ≠ var 0) : ∀ t : T, guarded Lv t → head t ≠ var 0
  | S, _ => by simp [head]
  | var n, h => by simp [guarded] at h; simp [head]; exact h
  | app f x, h => by
    rcases h with h | ⟨hf, _⟩
    · rw [h]; exact hL
    · simp [head]; exact guarded_head Lv hL f hf

theorem guarded_args (Lv : T) : ∀ t : T, guarded Lv t → head t = S → ¬ wpre Lv t → ∀ s ∈ args t, guarded Lv s
  | S, _, _, _, s, hs => by simp [args] at hs
  | var _, _, hh, _, _, _ => by simp [head] at hh
  | app f x, h, hh, hn, s, hs => by
    have h1 : app f x ≠ Lv := fun e => hn (Or.inl e)
    have h2 : ¬ wpre Lv f := fun e => hn (Or.inr e)
    rcases h with h | ⟨hf, hx⟩
    · exact absurd h h1
    · simp [args] at hs
      rcases hs with hs | hs
      · exact guarded_args Lv f hf (by simpa [head] using hh) h2 s hs
      · subst hs; exact hx

/-- a bottom is admissible if its first element is y-free or the bare y -/
def B0ok (B : List T) : Prop := ∀ e, B.head? = some e → occ2 e = 0 ∨ e = var 2

def BIg (c0' : T) (B : List T) (L : List T) : Prop :=
  ∃ Tp : List T, L = Tp ++ B ∧ (∀ e ∈ Tp, occ2 e = 0) ∧ 2 ≤ nbar c0' Tp

theorem big_step (c0' : T) (B : List T) (a b d : T) (R : List T) (hI : BIg c0' B (a :: b :: d :: R))
    (hna : barB c0' a = false) : BIg c0' B (args a ++ d :: app b d :: R) := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbar] at hn
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, hn =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    simp [nbar, hna] at hn; split at hn <;> omega
  | a1 :: b1 :: d1 :: R1, hL, hy, hn =>
    simp at hL
    obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    refine ⟨args a ++ d :: app b d :: R1, by rw [hR]; simp, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he | he
      · exact occ2_args a (hy a (by simp)) e he
      · rw [he]; exact hy d (by simp)
      · rw [he]; simp only [occ2]; have := hy b (by simp); have := hy d (by simp); omega
      · exact hy e (by simp [he])
    · rw [nbar_append]
      have hbd : (if barB c0' b = true then 1 else 0) ≤ (if barB c0' (app b d) = true then 1 else 0) := by
        by_cases hb : barB c0' b = true
        · simp [hb, barB_app c0' b d hb]
        · simp [hb]
      simp only [nbar, hna] at hn ⊢
      simp at hn ⊢
      omega

theorem big_x2 (c0' : T) (B : List T) (hB : B0ok B) (a b d : T) (R : List T)
    (hI : BIg c0' B (a :: b :: d :: R)) : occ2 d = 0 ∨ d = var 2 := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbar] at hn
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, _ =>
    simp at hL
    obtain ⟨_, _, hB2⟩ := hL
    exact hB d (by rw [← hB2]; simp)
  | a1 :: b1 :: d1 :: R1, hL, hy, _ =>
    simp at hL; obtain ⟨_, _, rfl, _⟩ := hL
    left; exact hy d (by simp)

theorem pa_phase_g (c0' : T) (B : List T) (L0 : List T) (h0 : BIg c0' B L0) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    BIg c0' B L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre c0' f) ∧ run (m - m1) L1 = some L
  | 0, L, h => by simp [run] at h; subst h; exact Or.inl h0
  | m + 1, L, h => by
    have hadd := run_add m 1 L0
    rw [h] at hadd
    cases hm : run m L0 with
    | none => rw [hm] at hadd; simp at hadd
    | some Lm =>
      rw [hm] at hadd
      have h1 : run 1 Lm = some L := by simpa using hadd.symm
      have hstep : step Lm = some L := by
        simp only [run] at h1
        cases hs : step Lm with
        | none => rw [hs] at h1; simp at h1
        | some L' => rw [hs] at h1; simp at h1; rw [h1]
      rcases pa_phase_g c0' B L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          simp only [step] at hstep
          split at hstep
          · rename_i hfS
            by_cases hb : barB c0' f = true
            · right
              have hwp : wpre c0' f := by
                simp only [barB, Bool.or_eq_true, decide_eq_true_eq] at hb
                rcases hb with hb | hb
                · exact (wpreB_iff c0' f).1 hb
                · rw [hfS] at hb; simp at hb
              refine ⟨m, f :: b :: d :: R, by omega, hm, ⟨f, b, d, R, rfl, hwp⟩, ?_⟩
              simpa using h1
            · left
              have hbf : barB c0' f = false := by simpa using hb
              injection hstep with hstep; subst hstep
              exact big_step c0' B f b d R hB hbf
          · exact absurd hstep (by simp)
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

/-- the generalised core: from any list args(b0') ++ [c0', p'] ++ B with an admissible bottom B -/
theorem pa_core_g (b0' c0' : T) (B : List T) (hB : B0ok B) (hc0' : head c0' = S)
    (hy0' : occ2 b0' = 0) (hy1' : occ2 c0' = 0)
    (hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args c0' ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m (args b0' ++ [c0', var 0] ++ B) = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hBI : BIg c0' B (args b0' ++ [c0', var 0] ++ B) := by
    refine ⟨args b0' ++ [c0', var 0], rfl, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB c0' c0' = true := by simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB c0' (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  rcases pa_phase_g c0' B _ hBI m _ hm with hB' | ⟨m1, L1, hlt, _, ⟨f1, b1, d1, R1, hL1, hwp⟩, hrest⟩
  · exact big_x2 c0' B hB f b d R hB'
  · exfalso
    obtain ⟨e1, e2, B', hs1⟩ := x1_open c0' f1 b1 d1 R1 hc0' hwp
    subst hL1
    have hj : m - m1 = (m - m1 - 1) + 1 := by omega
    rw [hj] at hrest
    simp only [run] at hrest
    rw [hs1] at hrest
    simp only at hrest
    exact hpost e1 e2 B' _ f _ hrest hf

/-- the guarded phase: until an Ln-prefixed front is opened no front is p'-headed -/
theorem guarded_phase (Ln : T) (hLnS : head Ln = S) (L0 : List T) (h0 : ∀ e ∈ L0, guarded Ln e) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    (∀ e ∈ L, guarded Ln e) ∨ ∃ m1 L1 L2, m1 < m ∧ run m1 L0 = some L1 ∧ (∀ e ∈ L1, guarded Ln e) ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre Ln f) ∧ step L1 = some L2 ∧ run (m - m1 - 1) L2 = some L
  | 0, L, h => by simp [run] at h; subst h; exact Or.inl h0
  | m + 1, L, h => by
    have hadd := run_add m 1 L0
    rw [h] at hadd
    cases hm : run m L0 with
    | none => rw [hm] at hadd; simp at hadd
    | some Lm =>
      rw [hm] at hadd
      have h1 : run 1 Lm = some L := by simpa using hadd.symm
      have hstep : step Lm = some L := by
        simp only [run] at h1
        cases hs : step Lm with
        | none => rw [hs] at h1; simp at h1
        | some L' => rw [hs] at h1; simp at h1; rw [h1]
      rcases guarded_phase Ln hLnS L0 h0 m Lm hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
      · match Lm, hG, hstep, hm with
        | a :: b :: d :: R, hG, hstep, hm =>
          simp only [step] at hstep
          split at hstep
          · rename_i haS
            by_cases hpre : wpre Ln a
            · right
              refine ⟨m, a :: b :: d :: R, L, by omega, hm, hG, ⟨a, b, d, R, rfl, hpre⟩, ?_, by simp [run]⟩
              simp [step, haS] at hstep ⊢; exact hstep
            · left
              injection hstep with hstep; subst hstep
              intro e he; simp at he
              rcases he with he | he | he | he
              · exact guarded_args Ln a (hG a (by simp)) haS hpre e he
              · rw [he]; exact hG d (by simp)
              · rw [he]; exact Or.inr ⟨hG b (by simp), hG d (by simp)⟩
              · exact hG e (by simp [he])
          · exact absurd hstep (by simp)
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, L2, by omega, hr1, hg1, hx1, hs2, ?_⟩
        have hadd2 := run_add (m - m1 - 1) 1 L2
        rw [hrest] at hadd2
        rw [show m + 1 - m1 - 1 = (m - m1 - 1) + 1 by omega, hadd2]
        simpa using h1

/-- **Theorem PAM.**  Let the innermost wrapper of a (possibly multi-wrapper) phase-2 handler be vn = b0.c0, glued in
    pattern alpha, with phase 2's continuation from that glue (top part args c0 ++ [y, vn.y]) reaching its TRANSFER
    after k guarded steps.  Let L0 be the start of the next phase, in which every occurrence of p' = var 0 lies inside
    an occurrence of the innermost level Ln = vn[p:=c].p' (true for the datum V[y:=p', p:=c]).  If the element right
    below p' after every opening of an Ln-prefixed front is y-free or the bare y (hypothesis hB0), then every
    p'-headed front of the next phase has a y-free element or the bare y at position 3: no proper transfer. -/
theorem pam_main (b0 c0 : T) (c : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args c0 ++ [var 2, app (app b0 c0) (var 2)]) = some (a' :: rest))
    (hok : runOK (app (app b0 c0) (var 2)) k (args c0 ++ [var 2, app (app b0 c0) (var 2)]))
    (hp : head a' = var 0) (L0 : List T)
    (h0 : ∀ e ∈ L0, guarded (app (app (sb c b0) (sb c c0)) (var 0)) e)
    (hB0 : ∀ (m1 : Nat) (L1 L2 : List T), run m1 L0 = some L1 →
      (∀ e ∈ L1, guarded (app (app (sb c b0) (sb c c0)) (var 0)) e) →
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre (app (app (sb c b0) (sb c c0)) (var 0)) f) →
      step L1 = some L2 → ∀ B, L2 = args (sb c b0) ++ [sb c c0, var 0] ++ B → B0ok B) :
    ∀ (m : Nat) (f b d : T) (R : List T), run m L0 = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hLnS : head (app (app (sb c b0) (sb c c0)) (var 0)) = S := by simp [head, hb0']
  rcases guarded_phase _ hLnS L0 h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exfalso
    have := guarded_head _ (by rw [hLnS]; simp) f (hG f (by simp))
    exact this hf
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    -- the opened element releases args(vn') ++ [p'] ++ u
    obtain ⟨us, hus⟩ := args_wpre _ hLnS f1 hwp
    have hf1S : head f1 = S := by rw [wpre_headeq _ f1 hwp]; exact hLnS
    have hs2' : step L1 = some (args (sb c b0) ++ [sb c c0, var 0] ++ (us ++ d1 :: app b1 d1 :: R1)) := by
      rw [hL1]; simp [step, hf1S, hus, args]
    rw [hs2'] at hs2
    injection hs2 with hs2
    subst hs2
    have hBok := hB0 m1 L1 _ hr1 hg1 ⟨f1, b1, d1, R1, hL1, hwp⟩ hs2' _ rfl
    have hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
        run j (args (sb c c0) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0 := by
      have hwy2 : var 2 ≠ app (app b0 c0) (var 2) := by intro h; cases h
      have hwyh : head (app (app b0 c0) (var 2)) ≠ var 0 := by simp [head, hb0S]
      have hsz : size c0 < size (app (app b0 c0) (var 2)) := by simp [size]; omega
      exact post_replay _ c0 c hc hc0S hy1 hsz hwy2 hwyh k a' rest hrun hok hp
    exact pa_core_g (sb c b0) (sb c c0) _ hBok hc0' hy0' hy1' hpost (m - m1 - 1) f b d R hrest hf


/-- **Re-execution replays the transfer (machine-checked form).**  Under the hypotheses of `post_replay`, the run from
    args(g[p:=c]) ++ [e1, e2, ...] reaches, after exactly k steps, the image under rho = (w.y -> e2, y -> e1, p -> c)
    of phase 2's transfer list a' :: rest, followed by the untouched bottom; its front is headed by the frozen c.
    So the frozen predecessor is re-executed on the images of exactly the arguments with which the live predecessor
    was activated at the transfer. -/
theorem reexec_replays_transfer (wy g : T) (c : Nat) (hgS : head g = S) (hgy : occ2 g = 0)
    (hsz : size g < size wy) (hwy2 : var 2 ≠ wy) (hwyh : head wy ≠ var 0)
    (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args g ++ [var 2, wy]) = some (a' :: rest))
    (hok : runOK wy k (args g ++ [var 2, wy])) (hp : head a' = var 0) (e1 e2 : T) (B' : List T) :
    run k (args (sb c g) ++ e1 :: e2 :: B') = some ((a' :: rest).map (rho wy e2 (sgE c e1)) ++ B') ∧
      head (rho wy e2 (sgE c e1) a') = var c := by
  have himg := pa_image_gen wy g e1 e2 c hgS hgy hsz hwy2
  have hM0 : args (sb c g) ++ e1 :: e2 :: B' = (args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B' := by
    rw [himg]; simp
  rw [hM0]
  refine ⟨run_append k _ _ B' (replay_run_gen wy e2 (sgE c e1) k _ _ hok hrun), ?_⟩
  have hna' : ¬ wpre wy a' := by
    intro hw; have := wpre_headeq _ a' hw; rw [hp] at this; exact hwyh this.symm
  rw [rho_headvar _ _ _ 0 a' hna' hp]; simp [sgE, head]


/-! ## The replayed handler is trivial (toward D3).
    Strengthened barrier invariant BIv: the top part above BOT is y-free, has >= 2 barriers AND contains a
    p'-headed element (the p'-barrier is never destroyed).  At the first c0'-prefixed front the element e2 that the
    replay substitutes for the handler w.y is y-free, or the bare y, or (p'-headed).y.  Consequently the datum that
    the re-executed frozen value would receive in the Church-chain model, e2[y := p'', p' := c'], has no live
    predecessor, or is the bare p'', or is frozen-headed: it cannot start a further proper transfer. -/

def BIv (c0' : T) (L : List T) : Prop :=
  ∃ Tp : List T, L = Tp ++ BOT ∧ (∀ e ∈ Tp, occ2 e = 0) ∧ 2 ≤ nbar c0' Tp ∧ ∃ e ∈ Tp, head e = var 0

theorem biv_bi (c0' : T) (L : List T) (h : BIv c0' L) : BI c0' L := by
  obtain ⟨Tp, h1, h2, h3, _⟩ := h
  exact ⟨Tp, h1, h2, h3⟩

theorem biv_step (c0' : T) (a b d : T) (R : List T) (hI : BIv c0' (a :: b :: d :: R)) (hS : head a = S)
    (hna : barB c0' a = false) : BIv c0' (args a ++ d :: app b d :: R) := by
  obtain ⟨Tp, hL, hy, hn, ⟨e0, he0, hh0⟩⟩ := hI
  obtain ⟨Tp', hL', hy', hn'⟩ := bi_step c0' a b d R ⟨Tp, hL, hy, hn⟩ hS hna
  refine ⟨Tp', hL', hy', hn', ?_⟩
  -- Tp = a :: b :: d :: R1 (as in bi_step); Tp' = args a ++ d :: app b d :: R1
  match Tp, hL, he0, hn with
  | [], _, he0, _ => simp at he0
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, hn =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    simp [nbar, hna] at hn; split at hn <;> omega
  | a1 :: b1 :: d1 :: R1, hL, he0, _ =>
    simp at hL
    obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hTp' : Tp' = args a ++ d :: app b d :: R1 := by
      have : Tp' ++ BOT = (args a ++ d :: app b d :: R1) ++ BOT := by rw [← hL', hR]; simp
      exact List.append_cancel_right this
    rw [hTp']
    simp at he0
    rcases he0 with he0 | he0 | he0 | he0
    · rw [he0, hS] at hh0; simp at hh0
    · exact ⟨app b d, by simp, by rw [he0] at hh0; simpa [head] using hh0⟩
    · exact ⟨d, by simp, by rw [← he0]; exact hh0⟩
    · exact ⟨e0, by simp [he0], hh0⟩

theorem pa_phase_v (c0' : T) (L0 : List T) (h0 : BIv c0' L0) : ∀ (m : Nat) (L : List T), run m L0 = some L →
    BIv c0' L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧ BIv c0' L1 ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre c0' f) ∧ run (m - m1) L1 = some L
  | 0, L, h => by simp [run] at h; subst h; exact Or.inl h0
  | m + 1, L, h => by
    have hadd := run_add m 1 L0
    rw [h] at hadd
    cases hm : run m L0 with
    | none => rw [hm] at hadd; simp at hadd
    | some Lm =>
      rw [hm] at hadd
      have h1 : run 1 Lm = some L := by simpa using hadd.symm
      have hstep : step Lm = some L := by
        simp only [run] at h1
        cases hs : step Lm with
        | none => rw [hs] at h1; simp at h1
        | some L' => rw [hs] at h1; simp at h1; rw [h1]
      rcases pa_phase_v c0' L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hb1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          simp only [step] at hstep
          split at hstep
          · rename_i hfS
            by_cases hb : barB c0' f = true
            · right
              have hwp : wpre c0' f := by
                simp only [barB, Bool.or_eq_true, decide_eq_true_eq] at hb
                rcases hb with hb | hb
                · exact (wpreB_iff c0' f).1 hb
                · rw [hfS] at hb; simp at hb
              refine ⟨m, f :: b :: d :: R, by omega, hm, hB, ⟨f, b, d, R, rfl, hwp⟩, ?_⟩
              simpa using h1
            · left
              have hbf : barB c0' f = false := by simpa using hb
              injection hstep with hstep; subst hstep
              exact biv_step c0' f b d R hB hfS hbf
          · exact absurd hstep (by simp)
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hb1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

/-- the replayed handler e2 at the first c0'-prefixed front is y-free, the bare y, or (p'-headed).y -/
def trivH (e : T) : Prop := occ2 e = 0 ∨ e = var 2 ∨ ∃ s, e = app s (var 2) ∧ head s = var 0

theorem x1_handler (c0' f b d : T) (R : List T) (hw : head c0' = S) (hf : wpre c0' f)
    (hI : BIv c0' (f :: b :: d :: R)) :
    ∃ e1 e2 B', step (f :: b :: d :: R) = some (args c0' ++ e1 :: e2 :: B') ∧ trivH e2 := by
  have hfS : head f = S := by rw [wpre_headeq c0' f hf]; exact hw
  obtain ⟨us, hus⟩ := args_wpre c0' hw f hf
  obtain ⟨Tp, hL, hy, hn, ⟨e0, he0, hh0⟩⟩ := hI
  have hs : step (f :: b :: d :: R) = some (args c0' ++ (us ++ d :: app b d :: R)) := by
    simp [step, hfS, hus]
  -- f's arguments are y-free (f is in the y-free top part)
  have hfy : occ2 f = 0 := by
    match Tp, hL, hy with
    | [], hL, _ => simp [BOT] at hL; rw [hL.1] at hfS; simp [head] at hfS
    | t0 :: Tq, hL, hy => simp at hL; rw [hL.1]; exact hy t0 (by simp)
  have hus_y : ∀ u ∈ us, occ2 u = 0 := by
    intro u hu
    have hu' : u ∈ args f := by rw [hus]; simp [hu]
    exact occ2_args f hfy u hu'
  match us, hs, hus_y with
  | u1 :: u2 :: us', hs, hus_y =>
    exact ⟨u1, u2, us' ++ d :: app b d :: R, by simpa using hs, Or.inl (hus_y u2 (by simp))⟩
  | [u1], hs, _ =>
    refine ⟨u1, d, app b d :: R, by simpa using hs, ?_⟩
    -- d is in the top part (y-free) or is the bare y
    match Tp, hL, hy, hn with
    | [], _, _, hn => simp [nbar] at hn
    | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
    | [a1, b1], hL, _, _ => simp [BOT] at hL; right; left; exact hL.2.2.1
    | a1 :: b1 :: d1 :: R1, hL, hy, _ =>
      simp at hL; obtain ⟨_, _, hd, _⟩ := hL
      left; rw [hd]; exact hy d1 (by simp)
  | [], hs, _ =>
    refine ⟨d, app b d, R, by simpa using hs, ?_⟩
    match Tp, hL, hy, hn, he0 with
    | [], _, _, hn, _ => simp [nbar] at hn
    | [a1], _, _, hn, _ => simp [nbar] at hn; split at hn <;> omega
    | [a1, b1], hL, _, _, he0 =>
      simp [BOT] at hL
      obtain ⟨hf1, hb1, hd2, _⟩ := hL
      -- the p'-headed element of [f, b] is b (f is S-headed)
      simp at he0
      rcases he0 with he0 | he0
      · rw [he0, ← hf1, hfS] at hh0; simp at hh0
      · right; right; exact ⟨b, by rw [hd2], by rw [hb1, ← he0]; exact hh0⟩
    | a1 :: b1 :: d1 :: R1, hL, hy, _, _ =>
      simp at hL; obtain ⟨_, hb1, hd1, _⟩ := hL
      left; simp only [occ2]; rw [hb1, hd1]
      have := hy b1 (by simp); have := hy d1 (by simp); omega

/-- the Church-chain model's next datum: y -> p'' (= var 0), p' (= var 0) -> c' -/
def sbq (c' : Nat) : T → T
  | S => S
  | var n => if n = 0 then var c' else if n = 2 then var 0 else var n
  | app f x => app (sbq c' f) (sbq c' x)

def occ0 : T → Nat
  | S => 0
  | var n => if n = 0 then 1 else 0
  | app f x => occ0 f + occ0 x

theorem sbq_no_live (c' : Nat) (hc' : c' ≠ 0) : ∀ e : T, occ2 e = 0 → occ0 (sbq c' e) = 0
  | S, _ => by simp [sbq, occ0]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [sbq, occ0, hc']
    · have h2 : n ≠ 2 := by intro e; subst e; simp [occ2] at h
      simp [sbq, occ0, h0, h2]
  | app f x, h => by
    simp only [occ2] at h
    simp only [sbq, occ0]
    rw [sbq_no_live c' hc' f (by omega), sbq_no_live c' hc' x (by omega)]

theorem sbq_head (c' : Nat) : ∀ s : T, head s = var 0 → head (sbq c' s) = var c'
  | S, h => by simp [head] at h
  | var n, h => by simp [head] at h; subst h; simp [sbq, head]
  | app f x, h => by simp only [sbq, head] at *; exact sbq_head c' f h

/-- the three kinds of replayed handler cannot start a further proper transfer in the Church-chain model:
    the next datum e2[y := p'', p' := c'] either does not contain the live atom at all, or is the bare p'' (whose
    run is stuck at once with the bare y at position 3), or is frozen-headed (stuck at once). -/
theorem trivH_next (c' : Nat) (hc' : c' ≠ 0) (e : T) (h : trivH e) :
    occ0 (sbq c' e) = 0 ∨ sbq c' e = var 0 ∨ ∃ s, sbq c' e = app s (var 0) ∧ head s = var c' := by
  rcases h with h | h | ⟨s, hs, hh⟩
  · left; exact sbq_no_live c' hc' e h
  · right; left; rw [h]; simp [sbq]
  · right; right
    refine ⟨sbq c' s, by rw [hs]; simp [sbq], ?_⟩
    exact sbq_head c' s hh


/-- **The replayed handler is trivial.**  In the next phase of a single-wrapper handler w = b0.c0 (datum w[p:=c].p'),
    every reachable list is still in the barrier phase, or comes after the first c0'-prefixed front, whose opening
    puts e1, e2 right after args(c0') with e2 trivial (y-free, the bare y, or (p'-headed).y).  With
    `reexec_replays_transfer`, e2 is what the re-executed frozen value receives in place of the handler w.y, and
    with `trivH_next` the Church-chain model's next datum e2[y := p'', p' := c'] cannot start a proper transfer. -/
theorem replayed_handler_trivial (b0 c0 : T) (c : Nat) (hc2 : c ≠ 2) (_hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0) :
    ∀ (m : Nat) (L : List T), run m ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) = some L →
      BIv (sb c c0) L ∨ ∃ m1 L1 e1 e2 B', m1 < m ∧
        run m1 ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) = some L1 ∧
        step L1 = some (args (sb c c0) ++ e1 :: e2 :: B') ∧ trivH e2 ∧
        run (m - m1 - 1) (args (sb c c0) ++ e1 :: e2 :: B') = some L := by
  intro m L hm
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hBI : BIv (sb c c0) ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    refine ⟨args (sb c b0) ++ [sb c c0, var 0], rfl, ?_, ?_, ⟨var 0, by simp, by simp [head]⟩⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB (sb c c0) (sb c c0) = true := by simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB (sb c c0) (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  rcases pa_phase_v (sb c c0) _ hBI m L hm with hB | ⟨m1, L1, hlt, hr1, hb1, ⟨f, b, d, R, hL1, hwp⟩, hrest⟩
  · exact Or.inl hB
  · right
    subst hL1
    obtain ⟨e1, e2, B', hs, ht⟩ := x1_handler (sb c c0) f b d R hc0' hwp hb1
    refine ⟨m1, f :: b :: d :: R, e1, e2, B', hlt, hr1, hs, ht, ?_⟩
    have hj : m - m1 = (m - m1 - 1) + 1 := by omega
    rw [hj] at hrest
    simp only [run] at hrest
    rw [hs] at hrest
    simpa using hrest


/-! ##################################################################################################
    R3 agent (2026-10-27): GUARD-FREE replay by pure atom substitution.
    The abstract run of a code g on two fresh 'hole' atoms decides where control goes; both phase 2 and the
    next phase are images of that one abstract run under atom substitutions, so no replay guard is needed.
    ################################################################################################## -/

theorem asub_headS (sg : Nat → T) : ∀ a : T, head a = S → head (asub sg a) = S
  | S, _ => by simp [asub, head]
  | var n, h => by simp [head] at h
  | app f x, h => by
    simp only [asub, head] at h ⊢
    exact asub_headS sg f h

theorem asub_args (sg : Nat → T) : ∀ a : T, head a = S → args (asub sg a) = (args a).map (asub sg)
  | S, _ => by simp [asub, args]
  | var n, h => by simp [head] at h
  | app f x, h => by
    simp only [asub, args, head] at h ⊢
    rw [asub_args sg f h]
    simp

theorem asub_headvar (sg : Nat → T) (n : Nat) : ∀ a : T, head a = var n → head (asub sg a) = head (sg n)
  | S, h => by simp [head] at h
  | var m, h => by simp [head] at h; subst h; simp [asub]
  | app f x, h => by
    simp only [asub, head] at h ⊢
    exact asub_headvar sg n f h

/-- one head step commutes with any atom substitution -/
theorem asub_step (sg : Nat → T) : ∀ (L L' : List T), step L = some L' →
    step (L.map (asub sg)) = some (L'.map (asub sg))
  | a :: b :: d :: R, L', h => by
    simp only [step] at h
    split at h
    · rename_i hS
      injection h with h; subst h
      simp only [List.map_cons, step, asub_headS sg a hS, ite_true, asub_args sg a hS, List.map_append]
      simp [asub]
    · simp at h
  | [], _, h => by simp [step] at h
  | [_], _, h => by simp [step] at h
  | [_, _], _, h => by simp [step] at h

/-- runs commute with any atom substitution (no guard at all) -/
theorem asub_run (sg : Nat → T) : ∀ (k : Nat) (L L' : List T), run k L = some L' →
    run k (L.map (asub sg)) = some (L'.map (asub sg))
  | 0, L, L', h => by simp [run] at h; subst h; simp [run]
  | k + 1, L, L', h => by
    simp only [run] at h ⊢
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      rw [asub_step sg L L1 hs]
      exact asub_run sg k L1 L' h

/-- if a run stops (step fails) at a list, the substituted run stops there too when the front's head is not
    mapped to an S-headed term -/
theorem step_none_len (L : List T) (h : step L = none) (h3 : 3 ≤ L.length) :
    ∃ f L', L = f :: L' ∧ head f ≠ S := by
  match L, h, h3 with
  | a :: b :: d :: R, h, _ =>
    refine ⟨a, b :: d :: R, rfl, ?_⟩
    intro hS; simp [step, hS] at h
  | [], _, h3 => simp at h3
  | [_], _, h3 => simp at h3
  | [_, _], _, h3 => simp at h3

theorem head_cases : ∀ t : T, head t = S ∨ ∃ n, head t = var n
  | S => Or.inl (by simp [head])
  | var n => Or.inr ⟨n, by simp [head]⟩
  | app f _ => by simp only [head]; exact head_cases f

/-- run arithmetic: a run that stops at step k gives none at every later step -/
theorem run_none_after : ∀ (k j : Nat) (L : List T), run k L = none → k ≤ j → run j L = none
  | k, j, L, h, hkj => by
    have := run_add k (j - k) L
    rw [show k + (j - k) = j by omega, h] at this
    simpa using this

/-! ### two hole atoms are two barriers -/

def isHB (h1 h2 : Nat) (t : T) : Bool := decide (head t = var h1) || decide (head t = var h2)

def nHB (h1 h2 : Nat) : List T → Nat
  | [] => 0
  | e :: L => (if isHB h1 h2 e = true then 1 else 0) + nHB h1 h2 L

theorem nHB_append (h1 h2 : Nat) : ∀ A B : List T, nHB h1 h2 (A ++ B) = nHB h1 h2 A + nHB h1 h2 B
  | [], B => by simp [nHB]
  | e :: A, B => by simp [nHB, nHB_append h1 h2 A B]; omega

theorem isHB_app (h1 h2 : Nat) (b d : T) : isHB h1 h2 (app b d) = isHB h1 h2 b := rfl

theorem isHB_S (h1 h2 : Nat) (a : T) (hS : head a = S) : isHB h1 h2 a = false := by
  simp [isHB, hS]

theorem nHB_step (h1 h2 : Nat) (a b d : T) (R : List T) (hS : head a = S) :
    nHB h1 h2 (a :: b :: d :: R) ≤ nHB h1 h2 (args a ++ d :: app b d :: R) := by
  rw [nHB_append]
  have e1 : nHB h1 h2 (a :: b :: d :: R) = (if isHB h1 h2 a = true then 1 else 0) +
      ((if isHB h1 h2 b = true then 1 else 0) + ((if isHB h1 h2 d = true then 1 else 0) + nHB h1 h2 R)) := rfl
  have e2 : nHB h1 h2 (d :: app b d :: R) = (if isHB h1 h2 d = true then 1 else 0) +
      ((if isHB h1 h2 (app b d) = true then 1 else 0) + nHB h1 h2 R) := rfl
  rw [e1, e2, isHB_app, isHB_S h1 h2 a hS]
  simp only [Bool.false_eq_true, ite_false]
  omega

theorem nHB_run (h1 h2 : Nat) : ∀ (k : Nat) (L L' : List T), run k L = some L' → nHB h1 h2 L ≤ nHB h1 h2 L'
  | 0, L, L', h => by simp [run] at h; subst h; exact Nat.le_refl _
  | k + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      have ih := nHB_run h1 h2 k L1 L' h
      match L, hs with
      | a :: b :: d :: R, hs =>
        simp only [step] at hs
        split at hs
        · rename_i hS
          injection hs with hs; subst hs
          exact Nat.le_trans (nHB_step h1 h2 a b d R hS) ih
        · simp at hs
      | [], hs => simp [step] at hs
      | [_], hs => simp [step] at hs
      | [_, _], hs => simp [step] at hs

theorem nHB_le_length (h1 h2 : Nat) : ∀ L : List T, nHB h1 h2 L ≤ L.length
  | [] => by simp [nHB]
  | e :: L => by
    have := nHB_le_length h1 h2 L
    simp only [nHB, List.length_cons]
    split <;> omega

/-- with two barriers, a run can only stop at an atom-headed front -/
theorem nHB_stop (h1 h2 : Nat) (L L' : List T) (k : Nat) (h2le : 2 ≤ nHB h1 h2 L)
    (hr : run k L = some L') (hs : step L' = none) : ∃ f rest, L' = f :: rest ∧ head f ≠ S := by
  have hn := Nat.le_trans h2le (nHB_run h1 h2 k L L' hr)
  match L', hn, hs with
  | [], hn, _ => simp [nHB] at hn
  | f :: rest, hn, hs =>
    refine ⟨f, rest, rfl, ?_⟩
    intro hfS
    have hf : isHB h1 h2 f = false := isHB_S h1 h2 f hfS
    simp [nHB, hf] at hn
    have hl := nHB_le_length h1 h2 rest
    have h3 : 3 ≤ (f :: rest).length := by simp; omega
    obtain ⟨f', L'', he, hne⟩ := step_none_len (f :: rest) hs h3
    injection he with he1 _
    rw [← he1] at hne
    exact hne hfS

/-- the first failing step of a run that eventually fails -/
theorem run_first_none : ∀ (j : Nat) (L : List T), run j L = none →
    ∃ k Lk, k < j ∧ run k L = some Lk ∧ step Lk = none
  | 0, L, h => by simp [run] at h
  | j + 1, L, h => by
    simp only [run] at h
    cases hs : step L with
    | none => exact ⟨0, L, by omega, by simp [run], hs⟩
    | some L1 =>
      rw [hs] at h
      simp only at h
      obtain ⟨k, Lk, hk, hrk, hsk⟩ := run_first_none j L1 h
      refine ⟨k + 1, Lk, by omega, ?_, hsk⟩
      simp only [run, hs]
      exact hrk

/-! ### Theorem PAF: the single-wrapper replay WITHOUT phase-2 hypotheses -/

/-- occurrences of the atom var n -/
def occN (n : Nat) : T → Nat
  | S => 0
  | var m => if m = n then 1 else 0
  | app f x => occN n f + occN n x

theorem occN_args (n : Nat) : ∀ t : T, occN n t = 0 → ∀ s ∈ args t, occN n s = 0
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp only [occN] at h
    simp [args] at hs
    rcases hs with hs | hs
    · exact occN_args n f (by omega) s hs
    · subst hs; omega

/-- the substitution of the guard-free replay: p -> c, h1 -> e1, h2 -> e2, other atoms fixed -/
def sgH (c h1 h2 : Nat) (e1 e2 : T) : Nat → T :=
  fun n => if n = 0 then var c else if n = h1 then e1 else if n = h2 then e2 else var n

theorem asub_sgH_sb (c h1 h2 : Nat) (e1 e2 : T) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) :
    ∀ t : T, occN h1 t = 0 → occN h2 t = 0 → asub (sgH c h1 h2 e1 e2) t = sb c t
  | S, _, _ => by simp [asub, sb]
  | var n, ha, hb => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, sgH]
    · have n1 : n ≠ h1 := by intro e; subst e; simp [occN] at ha
      have n2 : n ≠ h2 := by intro e; subst e; simp [occN] at hb
      simp [asub, sb, sgH, h0, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, sb, asub_sgH_sb c h1 h2 e1 e2 hh1 hh2 f (by omega) (by omega),
      asub_sgH_sb c h1 h2 e1 e2 hh1 hh2 x (by omega) (by omega)]

theorem sgH_head (c h1 h2 : Nat) (e1 e2 : T) (hc : c ≠ 0) (n : Nat) (n1 : n ≠ h1) (n2 : n ≠ h2) :
    head (sgH c h1 h2 e1 e2 n) ≠ var 0 ∧ head (sgH c h1 h2 e1 e2 n) ≠ S := by
  by_cases h0 : n = 0
  · subst h0; simp [sgH, head, hc]
  · simp [sgH, h0, n1, n2, head]

/-- **Post-x1 safety from the abstract outcome of c0.**  If the run of args(c0) ++ [h1, h2] (h1, h2 fresh atoms)
    never reaches a front headed by h1 or h2, then no run from args(c0[p:=c]) ++ [e1, e2, ...] ever reaches a front
    headed by var 0, whatever e1, e2 and the rest are.  No replay guard: both runs are images of one abstract run
    under atom substitutions. -/
theorem paf_post (c0 : T) (c h1 h2 : Nat) (hc : c ≠ 0) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) (h12 : h1 ≠ h2)
    (hgS : head c0 = S) (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0)
    (hNH : ∀ (k : Nat) (f : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (f :: L) →
      head f ≠ var h1 ∧ head f ≠ var h2) :
    ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args (sb c c0) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0 := by
  intro e1 e2 B' j f L hrun hf
  have hA : (args c0 ++ [var h1, var h2]).map (asub (sgH c h1 h2 e1 e2)) ++ B' =
      args (sb c c0) ++ e1 :: e2 :: B' := by
    rw [sb_args c c0 hgS]
    simp only [List.map_append, List.map_cons, List.map_nil]
    have hargs : (args c0).map (asub (sgH c h1 h2 e1 e2)) = (args c0).map (sb c) := by
      apply List.map_congr_left
      intro e he
      exact asub_sgH_sb c h1 h2 e1 e2 hh1 hh2 e (occN_args h1 c0 hf1 e he) (occN_args h2 c0 hf2 e he)
    rw [hargs]
    have hs1 : asub (sgH c h1 h2 e1 e2) (var h1) = e1 := by simp [asub, sgH, hh1]
    have hs2 : asub (sgH c h1 h2 e1 e2) (var h2) = e2 := by
      simp [asub, sgH, hh2, Ne.symm h12]
    rw [hs1, hs2]
    simp
  have hnHB : 2 ≤ nHB h1 h2 (args c0 ++ [var h1, var h2]) := by
    rw [nHB_append]; simp [nHB, isHB, head]
  rw [← hA] at hrun
  cases hj : run j (args c0 ++ [var h1, var h2]) with
  | some Aj =>
    have h1' := run_append j _ _ B' (asub_run (sgH c h1 h2 e1 e2) j _ _ hj)
    rw [hrun] at h1'
    have hlen := Nat.le_trans hnHB (nHB_run h1 h2 j _ Aj hj)
    match Aj, hj, h1', hlen with
    | [], _, _, hlen => simp [nHB] at hlen
    | f0 :: L0, hj, h1', _ =>
      simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h1'
      obtain ⟨hff, _⟩ := h1'
      obtain ⟨hn1, hn2⟩ := hNH j f0 L0 hj
      rcases head_cases f0 with hS | ⟨n, hn⟩
      · have := asub_headS (sgH c h1 h2 e1 e2) f0 hS
        rw [← hff, hf] at this; simp at this
      · have n1 : n ≠ h1 := by intro e; subst e; exact hn1 hn
        have n2 : n ≠ h2 := by intro e; subst e; exact hn2 hn
        have := asub_headvar (sgH c h1 h2 e1 e2) n f0 hn
        rw [← hff, hf] at this
        exact (sgH_head c h1 h2 e1 e2 hc n n1 n2).1 this.symm
  | none =>
    obtain ⟨k, Ak, hk, hrk, hsk⟩ := run_first_none j _ hj
    obtain ⟨f0, rest, hAk, hf0⟩ := nHB_stop h1 h2 _ Ak k hnHB hrk hsk
    subst hAk
    obtain ⟨hn1, hn2⟩ := hNH k f0 rest hrk
    obtain ⟨n, hn⟩ : ∃ n, head f0 = var n := (head_cases f0).resolve_left hf0
    have n1 : n ≠ h1 := by intro e; subst e; exact hn1 hn
    have n2 : n ≠ h2 := by intro e; subst e; exact hn2 hn
    have hck := run_append k _ _ B' (asub_run (sgH c h1 h2 e1 e2) k _ _ hrk)
    have hne : head (asub (sgH c h1 h2 e1 e2) f0) ≠ S := by
      rw [asub_headvar _ n f0 hn]; exact (sgH_head c h1 h2 e1 e2 hc n n1 n2).2
    have hstep : step ((f0 :: rest).map (asub (sgH c h1 h2 e1 e2)) ++ B') = none := by
      simp only [List.map_cons, List.cons_append]
      exact step_head_ne _ _ hne
    have hk1 : run (k + 1) ((args c0 ++ [var h1, var h2]).map (asub (sgH c h1 h2 e1 e2)) ++ B') = none := by
      rw [run_add k 1, hck, Option.bind_some]
      simp only [run]
      rw [hstep]
    have := run_none_after (k + 1) j _ hk1 (by omega)
    rw [hrun] at this; simp at this

/-- **THEOREM PAF (single wrapper, no phase-2 hypothesis).**  Let w = b0.c0 (b0, c0 S-headed and free of y; b0 = S
    allowed) and let the abstract run of c0 on two fresh atoms never call them (F(c0) is not h1/h2).  Then in the
    generic run of the next datum w[p:=c].p' every p'-headed front has a y-free element or the bare y at position 3. -/
theorem paf_main (b0 c0 : T) (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0)
    (hNH : ∀ (k : Nat) (f : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (f :: L) →
      head f ≠ var h1 ∧ head f ≠ var h2) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 :=
  pa_core b0 c0 c hc2 hb0S hc0S hy0 hy1 (paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH)

/-! ### The general correspondence lemma (GCL): two images of one abstract run -/

theorem run_ne_nil : ∀ (k : Nat) (L L' : List T), L ≠ [] → run k L = some L' → L' ≠ []
  | 0, L, L', hL, h => by simp [run] at h; subst h; exact hL
  | k + 1, L, L', hL, h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      apply run_ne_nil k L1 L' _ h
      match L, hs with
      | a :: b :: d :: R, hs =>
        simp only [step] at hs
        split at hs
        · injection hs with hs; subst hs; simp
        · simp at hs
      | [], hs => simp [step] at hs
      | [_], hs => simp [step] at hs
      | [_, _], hs => simp [step] at hs

/-- every front strictly before the end of a successful run is S-headed -/
theorem run_front_S (k j : Nat) (L L' Lj : List T) (h : run k L = some L') (hj : j < k)
    (hLj : run j L = some Lj) : ∃ g rest, Lj = g :: rest ∧ head g = S := by
  obtain ⟨Lj', hLj', hrest⟩ := run_prefix k j L L' h (by omega)
  rw [hLj] at hLj'; injection hLj' with e; subst e
  have hk : k - j = (k - j - 1) + 1 := by omega
  rw [hk] at hrest
  simp only [run] at hrest
  cases hs : step Lj with
  | none => rw [hs] at hrest; simp at hrest
  | some L1 =>
    match Lj, hs with
    | a :: b :: d :: R, hs =>
      refine ⟨a, b :: d :: R, rfl, ?_⟩
      simp only [step] at hs
      split at hs
      · assumption
      · simp at hs
    | [], hs => simp [step] at hs
    | [_], hs => simp [step] at hs
    | [_, _], hs => simp [step] at hs

/-- **GCL.**  One abstract list A, two atom substitutions: s2 (the earlier phase, which later reaches a p-front
    with at least three elements) and s3 (the next phase), with one of the two bottoms empty.  If s3 maps every
    atom to an atom-headed term and maps to a p'-headed term (var 0) only atoms that s2 maps to a term headed by a
    DIFFERENT atom, then the s3-run never reaches a var 0-headed front. -/
theorem gcl (A : List T) (hA0 : A ≠ []) (s2 s3 : Nat → T) (B2r B3r : List T) (hB : B2r = [] ∨ B3r = [])
    (C1 : ∀ n, head (s3 n) ≠ S)
    (C2 : ∀ n, head (s3 n) = var 0 → ∃ m, head (s2 n) = var m ∧ m ≠ 0)
    (L0 : List T) (t T' : Nat) (htT : t ≤ T') (ht : run t L0 = some (A.map (asub s2) ++ B2r))
    (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T), run m (A.map (asub s3) ++ B3r) = some (f' :: L') → head f' ≠ var 0 := by
  intro m f' L' h3 hf'
  -- phase-2 facts at time t + j
  have p2 : ∀ j Aj, run j A = some Aj → run (t + j) L0 = some (Aj.map (asub s2) ++ B2r) := by
    intro j Aj hj
    rw [run_add t j, ht, Option.bind_some]
    exact run_append j _ _ B2r (asub_run s2 j _ _ hj)
  -- if phase 2 is stuck (or short) at time t + j while the abstract run reached step j, then t + j = T'
  have p2stuck : ∀ j Aj, run j A = some Aj → run (t + j + 1) L0 = none →
      t + j = T' ∧ (Aj.map (asub s2) ++ B2r) = f :: b :: d :: R := by
    intro j Aj hj hnone
    have hTle : T' ≤ t + j := by
      apply Nat.le_of_not_lt
      intro hlt
      have := run_none_after (t + j + 1) T' L0 hnone (by omega)
      rw [hT] at this; simp at this
    by_cases hTe : T' = t + j
    · subst hTe; refine ⟨rfl, ?_⟩
      have := p2 j Aj hj; rw [hT] at this; injection this with e; exact e.symm
    · exfalso
      have hlt : T' - t < j := by omega
      obtain ⟨Aj', hAj'⟩ : ∃ Aj', run (T' - t) A = some Aj' := by
        obtain ⟨Lx, hLx, _⟩ := run_prefix j (T' - t) A Aj hj (by omega)
        exact ⟨Lx, hLx⟩
      obtain ⟨g, rest, hg, hgS⟩ := run_front_S j (T' - t) A Aj Aj' hj hlt hAj'
      have h2 := p2 (T' - t) Aj' hAj'
      rw [show t + (T' - t) = T' by omega, hT, hg] at h2
      simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h2
      have := asub_headS s2 g hgS
      rw [← h2.1, hf] at this; simp at this
  cases hm : run m A with
  | some Am =>
    have h3' := run_append m _ _ B3r (asub_run s3 m _ _ hm)
    rw [h3] at h3'
    have hne := run_ne_nil m A Am hA0 hm
    match Am, hm, h3', hne with
    | [], _, _, hne => exact hne rfl
    | f0 :: L0', hm, h3', _ =>
      simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h3'
      obtain ⟨hff, _⟩ := h3'
      rcases head_cases f0 with hS | ⟨n, hn⟩
      · have := asub_headS s3 f0 hS
        rw [← hff, hf'] at this; simp at this
      · have hh := asub_headvar s3 n f0 hn
        rw [← hff, hf'] at hh
        obtain ⟨m', hm', hm0⟩ := C2 n hh.symm
        -- phase 2 is stuck at time t + m with front headed by var m'
        have h2 := p2 m _ hm
        have hstuck : run (t + m + 1) L0 = none := by
          rw [run_add (t + m) 1, h2, Option.bind_some]
          simp only [run, List.map_cons, List.cons_append]
          rw [step_head_ne _ _ (by rw [asub_headvar s2 n f0 hn, hm']; simp)]
        obtain ⟨_, he⟩ := p2stuck m _ hm hstuck
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
        have := asub_headvar s2 n f0 hn
        rw [he.1, hf, hm'] at this
        injection this with e; exact hm0 e.symm
  | none =>
    obtain ⟨k, Ak, hk, hrk, hsk⟩ := run_first_none m _ hm
    have h3k := run_append k _ _ B3r (asub_run s3 k _ _ hrk)
    -- the s3-run must make a step at time k
    have hstep3 : ∃ L1, step (Ak.map (asub s3) ++ B3r) = some L1 := by
      have := run_add k (m - k) (A.map (asub s3) ++ B3r)
      rw [show k + (m - k) = m by omega, h3, h3k, Option.bind_some] at this
      have hmk : m - k = (m - k - 1) + 1 := by omega
      rw [hmk] at this
      simp only [run] at this
      cases hs : step (Ak.map (asub s3) ++ B3r) with
      | none => rw [hs] at this; simp at this
      | some L1 => exact ⟨L1, rfl⟩
    obtain ⟨L1, hL1⟩ := hstep3
    have hne := run_ne_nil k A Ak hA0 hrk
    match Ak, hrk, hsk, hL1, hne, h3k with
    | [], _, _, _, hne, _ => exact hne rfl
    | f0 :: rest, hrk, hsk, hL1, _, h3k =>
      rcases head_cases f0 with hS | ⟨n, hn⟩
      · -- the abstract run is short: one of the two images is exact
        have hshort : rest.length < 2 := by
          apply Nat.lt_of_not_le
          intro hlen
          have h3l : 3 ≤ (f0 :: rest).length := by simp; omega
          obtain ⟨g, _, hg, hgS⟩ := step_none_len (f0 :: rest) hsk h3l
          injection hg with e _; subst e; exact hgS hS
        rcases hB with hB | hB
        · -- phase 2 is exact and short at time t + k
          subst hB
          have h2 := p2 k _ hrk
          have hstuck : run (t + k + 1) L0 = none := by
            rw [run_add (t + k) 1, h2, Option.bind_some]
            simp only [List.append_nil]
            match rest, hshort with
            | [], _ => simp [run, step]
            | [_], _ => simp [run, step]
          obtain ⟨_, he⟩ := p2stuck k _ hrk hstuck
          simp only [List.append_nil] at he
          have := congrArg List.length he
          simp at this; omega
        · subst hB
          simp only [List.append_nil] at hL1
          match rest, hshort, hL1 with
          | [], _, hL1 => simp [step] at hL1
          | [_], _, hL1 => simp [step] at hL1
      · have hne3 : head (asub s3 f0) ≠ S := by rw [asub_headvar s3 n f0 hn]; exact C1 n
        simp only [List.map_cons, List.cons_append] at hL1
        rw [step_head_ne _ _ hne3] at hL1; simp at hL1

/-! ### Theorem IGEN: if the earlier phase ever lays out args(V) on top of its list (before its transfer), the next
    phase (datum V[y:=p', p:=c]) never reaches a p'-headed front at all. -/

/-- the next-phase substitution: p -> c (frozen), y -> p' = var 0 -/
def sg3 (c : Nat) : Nat → T := fun n => if n = 0 then var c else if n = 2 then var 0 else var n

/-- s3 with three hole atoms H, H+1, H+2 sent to the next phase's inputs y, x.y, r -/
def s3H (c H : Nat) : Nat → T := fun n =>
  if n = 0 then var c else if n = 2 then var 0 else if n = H then var 2 else
  if n = H + 1 then app (var 1) (var 2) else if n = H + 2 then var 3 else var n

/-- s2 with three hole atoms sent to the earlier phase's bottom elements -/
def s2H (H : Nat) (u1 u2 u3 : T) : Nat → T := fun n =>
  if n = H then u1 else if n = H + 1 then u2 else if n = H + 2 then u3 else var n

def fresh3 (H : Nat) (t : T) : Prop := occN H t = 0 ∧ occN (H + 1) t = 0 ∧ occN (H + 2) t = 0

theorem fresh3_args (H : Nat) (t : T) (h : fresh3 H t) : ∀ s ∈ args t, fresh3 H s := by
  intro s hs
  exact ⟨occN_args H t h.1 s hs, occN_args (H + 1) t h.2.1 s hs, occN_args (H + 2) t h.2.2 s hs⟩

theorem asub_s3H (c H : Nat) (hH : 4 ≤ H) : ∀ t : T, fresh3 H t → asub (s3H c H) t = asub (sg3 c) t
  | S, _ => by simp [asub]
  | var n, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have n1 : n ≠ H := by intro e; subst e; simp [occN] at h1
    have n2 : n ≠ H + 1 := by intro e; subst e; simp [occN] at h2
    have n3 : n ≠ H + 2 := by intro e; subst e; simp [occN] at h3
    simp [asub, s3H, sg3, n1, n2, n3]
  | app f x, h => by
    obtain ⟨h1, h2, h3⟩ := h
    simp only [occN] at h1 h2 h3
    simp [asub, asub_s3H c H hH f ⟨by omega, by omega, by omega⟩, asub_s3H c H hH x ⟨by omega, by omega, by omega⟩]

theorem asub_s2H (H : Nat) (u1 u2 u3 : T) : ∀ t : T, fresh3 H t → asub (s2H H u1 u2 u3) t = t
  | S, _ => by simp [asub]
  | var n, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have n1 : n ≠ H := by intro e; subst e; simp [occN] at h1
    have n2 : n ≠ H + 1 := by intro e; subst e; simp [occN] at h2
    have n3 : n ≠ H + 2 := by intro e; subst e; simp [occN] at h3
    simp [asub, s2H, n1, n2, n3]
  | app f x, h => by
    obtain ⟨h1, h2, h3⟩ := h
    simp only [occN] at h1 h2 h3
    simp [asub, asub_s2H H u1 u2 u3 f ⟨by omega, by omega, by omega⟩,
      asub_s2H H u1 u2 u3 x ⟨by omega, by omega, by omega⟩]

theorem s3H_C1 (c H : Nat) : ∀ n, head (s3H c H n) ≠ S := by
  intro n
  simp only [s3H]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp [head]

theorem s3H_C2 (c H : Nat) (hc : c ≠ 0) (hH : 4 ≤ H) (u1 u2 u3 : T) :
    ∀ n, head (s3H c H n) = var 0 → ∃ m, head (s2H H u1 u2 u3 n) = var m ∧ m ≠ 0 := by
  intro n hn
  by_cases h0 : n = 0
  · subst h0; simp [s3H, head, hc] at hn
  by_cases h2 : n = 2
  · subst h2
    refine ⟨2, ?_, by omega⟩
    have a1 : (2 : Nat) ≠ H := by omega
    have a2 : (2 : Nat) ≠ H + 1 := by omega
    have a3 : (2 : Nat) ≠ H + 2 := by omega
    have a4 : H ≠ 0 := by omega
    simp [s2H, a1, a2, a3, a4, head]
  exfalso
  simp only [s3H, h0, h2, ite_false] at hn
  split at hn
  · simp [head] at hn
  · split at hn
    · simp [head] at hn
    · split at hn
      · simp [head] at hn
      · simp [head] at hn; exact h0 hn

theorem args_map_s3H (c H : Nat) (hH : 4 ≤ H) (V : T) (hVS : head V = S) (hV : fresh3 H V) :
    (args V).map (asub (s3H c H)) = args (asub (sg3 c) V) := by
  rw [asub_args (sg3 c) V hVS]
  apply List.map_congr_left
  intro e he
  exact asub_s3H c H hH e (fresh3_args H V hV e he)

theorem args_map_s2H (H : Nat) (u1 u2 u3 : T) (V : T) (hV : fresh3 H V) :
    (args V).map (asub (s2H H u1 u2 u3)) = args V := by
  have : (args V).map (asub (s2H H u1 u2 u3)) = (args V).map id := by
    apply List.map_congr_left
    intro e he
    exact asub_s2H H u1 u2 u3 e (fresh3_args H V hV e he)
  simpa using this

theorem s3H_vals (c H : Nat) (hH : 4 ≤ H) :
    s3H c H H = var 2 ∧ s3H c H (H + 1) = app (var 1) (var 2) ∧ s3H c H (H + 2) = var 3 := by
  have a0 : H ≠ 0 := by omega
  have a2 : H ≠ 2 := by omega
  have b0 : H + 1 ≠ 0 := by omega
  have b2 : H + 1 ≠ 2 := by omega
  have b1 : H + 1 ≠ H := by omega
  have c0 : H + 2 ≠ 0 := by omega
  have c2 : H + 2 ≠ 2 := by omega
  have c1 : H + 2 ≠ H := by omega
  have c3 : H + 2 ≠ H + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [s3H, a0, a2, ite_false, ite_true]
  · simp only [s3H, b0, b2, b1, ite_false, ite_true]
  · simp only [s3H, c0, c2, c1, c3, ite_false, ite_true]

theorem s2H_vals (H : Nat) (u1 u2 u3 : T) :
    s2H H u1 u2 u3 H = u1 ∧ s2H H u1 u2 u3 (H + 1) = u2 ∧ s2H H u1 u2 u3 (H + 2) = u3 := by
  have b1 : H + 1 ≠ H := by omega
  have c1 : H + 2 ≠ H := by omega
  have c3 : H + 2 ≠ H + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [s2H, ite_true]
  · simp only [s2H, b1, ite_false, ite_true]
  · simp only [s2H, c1, c3, ite_false, ite_true]

/-- **THEOREM IGEN.**  Let V be S-headed (the transferred handler) and let a run from L0 (the earlier phase) reach
    a list args(V) ++ B2 at time t and, at a time T' >= t, a list with >= 3 elements whose front is p-headed.  Then
    the run of the next datum V[y:=p', p:=c] never reaches a p'-headed front. -/
theorem igen_main (V : T) (c H : Nat) (hc : c ≠ 0) (hH : 4 ≤ H) (hVS : head V = S) (hVa : args V ≠ []) (hV : fresh3 H V)
    (L0 : List T) (t T' : Nat) (B2 : List T) (htT : t ≤ T') (ht : run t L0 = some (args V ++ B2))
    (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T),
      run m [asub (sg3 c) V, var 1, var 2, var 3] = some (f' :: L') → head f' ≠ var 0 := by
  intro m f' L' h3
  have hD3S : head (asub (sg3 c) V) = S := asub_headS (sg3 c) V hVS
  match m, h3 with
  | 0, h3 =>
    simp [run] at h3; rw [← h3.1, hD3S]; simp
  | m' + 1, h3 =>
    have hs1 : step [asub (sg3 c) V, var 1, var 2, var 3] =
        some (args (asub (sg3 c) V) ++ [var 2, app (var 1) (var 2), var 3]) := by
      simp [step, hD3S]
    simp only [run] at h3
    rw [hs1] at h3
    simp only at h3
    match B2, ht with
    | [], ht =>
      have hA0 : args V ≠ [] := hVa
      apply gcl (args V) hA0 (s2H H S S S) (s3H c H) [] [var 2, app (var 1) (var 2), var 3] (Or.inl rfl)
        (s3H_C1 c H) (s3H_C2 c H hc hH S S S) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [args_map_s2H H S S S V hV]; exact ht
      · rw [args_map_s3H c H hH V hVS hV]; exact h3
    | [u1], ht =>
      apply gcl (args V ++ [var H]) (by simp) (s2H H u1 S S) (s3H c H) [] [app (var 1) (var 2), var 3]
        (Or.inl rfl) (s3H_C1 c H) (s3H_C2 c H hc hH u1 S S) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [List.map_append, args_map_s2H H u1 S S V hV]; simpa [asub, (s2H_vals H _ _ _).1, (s2H_vals H _ _ _).2.1, (s2H_vals H _ _ _).2.2] using ht
      · rw [List.map_append, args_map_s3H c H hH V hVS hV]
        have e1 : asub (s3H c H) (var H) = var 2 := by simp only [asub]; exact (s3H_vals c H hH).1
        rw [List.map_cons, List.map_nil, e1]; simpa using h3
    | [u1, u2], ht =>
      apply gcl (args V ++ [var H, var (H + 1)]) (by simp) (s2H H u1 u2 S) (s3H c H) [] [var 3]
        (Or.inl rfl) (s3H_C1 c H) (s3H_C2 c H hc hH u1 u2 S) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [List.map_append, args_map_s2H H u1 u2 S V hV]; simpa [asub, (s2H_vals H _ _ _).1, (s2H_vals H _ _ _).2.1, (s2H_vals H _ _ _).2.2] using ht
      · rw [List.map_append, args_map_s3H c H hH V hVS hV]
        have e1 : asub (s3H c H) (var H) = var 2 := by simp only [asub]; exact (s3H_vals c H hH).1
        have e2 : asub (s3H c H) (var (H + 1)) = app (var 1) (var 2) := by
          simp only [asub]; exact (s3H_vals c H hH).2.1
        rw [List.map_cons, List.map_cons, List.map_nil, e1, e2]; simpa using h3
    | u1 :: u2 :: u3 :: B2', ht =>
      apply gcl (args V ++ [var H, var (H + 1), var (H + 2)]) (by simp) (s2H H u1 u2 u3) (s3H c H) B2' []
        (Or.inr rfl) (s3H_C1 c H) (s3H_C2 c H hc hH u1 u2 u3) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [List.map_append, args_map_s2H H u1 u2 u3 V hV]; simpa [asub, (s2H_vals H _ _ _).1, (s2H_vals H _ _ _).2.1, (s2H_vals H _ _ _).2.2] using ht
      · rw [List.map_append, args_map_s3H c H hH V hVS hV]
        have e1 : asub (s3H c H) (var H) = var 2 := by simp only [asub]; exact (s3H_vals c H hH).1
        have e2 : asub (s3H c H) (var (H + 1)) = app (var 1) (var 2) := by
          simp only [asub]; exact (s3H_vals c H hH).2.1
        have e3 : asub (s3H c H) (var (H + 2)) = var 3 := by simp only [asub]; exact (s3H_vals c H hH).2.2
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, e1, e2, e3]; simpa using h3

/-! ### Theorem ALPHA: single-wrapper pattern alpha needs NO hypothesis beyond the glue step itself -/

theorem asub_args_var (sg : Nat → T) (n : Nat) (hS : head (sg n) = S) :
    ∀ f : T, head f = var n → args (asub sg f) = args (sg n) ++ (args f).map (asub sg)
  | S, h => by simp [head] at h
  | var m, h => by simp [head] at h; subst h; simp [asub, args]
  | app g x, h => by
    simp only [head] at h
    simp only [asub, args]
    rw [asub_args_var sg n hS g h]
    simp

theorem asub_sg3_sb (c : Nat) : ∀ t : T, occ2 t = 0 → asub (sg3 c) t = sb c t
  | S, _ => by simp [asub, sb]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, sg3]
    · have h2 : n ≠ 2 := by intro e; subst e; simp [occ2] at h
      simp [asub, sb, sg3, h0, h2]
  | app f x, h => by
    simp only [occ2] at h
    simp [asub, sb, asub_sg3_sb c f (by omega), asub_sg3_sb c x (by omega)]

/-- an image of an abstract run that is stuck (atom front, not p) or short before the time T' of a p-front list
    is impossible -/
theorem image_stuck (A : List T) (s2 : Nat → T) (B : List T) (L0 : List T) (t T' : Nat) (htT : t ≤ T')
    (ht : run t L0 = some (A.map (asub s2) ++ B)) (f b d : T) (R : List T)
    (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0)
    (j : Nat) (Aj : List T) (hj : run j A = some Aj) :
    (run (t + j + 1) L0 = none → (Aj.map (asub s2) ++ B) = f :: b :: d :: R ∧ t + j = T') ∧
    (T' < t + j → False) := by
  have p2 : ∀ i Ai, run i A = some Ai → run (t + i) L0 = some (Ai.map (asub s2) ++ B) := by
    intro i Ai hi
    rw [run_add t i, ht, Option.bind_some]
    exact run_append i _ _ B (asub_run s2 i _ _ hi)
  have early : T' < t + j → False := by
    intro hlt
    obtain ⟨Ai, hAi, _⟩ := run_prefix j (T' - t) A Aj hj (by omega)
    obtain ⟨g, rest, hg, hgS⟩ := run_front_S j (T' - t) A Aj Ai hj (by omega) hAi
    have h2 := p2 (T' - t) Ai hAi
    rw [show t + (T' - t) = T' by omega, hT, hg] at h2
    simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h2
    have := asub_headS s2 g hgS
    rw [← h2.1, hf] at this; simp at this
  refine ⟨?_, early⟩
  intro hnone
  have hTle : T' ≤ t + j := by
    apply Nat.le_of_not_lt
    intro hlt
    have := run_none_after (t + j + 1) T' L0 hnone (by omega)
    rw [hT] at this; simp at this
  have hTe : T' = t + j := by
    apply Nat.le_antisymm hTle
    apply Nat.le_of_not_lt
    intro hlt; exact early hlt
  subst hTe
  have := p2 j Aj hj; rw [hT] at this; injection this with e
  exact ⟨e.symm, rfl⟩

/-- the hole substitution of pattern alpha: h1 -> y, h2 -> w.y -/
def sgA (h1 h2 : Nat) (wy : T) : Nat → T := fun n => if n = h1 then var 2 else if n = h2 then wy else var n

theorem asub_sgA_id (h1 h2 : Nat) (wy : T) : ∀ t : T, occN h1 t = 0 → occN h2 t = 0 → asub (sgA h1 h2 wy) t = t
  | S, _, _ => by simp [asub]
  | var n, ha, hb => by
    have n1 : n ≠ h1 := by intro e; subst e; simp [occN] at ha
    have n2 : n ≠ h2 := by intro e; subst e; simp [occN] at hb
    simp [asub, sgA, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, asub_sgA_id h1 h2 wy f (by omega) (by omega), asub_sgA_id h1 h2 wy x (by omega) (by omega)]

/-- **THEOREM ALPHA (pattern alpha, no replay hypothesis).**  Let the earlier phase (any run from L0) pass through
    the glue list [c0, w, y] ++ R0 with w = b0.c0 (b0, c0 S-headed, y-free) at time t and reach a p-front list with
    >= 3 elements at a later time T'.  Then the next phase of the handler w.y never makes a proper transfer: every
    p'-headed front has a y-free element or the bare y at position 3.  (Either c0's abstract run never calls its two
    arguments - Theorem PAF - or the earlier phase re-opens a copy of w.y - Theorem IGEN.) -/
theorem alpha_main (b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (L0 : List T) (t T' : Nat) (R0 : List T) (hglue : run t L0 = some (c0 :: app b0 c0 :: var 2 :: R0))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  rcases Classical.em (∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g ≠ var h1 ∧ head g ≠ var h2) with hNH | hNH
  · exact paf_main b0 c0 c h1 h2 hc hc2 hh1 hh2 h12 hb0S hc0S hy0 hy1 hf1 hf2 hNH
  · -- some abstract front of c0's run is h1- or h2-headed
    have hex : ∃ k g L, run k (args c0 ++ [var h1, var h2]) = some (g :: L) ∧
        (head g = var h1 ∨ head g = var h2) := by
      apply Classical.byContradiction
      intro hno
      apply hNH
      intro k g L hk
      constructor
      · intro e; exact hno ⟨k, g, L, hk, Or.inl e⟩
      · intro e; exact hno ⟨k, g, L, hk, Or.inr e⟩
    obtain ⟨k, g, Lk, hk, hg⟩ := hex
    have hwyS : head (app (app b0 c0) (var 2)) = S := by simp [head, hb0S]
    have hs2_1 : sgA h1 h2 (app (app b0 c0) (var 2)) h1 = var 2 := by simp [sgA]
    have hs2_2 : sgA h1 h2 (app (app b0 c0) (var 2)) h2 = app (app b0 c0) (var 2) := by
      simp [sgA, Ne.symm h12]
    -- the earlier phase one step after the glue is the s2-image of the abstract list
    have hA2 : (args c0 ++ [var h1, var h2]).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0 =
        args c0 ++ var 2 :: app (app b0 c0) (var 2) :: R0 := by
      have hargs : (args c0).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) = args c0 := by
        have : (args c0).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) = (args c0).map id := by
          apply List.map_congr_left
          intro e he
          exact asub_sgA_id h1 h2 _ e (occN_args h1 c0 hf1 e he) (occN_args h2 c0 hf2 e he)
        simpa using this
      simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs2_1, hs2_2]
      simp
    have ht1 : run (t + 1) L0 = some ((args c0 ++ [var h1, var h2]).map
        (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) := by
      rw [hA2, run_add t 1, hglue, Option.bind_some]
      simp [run, step, hc0S]
    obtain ⟨hstuckE, hearly⟩ := image_stuck _ _ R0 L0 (t + 1) T' (by omega) ht1 f b d R hT hf k (g :: Lk) hk
    have p2k : run (t + 1 + k) L0 =
        some ((g :: Lk).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) := by
      rw [run_add (t + 1) k, ht1, Option.bind_some]
      exact run_append k _ _ R0 (asub_run _ k _ _ hk)
    rcases hg with hg | hg
    · -- an h1-front would be a y-front of the earlier phase: impossible
      exfalso
      have hy : head (asub (sgA h1 h2 (app (app b0 c0) (var 2))) g) = var 2 := by
        rw [asub_headvar _ h1 g hg, hs2_1]; simp [head]
      have hnone : run (t + 1 + k + 1) L0 = none := by
        rw [run_add (t + 1 + k) 1, p2k, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ (by rw [hy]; simp)]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      rw [← he.1, hy] at hf; injection hf with e; omega
    · -- an h2-front: the earlier phase opens a copy of w.y, i.e. lays out args(w.y): Theorem IGEN
      have hGS : head (asub (sgA h1 h2 (app (app b0 c0) (var 2))) g) = S := by
        rw [asub_headvar _ h2 g hg, hs2_2]; exact hwyS
      -- the earlier phase makes a step at time t + 1 + k
      have hTgt : t + 1 + k < T' := by
        apply Nat.lt_of_not_le
        intro hle
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact hearly (by omega)
        · subst heq
          rw [p2k] at hT
          simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at hT
          rw [← hT.1, hGS] at hf; simp at hf
      obtain ⟨Ln, hLn, _⟩ := run_prefix T' (t + 1 + k + 1) L0 _ hT (by omega)
      have hstep : step ((g :: Lk).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) = some Ln := by
        rw [run_add (t + 1 + k) 1, p2k, Option.bind_some] at hLn
        simp only [run] at hLn
        cases hs : step ((g :: Lk).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) with
        | none => rw [hs] at hLn; simp at hLn
        | some L1 => rw [hs] at hLn; simpa using hLn
      -- Ln starts with args(w.y)
      have hargsG := asub_args_var (sgA h1 h2 (app (app b0 c0) (var 2))) h2 (by rw [hs2_2]; exact hwyS) g hg
      rw [hs2_2] at hargsG
      have hLn_form : ∃ B2, Ln = args (app (app b0 c0) (var 2)) ++ B2 := by
        simp only [List.map_cons, List.cons_append] at hstep
        match hrest : Lk.map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0, hstep with
        | b2 :: d2 :: R2, hstep =>
          simp only [step, hGS, ite_true, Option.some.injEq] at hstep
          rw [hargsG] at hstep
          exact ⟨List.map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) (args g) ++ d2 :: app b2 d2 :: R2,
            by rw [← hstep, List.append_assoc]⟩
        | [], hstep => simp [step] at hstep
        | [_], hstep => simp [step] at hstep
      obtain ⟨B2, hB2⟩ := hLn_form
      rw [hB2] at hLn
      have hVa : args (app (app b0 c0) (var 2)) ≠ [] := by simp [args]
      have hno := igen_main (app (app b0 c0) (var 2)) c H hc hH hwyS hVa hV L0 (t + 1 + k + 1) T' B2
        (by omega) hLn f b d R hT hf
      have hD3 : asub (sg3 c) (app (app b0 c0) (var 2)) = app (app (sb c b0) (sb c c0)) (var 0) := by
        simp [asub, asub_sg3_sb c b0 hy0, asub_sg3_sb c c0 hy1, sg3]
      intro m f' b' d' R' hm hf'
      rw [← hD3] at hm
      exact absurd hf' (hno m f' _ hm)

/-! ### Handler-only variants: PAX (the next phase never opens c0') and PAMF (multi-wrapper with F(c0) not h1/h2) -/

/-- **THEOREM PAX.**  Single wrapper w = b0.c0: if the next phase never reaches a c0'-prefixed front, every
    p'-headed front has a y-free element or the bare y at position 3. -/
theorem pax_main (b0 c0 : T) (c : Nat) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hnx1 : ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      ¬ wpre (sb c c0) f) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hstep0 : step [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] =
      some ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    simp [step, head, hb0', args, BOT]
  have hBI : BI (sb c c0) ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    refine ⟨args (sb c b0) ++ [sb c c0, var 0], rfl, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB (sb c c0) (sb c c0) = true := by
        simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB (sb c c0) (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  match m, hm with
  | 0, hm =>
    simp [run] at hm
    obtain ⟨hf0, _⟩ := hm
    rw [← hf0] at hf; simp [head, hb0'] at hf
  | m' + 1, hm =>
    have hm' := hm
    simp only [run] at hm
    rw [hstep0] at hm
    simp only at hm
    rcases pa_phase (sb c c0) _ hBI m' _ hm with hB | ⟨m1, L1, hlt, hr1, ⟨f1, b1, d1, R1, hL1, hwp⟩, _⟩
    · exact bi_x2 (sb c c0) f b d R hB
    · exfalso
      have : run (m1 + 1) [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some L1 := by
        simp only [run]; rw [hstep0]; exact hr1
      rw [hL1] at this
      exact hnx1 (m1 + 1) f1 b1 d1 R1 this hwp

/-- the generalised core with a bare-S innermost code: from [c0', p'] ++ B no p'-front, whatever B is -/
theorem core_bareS (c0' : T) (B : List T) (hc0' : head c0' = S)
    (hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args c0' ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0) :
    ∀ (m : Nat) (f : T) (L : List T), run m ([c0', var 0] ++ B) = some (f :: L) → head f ≠ var 0 := by
  intro m f L hm
  match m, hm with
  | 0, hm =>
    simp [run] at hm; rw [← hm.1, hc0']; simp
  | m' + 1, hm =>
    match B, hm with
    | [], hm => simp [run, step] at hm
    | e :: B', hm =>
      simp only [List.cons_append, List.nil_append, run] at hm
      have hs : step (c0' :: var 0 :: e :: B') = some (args c0' ++ e :: app (var 0) e :: B') := by
        simp [step, hc0']
      rw [hs] at hm
      simp only at hm
      exact hpost e (app (var 0) e) B' m' f L hm

/-- **THEOREM PAMF.**  Theorem PAM with the replay hypothesis replaced by the handler-only condition 'the abstract
    run of args(c0) ++ [h1, h2] never calls h1 / h2' (paf_post), and the bottom condition replaced by
    'B0ok or b0 = S'.  Multi-wrapper handlers, innermost level vn = b0.c0. -/
theorem pamf_main (b0 c0 : T) (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0)
    (hNH : ∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g ≠ var h1 ∧ head g ≠ var h2)
    (L0 : List T) (h0 : ∀ e ∈ L0, guarded (app (app (sb c b0) (sb c c0)) (var 0)) e)
    (hB0 : b0 = S ∨ ∀ (m1 : Nat) (L1 L2 : List T), run m1 L0 = some L1 →
      (∀ e ∈ L1, guarded (app (app (sb c b0) (sb c c0)) (var 0)) e) →
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre (app (app (sb c b0) (sb c c0)) (var 0)) f) →
      step L1 = some L2 → ∀ B, L2 = args (sb c b0) ++ [sb c c0, var 0] ++ B → B0ok B) :
    ∀ (m : Nat) (f b d : T) (R : List T), run m L0 = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hLnS : head (app (app (sb c b0) (sb c c0)) (var 0)) = S := by simp [head, hb0']
  have hpost := paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH
  rcases guarded_phase _ hLnS L0 h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exfalso
    have := guarded_head _ (by rw [hLnS]; simp) f (hG f (by simp))
    exact this hf
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    obtain ⟨us, hus⟩ := args_wpre _ hLnS f1 hwp
    have hf1S : head f1 = S := by rw [wpre_headeq _ f1 hwp]; exact hLnS
    have hs2' : step L1 = some (args (sb c b0) ++ [sb c c0, var 0] ++ (us ++ d1 :: app b1 d1 :: R1)) := by
      rw [hL1]; simp [step, hf1S, hus, args]
    rw [hs2'] at hs2
    injection hs2 with hs2
    subst hs2
    rcases hB0 with hbS | hB0
    · exfalso
      subst hbS
      have hnil : args (sb c S) = [] := by simp [sb, args]
      rw [hnil, List.nil_append] at hrest
      exact core_bareS (sb c c0) _ hc0' hpost (m - m1 - 1) f (b :: d :: R) hrest hf
    · have hBok := hB0 m1 L1 _ hr1 hg1 ⟨f1, b1, d1, R1, hL1, hwp⟩ hs2' _ rfl
      exact pa_core_g (sb c b0) (sb c c0) _ hBok hc0' hy0' hy1' hpost (m - m1 - 1) f b d R hrest hf

/-! ### Counterexample to Conjecture R3 as stated for ALL ordered data (two occurrences of p).
    D = S(Sp)(S(S(S(SS)(SS)p))) (p = var 0, x = var 1, y = var 2, r = var 3, c = var 4 frozen).
    Phase 2 transfers w.y with w = S(S(S(SS)(SS)p)) after 2 steps; the next datum w[p:=c].p' (p' = var 0 again)
    reaches after 7 steps a p'-front with the proper y-comb (c.(SSc)).(p'.y) at position 3. -/

def cxS : T := S
def cxP : T := var 0
def cxW : T := app S (app S (app (app (app S (app S S)) (app S S)) cxP))
def cxD : T := app (app S (app S cxP)) cxW

theorem r3_cx_phase2 :
    run 2 [cxD, var 1, var 2, var 3] =
      some [var 0, var 2, app cxW (var 2), app (var 1) (var 2), var 3] := by
  rfl

/-- the next datum: w[p := c].p' with c = var 4 -/
def cxW' : T := app S (app S (app (app (app S (app S S)) (app S S)) (var 4)))
def cxD3 : T := app cxW' (var 0)

theorem r3_cx_next : asub (sg3 4) (app cxW (var 2)) = cxD3 := by rfl

theorem r3_cx_phase3 :
    run 7 [cxD3, var 1, var 2, var 3] =
      some [app (var 0) (var 2), app (var 4) (app (var 0) (var 2)),
            app (app (var 4) (app (app S S) (var 4))) (app (var 0) (var 2)),
            app (var 2) (app (var 0) (var 2)), app (var 1) (var 2), var 3] := by
  rfl

/-- copies of INNER.lean's `closed` / `ordered` (renamed): cxD satisfies the hypotheses of ordered_innermost -/
def iclosed : T → Prop
  | S => True
  | var n => 4 ≤ n
  | app f x => iclosed f ∧ iclosed x

def iordered : T → Prop
  | app f x => (head f = S → (iclosed x → iclosed f)) ∧ iordered f ∧ iordered x
  | _ => True

theorem r3_cx_ordered : iordered cxD ∧ head cxD = S ∧ occ2 cxD = 0 := by
  simp [iordered, iclosed, cxD, cxW, cxP, head, occ2]

/-! ### LN0: if the next phase never opens a copy of its innermost level, it has no p'-front at all -/

theorem ln0_main (Ln : T) (hLnS : head Ln = S) (L0 : List T) (h0 : ∀ e ∈ L0, guarded Ln e)
    (hno : ∀ (m : Nat) (f : T) (L : List T), run m L0 = some (f :: L) → ¬ wpre Ln f) :
    ∀ (m : Nat) (f : T) (L : List T), run m L0 = some (f :: L) → head f ≠ var 0 := by
  intro m f L hm hf
  rcases guarded_phase Ln hLnS L0 h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exact guarded_head Ln (by rw [hLnS]; simp) f (hG f (by simp)) hf
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    rw [hL1] at hr1
    exact hno m1 f1 _ hr1 hwp

/-! ### Theorem BETA0: pattern beta reduced to 'phase 2 runs c0 on (w, y)' plus a residual condition on c0 alone -/

/-- the hole substitution of BETA0: h1 -> w, h2 -> y -/
def sgB (h1 h2 : Nat) (w : T) : Nat → T := fun n => if n = h1 then w else if n = h2 then var 2 else var n

theorem asub_sgB_id (h1 h2 : Nat) (w : T) : ∀ t : T, occN h1 t = 0 → occN h2 t = 0 → asub (sgB h1 h2 w) t = t
  | S, _, _ => by simp [asub]
  | var n, ha, hb => by
    have n1 : n ≠ h1 := by intro e; subst e; simp [occN] at ha
    have n2 : n ≠ h2 := by intro e; subst e; simp [occN] at hb
    simp [asub, sgB, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, asub_sgB_id h1 h2 w f (by omega) (by omega), asub_sgB_id h1 h2 w x (by omega) (by omega)]

/-- **THEOREM BETA0.**  Single wrapper w = b0.c0.  Let the earlier phase (any run from L0) run c0 on the holes
    (w, y), i.e. reach args(c0) ++ [w, y] ++ B2 at time t, and reach a p-front list with >= 3 elements at T' > t.
    Assume the residual condition H1ok on c0 alone: whenever the abstract run of args(c0) ++ [h1, h2] reaches an
    h1-headed front, that front is h1.h2.(...) or the bare h1 with h2 at position 3.  Then the next phase of w.y never
    makes a proper transfer.  (Cases: c0 never calls its holes - PAF; it calls h2 - a y-front of the earlier phase,
    impossible; it calls h1 - the earlier phase opens w with y as first argument, i.e. lays out args(w.y) - IGEN.) -/
theorem beta_main (b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (L0 : List T) (t T' : Nat) (B2 : List T)
    (hc0w : run t L0 = some (args c0 ++ app b0 c0 :: var 2 :: B2))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0)
    (hH1 : ∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R')) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  rcases Classical.em (∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g ≠ var h1 ∧ head g ≠ var h2) with hNH | hNH
  · exact paf_main b0 c0 c h1 h2 hc hc2 hh1 hh2 h12 hb0S hc0S hy0 hy1 hf1 hf2 hNH
  · have hex : ∃ k g L, run k (args c0 ++ [var h1, var h2]) = some (g :: L) ∧
        (head g = var h1 ∨ head g = var h2) := by
      apply Classical.byContradiction
      intro hno
      apply hNH
      intro k g L hk
      constructor
      · intro e; exact hno ⟨k, g, L, hk, Or.inl e⟩
      · intro e; exact hno ⟨k, g, L, hk, Or.inr e⟩
    obtain ⟨k, g, Lk, hk, hg⟩ := hex
    have hwS : head (app b0 c0) = S := by simp [head, hb0S]
    have hwyS : head (app (app b0 c0) (var 2)) = S := by simp [head, hb0S]
    have hs1 : sgB h1 h2 (app b0 c0) h1 = app b0 c0 := by simp [sgB]
    have hs2 : sgB h1 h2 (app b0 c0) h2 = var 2 := by simp [sgB, Ne.symm h12]
    have hA2 : (args c0 ++ [var h1, var h2]).map (asub (sgB h1 h2 (app b0 c0))) ++ B2 =
        args c0 ++ app b0 c0 :: var 2 :: B2 := by
      have hargs : (args c0).map (asub (sgB h1 h2 (app b0 c0))) = args c0 := by
        have : (args c0).map (asub (sgB h1 h2 (app b0 c0))) = (args c0).map id := by
          apply List.map_congr_left
          intro e he
          exact asub_sgB_id h1 h2 _ e (occN_args h1 c0 hf1 e he) (occN_args h2 c0 hf2 e he)
        simpa using this
      simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs1, hs2]
      simp
    have ht' : run t L0 = some ((args c0 ++ [var h1, var h2]).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) := by
      rw [hA2]; exact hc0w
    obtain ⟨hstuckE, hearly⟩ := image_stuck _ _ B2 L0 t T' (by omega) ht' f b d R hT hf k (g :: Lk) hk
    have p2k : run (t + k) L0 = some ((g :: Lk).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) := by
      rw [run_add t k, ht', Option.bind_some]
      exact run_append k _ _ B2 (asub_run _ k _ _ hk)
    rcases hg with hg | hg
    · -- h1-front: the earlier phase opens w; by H1ok its first argument is y: IGEN
      have hGS : head (asub (sgB h1 h2 (app b0 c0)) g) = S := by
        rw [asub_headvar _ h1 g hg, hs1]; exact hwS
      have hTgt : t + k < T' := by
        apply Nat.lt_of_not_le
        intro hle
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact hearly (by omega)
        · subst heq
          rw [p2k] at hT
          simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at hT
          rw [← hT.1, hGS] at hf; simp at hf
      obtain ⟨Ln, hLn, _⟩ := run_prefix T' (t + k + 1) L0 _ hT (by omega)
      have hstep : step ((g :: Lk).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) = some Ln := by
        rw [run_add (t + k) 1, p2k, Option.bind_some] at hLn
        simp only [run] at hLn
        cases hs : step ((g :: Lk).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) with
        | none => rw [hs] at hLn; simp at hLn
        | some L1 => rw [hs] at hLn; simpa using hLn
      have hargsG := asub_args_var (sgB h1 h2 (app b0 c0)) h1 (by rw [hs1]; exact hwS) g hg
      rw [hs1] at hargsG
      have hLn_form : ∃ B3, Ln = args (app (app b0 c0) (var 2)) ++ B3 := by
        have hwy_args : args (app (app b0 c0) (var 2)) = args (app b0 c0) ++ [var 2] := by simp [args]
        rcases hH1 k g Lk hk hg with hfirst | ⟨hnil, b'', R'', hL⟩
        · -- the front is w.y.(...)
          match hag : args g, hfirst with
          | u :: us, hfirst =>
            simp only [List.head?, Option.some.injEq] at hfirst
            subst hfirst
            rw [hag] at hargsG
            simp only [List.map_cons, List.cons_append] at hstep
            match hrest : Lk.map (asub (sgB h1 h2 (app b0 c0))) ++ B2, hstep with
            | b2 :: d2 :: R2, hstep =>
              simp only [step, hGS, ite_true, Option.some.injEq] at hstep
              rw [hargsG] at hstep
              refine ⟨List.map (asub (sgB h1 h2 (app b0 c0))) us ++ d2 :: app b2 d2 :: R2, ?_⟩
              rw [← hstep, hwy_args]
              simp [asub, hs2]
            | [], hstep => simp [step] at hstep
            | [_], hstep => simp [step] at hstep
        · -- the front is the bare h1 (so its image is w) with h2 (image y) at position 3
          subst hL
          rw [hnil] at hargsG
          simp only [List.map_cons, List.cons_append, List.map_nil] at hstep
          simp only [step, hGS, ite_true, Option.some.injEq] at hstep
          rw [hargsG] at hstep
          refine ⟨app (asub (sgB h1 h2 (app b0 c0)) b'') (var 2) ::
            (List.map (asub (sgB h1 h2 (app b0 c0))) R'' ++ B2), ?_⟩
          rw [← hstep, hwy_args]
          simp [asub, hs2]
      obtain ⟨B3, hB3⟩ := hLn_form
      rw [hB3] at hLn
      have hVa : args (app (app b0 c0) (var 2)) ≠ [] := by simp [args]
      have hno := igen_main (app (app b0 c0) (var 2)) c H hc hH hwyS hVa hV L0 (t + k + 1) T' B3
        (by omega) hLn f b d R hT hf
      have hD3 : asub (sg3 c) (app (app b0 c0) (var 2)) = app (app (sb c b0) (sb c c0)) (var 0) := by
        simp [asub, asub_sg3_sb c b0 hy0, asub_sg3_sb c c0 hy1, sg3]
      intro m f' b' d' R' hm hf'
      rw [← hD3] at hm
      exact absurd hf' (hno m f' _ hm)
    · -- h2-front: a y-front of the earlier phase, impossible
      exfalso
      have hy : head (asub (sgB h1 h2 (app b0 c0)) g) = var 2 := by
        rw [asub_headvar _ h2 g hg, hs2]; simp [head]
      have hnone : run (t + k + 1) L0 = none := by
        rw [run_add (t + k) 1, p2k, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ (by rw [hy]; simp)]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      rw [← he.1, hy] at hf; injection hf with e; omega

/-! ### Theorem PBT: pattern beta with c0 = S.a1 needs no hypothesis beyond its own glue (H1ok is automatic) -/

/-- h1 occurs only inside copies of h1.h2 -/
def gH (h1 h2 : Nat) : T → Prop
  | S => True
  | var n => n ≠ h1
  | app f x => (f = var h1 ∧ x = var h2) ∨ (gH h1 h2 f ∧ gH h1 h2 x)

theorem gH_headS_args (h1 h2 : Nat) : ∀ t : T, gH h1 h2 t → head t = S → ∀ s ∈ args t, gH h1 h2 s
  | S, _, _, s, hs => by simp [args] at hs
  | var _, _, hh, _, _ => by simp [head] at hh
  | app f x, h, hh, s, hs => by
    rcases h with ⟨hf, _⟩ | ⟨hf, hx⟩
    · subst hf; simp [head] at hh
    · simp [args] at hs
      rcases hs with hs | hs
      · exact gH_headS_args h1 h2 f hf (by simpa [head] using hh) s hs
      · subst hs; exact hx

theorem gH_h1head (h1 h2 : Nat) : ∀ t : T, gH h1 h2 t → head t = var h1 → (args t).head? = some (var h2)
  | S, _, hh => by simp [head] at hh
  | var n, h, hh => by simp [head] at hh; subst hh; simp [gH] at h
  | app f x, h, hh => by
    rcases h with ⟨hf, hx⟩ | ⟨hf, _⟩
    · subst hf; subst hx; simp [args]
    · have := gH_h1head h1 h2 f hf (by simpa [head] using hh)
      simp only [args]
      cases hfa : args f with
      | nil => rw [hfa] at this; simp at this
      | cons u us => rw [hfa] at this; simpa using this

theorem gH_run (h1 h2 : Nat) : ∀ (k : Nat) (L L' : List T), (∀ e ∈ L, gH h1 h2 e) → run k L = some L' →
    ∀ e ∈ L', gH h1 h2 e
  | 0, L, L', h0, h => by simp [run] at h; subst h; exact h0
  | k + 1, L, L', h0, h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      apply gH_run h1 h2 k L1 L' _ h
      match L, hs, h0 with
      | a :: b :: d :: R, hs, h0 =>
        simp only [step] at hs
        split at hs
        · rename_i haS
          injection hs with hs; subst hs
          intro e he; simp at he
          rcases he with he | he | he | he
          · exact gH_headS_args h1 h2 a (h0 a (by simp)) haS e he
          · rw [he]; exact h0 d (by simp)
          · rw [he]; exact Or.inr ⟨h0 b (by simp), h0 d (by simp)⟩
          · exact h0 e (by simp [he])
        · simp at hs
      | [], hs, _ => simp [step] at hs
      | [_], hs, _ => simp [step] at hs
      | [_, _], hs, _ => simp [step] at hs

theorem gH_free (h1 h2 : Nat) : ∀ t : T, occN h1 t = 0 → gH h1 h2 t
  | S, _ => trivial
  | var n, h => by
    show n ≠ h1
    intro e; subst e; simp [occN] at h
  | app f x, h => by
    simp only [occN] at h
    exact Or.inr ⟨gH_free h1 h2 f (by omega), gH_free h1 h2 x (by omega)⟩

/-- H1ok holds automatically for c0 = S.a1 -/
theorem h1ok_Sa1 (a1 : T) (h1 h2 : Nat) (h12 : h1 ≠ h2) (ha1S : head a1 = S) (hf1 : occN h1 a1 = 0) :
    ∀ (k : Nat) (g : T) (L : List T), run k (args (app S a1) ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R') := by
  intro k g L hk hg
  left
  match k, hk with
  | 0, hk =>
    simp [args, run] at hk
    rw [← hk.1, ha1S] at hg; simp at hg
  | k' + 1, hk =>
    have hs : step (args (app S a1) ++ [var h1, var h2]) = some (args a1 ++ [var h2, app (var h1) (var h2)]) := by
      simp [args, step, ha1S]
    simp only [run] at hk
    rw [hs] at hk
    simp only at hk
    have h0 : ∀ e ∈ args a1 ++ [var h2, app (var h1) (var h2)], gH h1 h2 e := by
      intro e he; simp at he
      rcases he with he | he | he
      · exact gH_free h1 h2 e (occN_args h1 a1 hf1 e he)
      · rw [he]; show h2 ≠ h1; exact Ne.symm h12
      · rw [he]; exact Or.inl ⟨rfl, rfl⟩
    have hgg := gH_run h1 h2 k' _ _ h0 hk g (by simp)
    exact gH_h1head h1 h2 g hgg hg

/-- **THEOREM PBT (pattern beta with c0 = S.a1, no replay hypothesis).**  If the earlier phase (any run from L0)
    opens the element (S.a1).w with y at position 3 - i.e. reaches [(S.a1).w, b, y] ++ R0, where w = b0.(S.a1) -
    and later reaches a p-front list with >= 3 elements, then the next phase of w.y never makes a proper transfer. -/
theorem pbt_main (b0 a1 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (hb0S : head b0 = S) (ha1S : head a1 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 a1 = 0)
    (hf1 : occN h1 a1 = 0) (hf2 : occN h2 a1 = 0) (hV : fresh3 H (app (app b0 (app S a1)) (var 2)))
    (L0 : List T) (t T' : Nat) (b0' : T) (R0 : List T)
    (hfront : run t L0 = some (app (app S a1) (app b0 (app S a1)) :: b0' :: var 2 :: R0))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c (app S a1))) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  have hc0S : head (app S a1) = S := by simp [head]
  have hy1' : occ2 (app S a1) = 0 := by simp [occ2]; exact hy1
  have hf1' : occN h1 (app S a1) = 0 := by simp [occN]; exact hf1
  have hf2' : occN h2 (app S a1) = 0 := by simp [occN]; exact hf2
  -- one step after the beta1 front: c0 runs on (w, y)
  have hc0w : run (t + 1) L0 = some (args (app S a1) ++ app b0 (app S a1) :: var 2 :: app b0' (var 2) :: R0) := by
    rw [run_add t 1, hfront, Option.bind_some]
    simp [run, step, head, args]
  have hT1 : t + 1 < T' ∨ t + 1 = T' := by omega
  rcases hT1 with hlt | heq
  · exact beta_main b0 (app S a1) c h1 h2 H hc hc2 hh1 hh2 h12 hH hb0S hc0S hy0 hy1' hf1' hf2' hV L0 (t + 1) T'
      (app b0' (var 2) :: R0) hc0w hlt f b d R hT hf (h1ok_Sa1 a1 h1 h2 h12 ha1S hf1)
  · exfalso
    subst heq
    rw [hc0w] at hT
    simp [args] at hT
    rw [← hT.1, ha1S] at hf; simp at hf

/-! ### Theorem NHALL: multi-wrapper handlers whose every level's c-code never calls its holes -/

/-- generic barrier count -/
def nbarG (bar : T → Bool) : List T → Nat
  | [] => 0
  | e :: L => (if bar e = true then 1 else 0) + nbarG bar L

theorem nbarG_append (bar : T → Bool) : ∀ A B : List T, nbarG bar (A ++ B) = nbarG bar A + nbarG bar B
  | [], B => by simp [nbarG]
  | e :: A, B => by simp [nbarG, nbarG_append bar A B]; omega

def BIG (bar : T → Bool) (B : List T) (L : List T) : Prop :=
  ∃ Tp : List T, L = Tp ++ B ∧ (∀ e ∈ Tp, occ2 e = 0) ∧ 2 ≤ nbarG bar Tp

theorem big2_shape (bar : T → Bool) (B : List T) (a : T) (L : List T) (hI : BIG bar B (a :: L))
    (hna : bar a = false) :
    ∃ b d R', a :: L = a :: b :: d :: R' ++ B ∧ (∀ e ∈ a :: b :: d :: R', occ2 e = 0) ∧
      2 ≤ nbarG bar (b :: d :: R') := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbarG] at hn
  | [a1], _, _, hn => simp [nbarG] at hn; split at hn <;> omega
  | [a1, b1], hL, _, hn =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    simp [nbarG, hna] at hn; split at hn <;> omega
  | a1 :: b1 :: d1 :: R1, hL, hy, hn =>
    simp at hL; obtain ⟨rfl, hL2⟩ := hL
    refine ⟨b1, d1, R1, by rw [hL2]; simp, hy, ?_⟩
    simp [nbarG, hna] at hn ⊢; omega

theorem big2_step (bar : T → Bool) (hbar : ∀ b d, bar b = true → bar (app b d) = true)
    (B : List T) (a b d : T) (R : List T) (hI : BIG bar B (a :: b :: d :: R))
    (hna : bar a = false) : BIG bar B (args a ++ d :: app b d :: R) := by
  obtain ⟨b1, d1, R1, hL, hy, hn⟩ := big2_shape bar B a _ hI hna
  simp at hL
  obtain ⟨rfl, rfl, hR⟩ := hL
  refine ⟨args a ++ d :: app b d :: R1, by rw [hR]; simp, ?_, ?_⟩
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact occ2_args a (hy a (by simp)) e he
    · rw [he]; exact hy d (by simp)
    · rw [he]; simp only [occ2]; have := hy b (by simp); have := hy d (by simp); omega
    · exact hy e (by simp [he])
  · rw [nbarG_append]
    have hbd : (if bar b = true then 1 else 0) ≤ (if bar (app b d) = true then 1 else 0) := by
      by_cases hb : bar b = true
      · simp [hb, hbar b d hb]
      · simp [hb]
    simp only [nbarG] at hn ⊢
    omega

/-- at a barrier front of a BIG list, position 3 is a y-free top element or the first bottom element -/
theorem big2_pos3 (bar : T → Bool) (B : List T) (hB : B0ok B) (a b d : T) (R : List T)
    (hI : BIG bar B (a :: b :: d :: R)) : occ2 d = 0 ∨ d = var 2 := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbarG] at hn
  | [a1], _, _, hn => simp [nbarG] at hn; split at hn <;> omega
  | [a1, b1], hL, _, _ =>
    simp at hL
    obtain ⟨_, _, hB2⟩ := hL
    exact hB d (by rw [← hB2]; simp)
  | a1 :: b1 :: d1 :: R1, hL, hy, _ =>
    simp at hL; obtain ⟨_, _, rfl, _⟩ := hL
    left; exact hy d (by simp)

/-- the first barrier front of a BIG phase -/
theorem big2_phase (bar : T → Bool) (hbar : ∀ b d, bar b = true → bar (app b d) = true) (B : List T)
    (L0 : List T) (h0 : BIG bar B L0) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    BIG bar B L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧ BIG bar B L1 ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ bar f = true) ∧ run (m - m1) L1 = some L
  | 0, L, h => by simp [run] at h; subst h; exact Or.inl h0
  | m + 1, L, h => by
    have hadd := run_add m 1 L0
    rw [h] at hadd
    cases hm : run m L0 with
    | none => rw [hm] at hadd; simp at hadd
    | some Lm =>
      rw [hm] at hadd
      have h1 : run 1 Lm = some L := by simpa using hadd.symm
      have hstep : step Lm = some L := by
        simp only [run] at h1
        cases hs : step Lm with
        | none => rw [hs] at h1; simp at h1
        | some L' => rw [hs] at h1; simp at h1; rw [h1]
      rcases big2_phase bar hbar B L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hb1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          by_cases hb : bar f = true
          · right
            exact ⟨m, f :: b :: d :: R, by omega, hm, hB, ⟨f, b, d, R, rfl, hb⟩, by simpa using h1⟩
          · left
            simp only [step] at hstep
            split at hstep
            · injection hstep with hstep; subst hstep
              exact big2_step bar hbar B f b d R hB (by simpa using hb)
            · simp at hstep
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hb1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

/-- generic first-barrier lemma with an arbitrary invariant preserved by non-barrier S-headed steps -/
theorem phaseQ (bar : T → Bool) (Inv : List T → Prop)
    (hInv : ∀ f b d R, Inv (f :: b :: d :: R) → bar f = false → head f = S → Inv (args f ++ d :: app b d :: R))
    (L0 : List T) (h0 : Inv L0) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    Inv L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧ Inv L1 ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ bar f = true) ∧ run (m - m1) L1 = some L
  | 0, L, h => by simp [run] at h; subst h; exact Or.inl h0
  | m + 1, L, h => by
    have hadd := run_add m 1 L0
    rw [h] at hadd
    cases hm : run m L0 with
    | none => rw [hm] at hadd; simp at hadd
    | some Lm =>
      rw [hm] at hadd
      have h1 : run 1 Lm = some L := by simpa using hadd.symm
      have hstep : step Lm = some L := by
        simp only [run] at h1
        cases hs : step Lm with
        | none => rw [hs] at h1; simp at h1
        | some L' => rw [hs] at h1; simp at h1; rw [h1]
      rcases phaseQ bar Inv hInv L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hb1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          by_cases hb : bar f = true
          · right
            exact ⟨m, f :: b :: d :: R, by omega, hm, hB, ⟨f, b, d, R, rfl, hb⟩, by simpa using h1⟩
          · left
            simp only [step] at hstep
            split at hstep
            · rename_i hfS
              injection hstep with hstep; subst hstep
              exact hInv f b d R hB (by simpa using hb) hfS
            · simp at hstep
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hb1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

def rcombT : List T → T → T
  | [], t => t
  | d :: ds, t => app d (rcombT ds t)

def NHc (c0 : T) (h1 h2 : Nat) : Prop := ∀ (k : Nat) (g : T) (L : List T),
  run k (args c0 ++ [var h1, var h2]) = some (g :: L) → head g ≠ var h1 ∧ head g ≠ var h2

/-- a phase-2 wrapper satisfying the hypotheses of PAF -/
def WOK (h1 h2 : Nat) (u : T) : Prop := ∃ b0 c0, u = app b0 c0 ∧ head b0 = S ∧ head c0 = S ∧ occ2 b0 = 0 ∧
  occ2 c0 = 0 ∧ occN h1 c0 = 0 ∧ occN h2 c0 = 0 ∧ NHc c0 h1 h2

theorem guarded_free (Lv : T) : ∀ t : T, occN 0 t = 0 → guarded Lv t
  | S, _ => trivial
  | var n, h => by
    show n ≠ 0
    intro e; subst e; simp [occN] at h
  | app f x, h => by
    simp only [occN] at h
    exact Or.inr ⟨guarded_free Lv f (by omega), guarded_free Lv x (by omega)⟩

theorem sb_free0 (c : Nat) (hc : c ≠ 0) : ∀ t : T, occN 0 (sb c t) = 0
  | S => by simp [sb, occN]
  | var n => by
    by_cases h0 : n = 0
    · subst h0; simp [sb, occN, hc]
    · simp [sb, occN, h0]
  | app f x => by simp [sb, occN, sb_free0 c hc f, sb_free0 c hc x]

theorem guarded_mono (u Lv2 : T) (hu : occN 0 u = 0) (hL2 : ∃ f x, Lv2 = app f x) :
    ∀ t : T, guarded (app u Lv2) t → guarded Lv2 t
  | S, _ => trivial
  | var n, h => h
  | app f x, h => by
    rcases h with h | ⟨hf, hx⟩
    · rw [h]
      refine Or.inr ⟨guarded_free Lv2 u hu, ?_⟩
      obtain ⟨g, z, hgz⟩ := hL2
      rw [hgz]; exact Or.inl rfl
    · exact Or.inr ⟨guarded_mono u Lv2 hu hL2 f hf, guarded_mono u Lv2 hu hL2 x hx⟩

theorem guarded_prefix_args (Lv : T) : ∀ f : T, wpre Lv f → guarded Lv f →
    ∃ us, args f = args Lv ++ us ∧ ∀ u ∈ us, guarded Lv u
  | S, h, _ => by simp [wpre] at h; subst h; exact ⟨[], by simp, by simp⟩
  | var n, h, _ => by simp [wpre] at h; subst h; exact ⟨[], by simp, by simp⟩
  | app g x, h, hg => by
    by_cases he : app g x = Lv
    · rw [he]; exact ⟨[], by simp, by simp⟩
    · have hwg : wpre Lv g := by
        rcases h with h | h
        · exact absurd h he
        · exact h
      rcases hg with hg | ⟨hgg, hgx⟩
      · exact absurd hg he
      · obtain ⟨us, hus, hall⟩ := guarded_prefix_args Lv g hwg hgg
        refine ⟨us ++ [x], by simp [args, hus], ?_⟩
        intro u hu; simp at hu
        rcases hu with hu | hu
        · exact hall u hu
        · subst hu; exact hgx

theorem occ2_rcombT (c : Nat) (hc2 : c ≠ 2) : ∀ (us : List T), (∀ u ∈ us, occ2 u = 0) →
    occ2 (rcombT (us.map (sb c)) (var 0)) = 0
  | [], _ => by simp [rcombT, occ2]
  | u :: us, h => by
    simp only [List.map_cons, rcombT, occ2]
    rw [sb_occ2 c hc2 u (h u (by simp)), occ2_rcombT c hc2 us (fun v hv => h v (by simp [hv]))]

def WOKp (h1 h2 : Nat) (b0 c0 : T) : Prop := head b0 = S ∧ head c0 = S ∧ occ2 b0 = 0 ∧ occ2 c0 = 0 ∧
  occN h1 c0 = 0 ∧ occN h2 c0 = 0 ∧ NHc c0 h1 h2

theorem wpreB_app' (w b d : T) (h : wpreB w b = true) : wpreB w (app b d) = true := by
  rw [wpreB_iff] at *; exact Or.inr h

/-- **The descent.**  From the start list of a level (wrapper b0.c0, remaining inner wrappers us, bottom B whose first
    element is y-free or the bare y and whose elements are guarded by the next level), every p'-headed front has a
    y-free element or the bare y at position 3, provided every level's c-code never calls its two holes. -/
theorem descend (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) (h12 : h1 ≠ h2) :
    ∀ (us : List T) (b0 c0 : T) (B : List T), WOKp h1 h2 b0 c0 → (∀ u ∈ us, WOK h1 h2 u) → B0ok B →
    (us ≠ [] → ∀ e ∈ B, guarded (rcombT (us.map (sb c)) (var 0)) e) →
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m (args (sb c b0) ++ [sb c c0, rcombT (us.map (sb c)) (var 0)] ++ B) = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2
  | [], b0, c0, B, ⟨hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩, _, hB, _ => by
    intro m f b d R hm hf
    have hpost := paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH
    exact pa_core_g (sb c b0) (sb c c0) B hB (sb_head c c0 hc0S) (sb_occ2 c hc2 b0 hy0) (sb_occ2 c hc2 c0 hy1)
      hpost m f b d R (by simpa [rcombT] using hm) hf
  | u' :: us'', b0, c0, B, ⟨hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩, hus, hB, hg => by
    intro m f b d R hm hf
    obtain ⟨b1, c1, hu', hb1S, hc1S, hy0', hy1', hf1', hf2', hNH'⟩ := hus u' (by simp)
    have hus'' : ∀ u ∈ us'', WOK h1 h2 u := fun u hu => hus u (by simp [hu])
    have hpost := paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH
    -- the next level
    have hLn : rcombT ((u' :: us'').map (sb c)) (var 0) =
        app (app (sb c b1) (sb c c1)) (rcombT (us''.map (sb c)) (var 0)) := by
      simp [rcombT, hu', sb]
    generalize hLnext : rcombT ((u' :: us'').map (sb c)) (var 0) = Lnext at hm hg
    have hLnS : head Lnext = S := by rw [← hLnext, hLn]; simp [head, sb_head c b1 hb1S]
    have hc0'S : head (sb c c0) = S := sb_head c c0 hc0S
    let bar : T → Bool := fun t => wpreB (sb c c0) t || wpreB Lnext t
    have hbar : ∀ b' d', bar b' = true → bar (app b' d') = true := by
      intro b' d' hb'
      simp only [bar, Bool.or_eq_true] at hb' ⊢
      rcases hb' with hb' | hb'
      · exact Or.inl (wpreB_app' _ _ _ hb')
      · exact Or.inr (wpreB_app' _ _ _ hb')
    let Inv : List T → Prop := fun L => BIG bar B L ∧ ∀ e ∈ L, guarded Lnext e
    have hInv : ∀ f' b' d' R', Inv (f' :: b' :: d' :: R') → bar f' = false → head f' = S →
        Inv (args f' ++ d' :: app b' d' :: R') := by
      intro f' b' d' R' ⟨hBI, hG⟩ hbf hfS
      refine ⟨big2_step bar hbar B f' b' d' R' hBI hbf, ?_⟩
      have hnw : ¬ wpre Lnext f' := by
        intro hw
        have : wpreB Lnext f' = true := (wpreB_iff _ _).2 hw
        simp [bar, this] at hbf
      intro e he; simp at he
      rcases he with he | he | he | he
      · exact guarded_args Lnext f' (hG f' (by simp)) hfS hnw e he
      · rw [he]; exact hG d' (by simp)
      · rw [he]; exact Or.inr ⟨hG b' (by simp), hG d' (by simp)⟩
      · exact hG e (by simp [he])
    have hy0'' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
    have hy1'' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
    have hyL : occ2 Lnext = 0 := by
      rw [← hLnext]
      apply occ2_rcombT c hc2
      intro u hu; simp at hu
      rcases hu with hu | hu
      · rw [hu, hu']; simp [occ2, hy0', hy1']
      · obtain ⟨b2, c2, he, _, _, hy2, hy3, _⟩ := hus'' u hu
        rw [he]; simp [occ2, hy2, hy3]
    have hI0 : Inv (args (sb c b0) ++ [sb c c0, Lnext] ++ B) := by
      refine ⟨⟨args (sb c b0) ++ [sb c c0, Lnext], rfl, ?_, ?_⟩, ?_⟩
      · intro e he; simp at he
        rcases he with he | he | he
        · exact occ2_args _ hy0'' e he
        · rw [he]; exact hy1''
        · rw [he]; exact hyL
      · rw [nbarG_append]
        have e1 : bar (sb c c0) = true := by simp [bar, (wpreB_iff _ _).2 (wpre_self _)]
        have e2 : bar Lnext = true := by simp [bar, (wpreB_iff _ _).2 (wpre_self _)]
        simp [nbarG, e1, e2]
      · intro e he; simp at he
        rcases he with he | he | he | he
        · exact guarded_free Lnext e (occN_args 0 _ (sb_free0 c hc b0) e he)
        · rw [he]; exact guarded_free Lnext _ (sb_free0 c hc c0)
        · rw [he, ← hLnext, hLn]; exact Or.inl rfl
        · exact hg (by simp) e he
    rcases phaseQ bar Inv hInv _ hI0 m _ hm with ⟨_, hG⟩ | ⟨m1, L1, hlt, hr1, ⟨hBI1, hG1⟩, ⟨f1, b1', d1, R1, hL1, hbf1⟩, hrest⟩
    · exact absurd hf (guarded_head Lnext (by rw [hLnS]; simp) f (hG f (by simp)))
    · subst hL1
      have hmk : m - m1 = (m - m1 - 1) + 1 := by omega
      rw [hmk] at hrest
      simp only [run] at hrest
      by_cases hx1 : wpre (sb c c0) f1
      · exfalso
        obtain ⟨e1, e2, B', hs1⟩ := x1_open (sb c c0) f1 b1' d1 R1 hc0'S hx1
        rw [hs1] at hrest
        simp only at hrest
        exact hpost e1 e2 B' _ f _ hrest hf
      · have hx2 : wpre Lnext f1 := by
          simp only [bar, Bool.or_eq_true] at hbf1
          rcases hbf1 with h | h
          · exact absurd ((wpreB_iff _ _).1 h) hx1
          · exact (wpreB_iff _ _).1 h
        have hf1S : head f1 = S := by rw [wpre_headeq _ f1 hx2]; exact hLnS
        obtain ⟨us1, hus1, hgus1⟩ := guarded_prefix_args Lnext f1 hx2 (hG1 f1 (by simp))
        have hargsL : args Lnext = args (sb c b1) ++ [sb c c1, rcombT (us''.map (sb c)) (var 0)] := by
          rw [← hLnext, hLn]; simp [args]
        have hs2 : step (f1 :: b1' :: d1 :: R1) = some (args (sb c b1) ++
            [sb c c1, rcombT (us''.map (sb c)) (var 0)] ++ (us1 ++ d1 :: app b1' d1 :: R1)) := by
          simp [step, hf1S, hus1, hargsL]
        rw [hs2] at hrest
        simp only at hrest
        -- the new bottom
        have hyf1 : occ2 f1 = 0 := by
          obtain ⟨Tp, hTp, hyT, hnT⟩ := hBI1
          match Tp, hTp, hnT with
          | [], _, hnT => simp [nbarG] at hnT
          | t1 :: Tp', hTp, _ =>
            simp at hTp; rw [hTp.1]; exact hyT t1 (by simp)
        have hB' : B0ok (us1 ++ d1 :: app b1' d1 :: R1) := by
          intro e he
          cases us1 with
          | nil =>
            simp only [List.nil_append, List.head?_cons, Option.some.injEq] at he
            subst he
            exact big2_pos3 bar B hB f1 b1' _ R1 hBI1
          | cons u us1' =>
            simp only [List.cons_append, List.head?_cons, Option.some.injEq] at he
            subst he
            left
            exact occ2_args f1 hyf1 _ (by rw [hus1]; simp)
        have hfree' : occN 0 (app (sb c b1) (sb c c1)) = 0 := by
          simp [occN, sb_free0 c hc b1, sb_free0 c hc c1]
        have hg' : us'' ≠ [] → ∀ e ∈ us1 ++ d1 :: app b1' d1 :: R1,
            guarded (rcombT (us''.map (sb c)) (var 0)) e := by
          intro hne e he
          have hL2app : ∃ g z, rcombT (us''.map (sb c)) (var 0) = app g z := by
            match us'', hne with
            | v :: vs, _ => exact ⟨sb c v, rcombT (vs.map (sb c)) (var 0), by simp [rcombT]⟩
          have hmono : ∀ t, guarded Lnext t → guarded (rcombT (us''.map (sb c)) (var 0)) t := by
            intro t ht
            rw [← hLnext, hLn] at ht
            exact guarded_mono _ _ hfree' hL2app t ht
          simp at he
          rcases he with he | he | he | he
          · exact hmono e (hgus1 e he)
          · rw [he]; exact hmono _ (hG1 d1 (by simp))
          · rw [he]; exact hmono _ (Or.inr ⟨hG1 b1' (by simp), hG1 d1 (by simp)⟩)
          · exact hmono e (hG1 e (by simp [he]))
        exact descend c h1 h2 hc hc2 hh1 hh2 h12 us'' b1 c1 _ ⟨hb1S, hc1S, hy0', hy1', hf1', hf2', hNH'⟩ hus''
          hB' hg' (m - m1 - 1) f b d R (by simpa using hrest) hf

/-- **THEOREM NHALL.**  Let V = v1.(v2.(...(vn.y))) be a phase-2 handler (any number n >= 1 of wrappers) such that
    every wrapper v_j = b_j.c_j has S-headed y-free b_j, c_j and the abstract run of args(c_j) ++ [h1, h2] never
    calls h1 or h2.  Then in the next phase (datum V[y:=p', p:=c]) every p'-headed front has a y-free element or
    the bare y at position 3: no proper transfer.  The hypothesis concerns only the codes c_j of the handler. -/
theorem nhall_main (ws : List T) (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hws : ws ≠ []) (hall : ∀ u ∈ ws, WOK h1 h2 u) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [rcombT (ws.map (sb c)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  match ws, hws, hall with
  | u0 :: ws', _, hall =>
    obtain ⟨b0, c0, hu0, hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩ := hall u0 (by simp)
    have hall' : ∀ u ∈ ws', WOK h1 h2 u := fun u hu => hall u (by simp [hu])
    have hD3 : rcombT ((u0 :: ws').map (sb c)) (var 0) =
        app (app (sb c b0) (sb c c0)) (rcombT (ws'.map (sb c)) (var 0)) := by
      simp [rcombT, hu0, sb]
    rw [hD3] at hm
    have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
    match m, hm with
    | 0, hm =>
      simp [run] at hm; rw [← hm.1] at hf; simp [head, hb0'] at hf
    | m' + 1, hm =>
      have hs : step [app (app (sb c b0) (sb c c0)) (rcombT (ws'.map (sb c)) (var 0)), var 1, var 2, var 3] =
          some (args (sb c b0) ++ [sb c c0, rcombT (ws'.map (sb c)) (var 0)] ++
            [var 2, app (var 1) (var 2), var 3]) := by
        simp [step, head, hb0', args]
      simp only [run] at hm
      rw [hs] at hm
      simp only at hm
      have hB : B0ok [var 2, app (var 1) (var 2), var 3] := by
        intro e he; simp at he; subst he; right; rfl
      have hg : ws' ≠ [] → ∀ e ∈ [var 2, app (var 1) (var 2), var 3],
          guarded (rcombT (ws'.map (sb c)) (var 0)) e := by
        intro _ e he; simp at he
        rcases he with he | he | he <;> (subst he; apply guarded_free; simp [occN])
      exact descend c h1 h2 hc hc2 hh1 hh2 h12 ws' b0 c0 _ ⟨hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩ hall' hB hg
        m' f b d R hm hf

/-! ### Theorem CLOSEDGLUE: a glue [a1, w, y] whose front a1 does not contain the live atom forces IGEN -/

theorem occN_run (n : Nat) : ∀ (k : Nat) (L L' : List T), (∀ e ∈ L, occN n e = 0) → run k L = some L' →
    ∀ e ∈ L', occN n e = 0
  | 0, L, L', h0, h => by simp [run] at h; subst h; exact h0
  | k + 1, L, L', h0, h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      apply occN_run n k L1 L' _ h
      match L, hs, h0 with
      | a :: b :: d :: R, hs, h0 =>
        simp only [step] at hs
        split at hs
        · injection hs with hs; subst hs
          intro e he; simp at he
          rcases he with he | he | he | he
          · exact occN_args n a (h0 a (by simp)) e he
          · rw [he]; exact h0 d (by simp)
          · rw [he]; simp only [occN]; have := h0 b (by simp); have := h0 d (by simp); omega
          · exact h0 e (by simp [he])
        · simp at hs
      | [], hs, _ => simp [step] at hs
      | [_], hs, _ => simp [step] at hs
      | [_, _], hs, _ => simp [step] at hs

theorem occN_head (n : Nat) : ∀ t : T, head t = var n → occN n t ≠ 0
  | S, h => by simp [head] at h
  | var m, h => by simp [head] at h; subst h; simp [occN]
  | app f x, h => by
    simp only [head] at h
    have := occN_head n f h
    simp only [occN]; omega

/-- **THEOREM CLOSEDGLUE.**  If the earlier phase (any run from L0) passes through a glue list [a1, w, y] ++ R0 whose
    front a1 is S-headed and free of the live atom p (var 0) (frozen atoms allowed), and later reaches a p-front list
    with >= 3 elements, then the next phase of w.y (w S-headed) has NO p'-front at all.  (Run from the glue, a1's
    code cannot bring p to the front; calling its first hole is a y-call of the earlier phase; so it calls its second
    hole w.y, i.e. the earlier phase opens a copy of w.y and lays out args(w.y): IGEN.) -/
theorem closedglue_main (a1 w : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (ha1S : head a1 = S) (ha10 : occN 0 a1 = 0) (hwS : head w = S)
    (hf1 : occN h1 a1 = 0) (hf2 : occN h2 a1 = 0) (hV : fresh3 H (app w (var 2)))
    (L0 : List T) (t T' : Nat) (R0 : List T) (hglue : run t L0 = some (a1 :: w :: var 2 :: R0))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T),
      run m [asub (sg3 c) (app w (var 2)), var 1, var 2, var 3] = some (f' :: L') → head f' ≠ var 0 := by
  have hwyS : head (app w (var 2)) = S := by simp [head, hwS]
  have hs2_1 : sgA h1 h2 (app w (var 2)) h1 = var 2 := by simp [sgA]
  have hs2_2 : sgA h1 h2 (app w (var 2)) h2 = app w (var 2) := by simp [sgA, Ne.symm h12]
  have hA2 : (args a1 ++ [var h1, var h2]).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0 =
      args a1 ++ var 2 :: app w (var 2) :: R0 := by
    have hargs : (args a1).map (asub (sgA h1 h2 (app w (var 2)))) = args a1 := by
      have : (args a1).map (asub (sgA h1 h2 (app w (var 2)))) = (args a1).map id := by
        apply List.map_congr_left
        intro e he
        exact asub_sgA_id h1 h2 _ e (occN_args h1 a1 hf1 e he) (occN_args h2 a1 hf2 e he)
      simpa using this
    simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs2_1, hs2_2]
    simp
  have ht1 : run (t + 1) L0 = some ((args a1 ++ [var h1, var h2]).map
      (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
    rw [hA2, run_add t 1, hglue, Option.bind_some]
    simp [run, step, ha1S]
  have hA0 : ∀ e ∈ args a1 ++ [var h1, var h2], occN 0 e = 0 := by
    intro e he; simp at he
    rcases he with he | he | he
    · exact occN_args 0 a1 ha10 e he
    · rw [he]; simp [occN]; omega
    · rw [he]; simp [occN]; omega
  have hnB : 2 ≤ nHB h1 h2 (args a1 ++ [var h1, var h2]) := by
    rw [nHB_append]; simp [nHB, isHB, head]
  -- the image of an abstract front that is not h2-headed is never a var 0-headed or S-headed-then-p front
  have himg : ∀ g : T, head g ≠ var h2 → occN 0 g = 0 →
      head (asub (sgA h1 h2 (app w (var 2))) g) ≠ var 0 := by
    intro g hg2 hg0
    rcases head_cases g with hgS | ⟨n, hn⟩
    · rw [asub_headS _ g hgS]; simp
    · rw [asub_headvar _ n g hn]
      have hn0 : n ≠ 0 := by intro e; subst e; exact occN_head 0 g hn hg0
      have hn2 : n ≠ h2 := by intro e; subst e; exact hg2 hn
      by_cases e1 : n = h1
      · subst e1; rw [hs2_1]; simp [head]
      · simp [sgA, e1, hn2, head, hn0]
  have hex : ∃ k g Lk, run k (args a1 ++ [var h1, var h2]) = some (g :: Lk) ∧ head g = var h2 := by
    apply Classical.byContradiction
    intro hno
    cases hj : run (T' - (t + 1)) (args a1 ++ [var h1, var h2]) with
    | some AT =>
      -- the earlier phase at time T' is the image of AT
      have h2T : run T' L0 = some (AT.map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
        rw [show T' = (t + 1) + (T' - (t + 1)) by omega, run_add (t + 1) (T' - (t + 1)), ht1, Option.bind_some]
        exact run_append _ _ _ R0 (asub_run _ _ _ _ hj)
      rw [hT] at h2T
      have hne := run_ne_nil _ _ AT (by simp) hj
      match AT, hne, h2T, hj with
      | g :: Lg, _, h2T, hj =>
        simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h2T
        have hg2 : head g ≠ var h2 := fun e => hno ⟨_, g, Lg, hj, e⟩
        have hg0 : occN 0 g = 0 := occN_run 0 _ _ _ hA0 hj g (by simp)
        exact himg g hg2 hg0 (by rw [← h2T.1]; exact hf)
    | none =>
      obtain ⟨k, Ak, hk, hrk, hsk⟩ := run_first_none _ _ hj
      obtain ⟨g, rest, hAk, hgS⟩ := nHB_stop h1 h2 _ Ak k hnB hrk hsk
      subst hAk
      obtain ⟨hstuckE, _⟩ := image_stuck _ _ R0 L0 (t + 1) T' (by omega) ht1 f b d R hT hf k _ hrk
      have hg2 : head g ≠ var h2 := fun e => hno ⟨k, g, rest, hrk, e⟩
      have hg0 : occN 0 g = 0 := occN_run 0 _ _ _ hA0 hrk g (by simp)
      have hneS : head (asub (sgA h1 h2 (app w (var 2))) g) ≠ S := by
        obtain ⟨n, hn⟩ : ∃ n, head g = var n := (head_cases g).resolve_left hgS
        rw [asub_headvar _ n g hn]
        have hn2 : n ≠ h2 := by intro e; subst e; exact hg2 hn
        by_cases e1 : n = h1
        · subst e1; rw [hs2_1]; simp [head]
        · simp [sgA, e1, hn2, head]
      have hp2 : run (t + 1 + k) L0 = some ((g :: rest).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
        rw [run_add (t + 1) k, ht1, Option.bind_some]
        exact run_append k _ _ R0 (asub_run _ k _ _ hrk)
      have hnone : run (t + 1 + k + 1) L0 = none := by
        rw [run_add (t + 1 + k) 1, hp2, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ hneS]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      exact himg g hg2 hg0 (by rw [he.1]; exact hf)
  -- an h2-front: the earlier phase opens a copy of w.y, IGEN
  obtain ⟨k, g, Lk, hk, hg⟩ := hex
  obtain ⟨_, hearly⟩ := image_stuck _ _ R0 L0 (t + 1) T' (by omega) ht1 f b d R hT hf k (g :: Lk) hk
  have p2k : run (t + 1 + k) L0 = some ((g :: Lk).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
    rw [run_add (t + 1) k, ht1, Option.bind_some]
    exact run_append k _ _ R0 (asub_run _ k _ _ hk)
  have hGS : head (asub (sgA h1 h2 (app w (var 2))) g) = S := by
    rw [asub_headvar _ h2 g hg, hs2_2]; exact hwyS
  have hTgt : t + 1 + k < T' := by
    apply Nat.lt_of_not_le
    intro hle
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hearly (by omega)
    · subst heq
      rw [p2k] at hT
      simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at hT
      rw [← hT.1, hGS] at hf; simp at hf
  obtain ⟨Ln, hLn, _⟩ := run_prefix T' (t + 1 + k + 1) L0 _ hT (by omega)
  have hstep : step ((g :: Lk).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) = some Ln := by
    rw [run_add (t + 1 + k) 1, p2k, Option.bind_some] at hLn
    simp only [run] at hLn
    cases hs : step ((g :: Lk).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) with
    | none => rw [hs] at hLn; simp at hLn
    | some L1 => rw [hs] at hLn; simpa using hLn
  have hargsG := asub_args_var (sgA h1 h2 (app w (var 2))) h2 (by rw [hs2_2]; exact hwyS) g hg
  rw [hs2_2] at hargsG
  have hLn_form : ∃ B2, Ln = args (app w (var 2)) ++ B2 := by
    simp only [List.map_cons, List.cons_append] at hstep
    match hrest : Lk.map (asub (sgA h1 h2 (app w (var 2)))) ++ R0, hstep with
    | b2 :: d2 :: R2, hstep =>
      simp only [step, hGS, ite_true, Option.some.injEq] at hstep
      rw [hargsG] at hstep
      exact ⟨List.map (asub (sgA h1 h2 (app w (var 2)))) (args g) ++ d2 :: app b2 d2 :: R2,
        by rw [← hstep, List.append_assoc]⟩
    | [], hstep => simp [step] at hstep
    | [_], hstep => simp [step] at hstep
  obtain ⟨B2, hB2⟩ := hLn_form
  rw [hB2] at hLn
  have hVa : args (app w (var 2)) ≠ [] := by simp [args]
  exact igen_main (app w (var 2)) c H hc hH hwyS hVa hV L0 (t + 1 + k + 1) T' B2 (by omega) hLn f b d R hT hf

/-! ### Theorem PAH: a single wrapper whose c-code is atom-headed (p- or frozen-headed) -/

/-- **THEOREM PAH.**  Single wrapper w = b0.c0 with b0 S-headed and y-free and c0 headed by an atom other than y
    (the live p, which becomes the frozen c, or a frozen atom).  Then every p'-headed front of the next phase has a
    y-free element or the bare y at position 3: the barrier phase can only end at a c0'-prefixed front, which is
    headed by a frozen atom and stuck (a re-execution). -/
theorem pah_main (b0 c0 : T) (c n : Nat) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hy0 : occ2 b0 = 0)
    (hy1 : occ2 c0 = 0) (hn : head c0 = var n) (hn2 : n ≠ 2) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hc0'h : head (sb c c0) ≠ S := by
    have : sb c c0 = asub (fun k => if k = 0 then var c else var k) c0 := by
      clear hm hf hy1 hy1' hn hn2
      induction c0 with
      | S => simp [sb, asub]
      | var k => by_cases h : k = 0 <;> simp [sb, asub, h]
      | app f x ihf ihx => simp [sb, asub, ihf, ihx]
    rw [this, asub_headvar _ n c0 hn]
    by_cases h : n = 0 <;> simp [h, head]
  have hstep0 : step [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] =
      some ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    simp [step, head, hb0', args, BOT]
  have hBI : BI (sb c c0) ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    refine ⟨args (sb c b0) ++ [sb c c0, var 0], rfl, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB (sb c c0) (sb c c0) = true := by
        simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB (sb c c0) (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  match m, hm with
  | 0, hm =>
    simp [run] at hm
    obtain ⟨hf0, _⟩ := hm
    rw [← hf0] at hf; simp [head, hb0'] at hf
  | m' + 1, hm =>
    simp only [run] at hm
    rw [hstep0] at hm
    simp only at hm
    rcases pa_phase (sb c c0) _ hBI m' _ hm with hB | ⟨m1, L1, hlt, _, ⟨f1, b1, d1, R1, hL1, hwp⟩, hrest⟩
    · exact bi_x2 (sb c c0) f b d R hB
    · exfalso
      subst hL1
      have hf1 : head f1 ≠ S := by rw [wpre_headeq _ f1 hwp]; exact hc0'h
      have hj : m' - m1 = (m' - m1 - 1) + 1 := by omega
      rw [hj] at hrest
      simp only [run] at hrest
      rw [step_head_ne _ _ hf1] at hrest
      simp at hrest
#print axioms asub_run
#print axioms nHB_stop
#print axioms paf_post
#print axioms paf_main
#print axioms gcl
#print axioms igen_main
#print axioms alpha_main
#print axioms closedglue_main
#print axioms pah_main
#print axioms pax_main
#print axioms pamf_main
#print axioms ln0_main
#print axioms beta_main
#print axioms h1ok_Sa1
#print axioms pbt_main
#print axioms descend
#print axioms nhall_main
#print axioms r3_cx_ordered
#print axioms r3_cx_phase2
#print axioms r3_cx_next
#print axioms r3_cx_phase3

/-! =====================================================================================================
    S1 agent (2026-10-27): THEOREM S1 (structural claim) and the single-wrapper consequences.
    Everything below is new; everything above is R3F.lean verbatim. -/
/-! ## S1 Part 1: class ranks, sorted spines, the segment invariant -/

/-- class rank: 0 = closed (no p, x, y, r; frozen atoms allowed), 1 = P (p, no x, y, r), 2 = Y (x, y or r) -/
def rk (t : T) : Nat := if occN 1 t + occN 2 t + occN 3 t ≠ 0 then 2 else if occN 0 t ≠ 0 then 1 else 0

theorem rk_le2 (t : T) : rk t ≤ 2 := by
  unfold rk; split <;> (try split) <;> omega

theorem rk_app (b c : T) : rk (app b c) = max (rk b) (rk c) := by
  unfold rk
  simp only [occN]
  by_cases h1 : occN 1 b + occN 2 b + occN 3 b = 0 <;> by_cases h2 : occN 1 c + occN 2 c + occN 3 c = 0 <;>
    by_cases h3 : occN 0 b = 0 <;> by_cases h4 : occN 0 c = 0 <;> simp_all <;> omega

theorem rk_app_left (b c : T) : rk b ≤ rk (app b c) := by rw [rk_app]; omega
theorem rk_app_right (b c : T) : rk c ≤ rk (app b c) := by rw [rk_app]; omega

/-- argument occurrences are bounded by the term's -/
theorem occN_args_le (n : Nat) : ∀ t : T, ∀ s ∈ args t, occN n s ≤ occN n t
  | S, s, hs => by simp [args] at hs
  | var _, s, hs => by simp [args] at hs
  | app f x, s, hs => by
    simp [args] at hs
    simp only [occN]
    rcases hs with hs | hs
    · have := occN_args_le n f s hs; omega
    · subst hs; omega

theorem rk_spec (t : T) : (rk t = 2 ∧ occN 1 t + occN 2 t + occN 3 t ≠ 0) ∨
    (rk t = 1 ∧ occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t ≠ 0) ∨
    (rk t = 0 ∧ occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t = 0) := by
  unfold rk
  by_cases h : occN 1 t + occN 2 t + occN 3 t ≠ 0
  · rw [if_pos h]; exact Or.inl ⟨rfl, h⟩
  · rw [if_neg h]
    by_cases h0 : occN 0 t ≠ 0
    · rw [if_pos h0]; exact Or.inr (Or.inl ⟨rfl, by omega, h0⟩)
    · rw [if_neg h0]; exact Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)

theorem rk_eq2 (t : T) : rk t = 2 ↔ occN 1 t + occN 2 t + occN 3 t ≠ 0 := by
  rcases rk_spec t with h | h | h <;> constructor <;> intro e <;> omega

theorem rk_eq1 (t : T) : rk t = 1 ↔ (occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t ≠ 0) := by
  rcases rk_spec t with h | h | h <;> constructor <;> intro e <;> omega

theorem rk_eq0 (t : T) : rk t = 0 ↔ (occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t = 0) := by
  rcases rk_spec t with h | h | h <;> constructor <;> intro e <;> omega

theorem rk_cases (t : T) : rk t = 0 ∨ rk t = 1 ∨ rk t = 2 := by
  have := rk_le2 t; omega

theorem rk_mono_occ (s t : T) (h : ∀ n, occN n s ≤ occN n t) : rk s ≤ rk t := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  rcases rk_cases s with hs | hs | hs <;> rcases rk_cases t with ht | ht | ht <;> try omega
  · rw [rk_eq1] at hs; rw [rk_eq0] at ht; omega
  · rw [rk_eq2] at hs; rw [rk_eq0] at ht; omega
  · rw [rk_eq2] at hs; rw [rk_eq1] at ht; omega

theorem rk_args_le (t : T) (s : T) (hs : s ∈ args t) : rk s ≤ rk t :=
  rk_mono_occ s t (fun n => occN_args_le n t s hs)

/-- the occurrences of an S-headed term are those of its arguments -/
theorem occN_spine (n : Nat) : ∀ t : T, head t = S → occN n t = ((args t).map (occN n)).sum
  | S, _ => by simp [occN, args]
  | var _, h => by simp [head] at h
  | app f x, h => by
    simp only [head] at h
    simp [occN, args, occN_spine n f h]

theorem sum_ne_zero_mem : ∀ (l : List T), (l.map (occN 0)).sum ≠ 0 → ∃ s ∈ l, occN 0 s ≠ 0
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : occN 0 a = 0
    · simp [ha] at h
      obtain ⟨s, hs, hs0⟩ := sum_ne_zero_mem l (by simpa using h)
      exact ⟨s, by simp [hs], hs0⟩
    · exact ⟨a, by simp, ha⟩

/-- an S-headed P-term has a P-argument -/
theorem P_has_P_arg (t : T) (hS : head t = S) (h1 : rk t = 1) : ∃ s ∈ args t, rk s = 1 := by
  have h1' := (rk_eq1 t).1 h1
  have h0 : ((args t).map (occN 0)).sum ≠ 0 := by rw [← occN_spine 0 t hS]; exact h1'.2
  obtain ⟨s, hs, hs0⟩ := sum_ne_zero_mem _ h0
  refine ⟨s, hs, ?_⟩
  have hle := rk_args_le t s hs
  rw [h1] at hle
  rcases rk_cases s with h | h | h
  · exact absurd ((rk_eq0 s).1 h).2 hs0
  · exact h
  · omega

/-- hereditarily sorted spines: every S-headed subterm has its arguments sorted by rank -/
def ordT : T → Prop
  | app f x => ordT f ∧ ordT x ∧ (head f = S → ∀ a ∈ args f, rk a ≤ rk x)
  | _ => True

theorem ordT_args : ∀ t : T, ordT t → ∀ s ∈ args t, ordT s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact ordT_args f h.1 s hs
    · subst hs; exact h.2.1

def srt (L : List T) : Prop := List.Pairwise (fun a b => rk a ≤ rk b) L

theorem ordT_srt : ∀ t : T, ordT t → head t = S → srt (args t)
  | S, _, _ => by simp [srt, args]
  | var _, _, h => by simp [head] at h
  | app f x, h, hh => by
    simp only [head] at hh
    unfold srt
    simp only [args]
    rw [List.pairwise_append]
    refine ⟨ordT_srt f h.1 hh, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    exact h.2.2 hh a ha

/-- the segment invariant: ranks sorted along the list, every element hereditarily sorted -/
def Seg (L : List T) : Prop := srt L ∧ ∀ e ∈ L, ordT e

theorem seg_step (a b c : T) (R : List T) (ha : head a = S) (h : Seg (a :: b :: c :: R)) :
    Seg (args a ++ c :: app b c :: R) := by
  obtain ⟨hs, ho⟩ := h
  unfold srt at hs
  simp only [List.pairwise_cons] at hs
  obtain ⟨ha', hb', hcR, hR⟩ := hs
  have hbc' : rk b ≤ rk c := hb' c (by simp)
  have hac' : rk a ≤ rk c := ha' c (by simp)
  have hrbc : rk (app b c) = rk c := by rw [rk_app]; omega
  refine ⟨?_, ?_⟩
  · unfold srt
    rw [List.pairwise_append]
    refine ⟨ordT_srt a (ho a (by simp)) ha, ?_, ?_⟩
    · simp only [List.pairwise_cons]
      refine ⟨?_, ?_, hR⟩
      · intro x hx
        simp at hx
        rcases hx with hx | hx
        · rw [hx, hrbc]; exact Nat.le_refl _
        · exact hcR x hx
      · intro x hx; rw [hrbc]; exact hcR x hx
    · intro x hx y hy
      have hxa := rk_args_le a x hx
      simp at hy
      rcases hy with hy | hy | hy
      · subst hy; omega
      · subst hy; rw [hrbc]; omega
      · have := hcR y hy; omega
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact ordT_args a (ho a (by simp)) e he
    · rw [he]; exact ho c (by simp)
    · rw [he]
      refine ⟨ho b (by simp), ho c (by simp), ?_⟩
      intro _ x hx
      have := rk_args_le b x hx; omega
    · exact ho e (by simp [he])

theorem step_some (L L' : List T) (h : step L = some L') :
    ∃ a b c R, L = a :: b :: c :: R ∧ head a = S ∧ L' = args a ++ c :: app b c :: R := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    by_cases hS : head a = S
    · rw [if_pos hS] at h
      injection h with h
      exact ⟨a, b, c, R, rfl, hS, h.symm⟩
    · rw [if_neg hS] at h; simp at h
  | [], h => simp [step] at h
  | [_], h => simp [step] at h
  | [_, _], h => simp [step] at h

theorem run_succ_some (k : Nat) (L L' : List T) (h : run (k + 1) L = some L') :
    ∃ L1, step L = some L1 ∧ run k L1 = some L' := by
  simp only [run] at h
  cases hs : step L with
  | none => rw [hs] at h; simp at h
  | some L1 => rw [hs] at h; exact ⟨L1, rfl, h⟩

theorem seg_run : ∀ (k : Nat) (L L' : List T), Seg L → run k L = some L' → Seg L'
  | 0, L, L', h, hr => by simp [run] at hr; subst hr; exact h
  | k + 1, L, L', h, hr => by
    obtain ⟨L1, hs, hr1⟩ := run_succ_some k L L' hr
    obtain ⟨a, b, c, R, rfl, hS, rfl⟩ := step_some L L1 hs
    exact seg_run k _ L' (seg_step a b c R hS h) hr1



/-! ## S1 Part 2: the P-region, the Y-top and Lemma AB (|P| >= 3 is absorbing and forbids a proper transfer) -/

def Preg (L : List T) : List T := L.filter (fun e => rk e == 1)
def Yl (L : List T) : List T := L.filter (fun e => rk e == 2)
def Ytop (L : List T) : Option T := (Yl L).head?

theorem Preg_cons (e : T) (L : List T) : Preg (e :: L) = if rk e = 1 then e :: Preg L else Preg L := by
  unfold Preg
  by_cases h : rk e = 1 <;> simp [List.filter_cons, h]

theorem Preg_append (A B : List T) : Preg (A ++ B) = Preg A ++ Preg B := by
  unfold Preg; simp [List.filter_append]

theorem Yl_cons (e : T) (L : List T) : Yl (e :: L) = if rk e = 2 then e :: Yl L else Yl L := by
  unfold Yl
  by_cases h : rk e = 2 <;> simp [List.filter_cons, h]

theorem Yl_append (A B : List T) : Yl (A ++ B) = Yl A ++ Yl B := by
  unfold Yl; simp [List.filter_append]

theorem Preg_nil_of (L : List T) (h : ∀ e ∈ L, rk e ≠ 1) : Preg L = [] := by
  unfold Preg
  rw [List.filter_eq_nil_iff]
  intro e he; simp [h e he]

theorem Yl_nil_of (L : List T) (h : ∀ e ∈ L, rk e ≠ 2) : Yl L = [] := by
  unfold Yl
  rw [List.filter_eq_nil_iff]
  intro e he; simp [h e he]

theorem Preg_length_le (L : List T) : (Preg L).length ≤ L.length := by
  unfold Preg; exact List.length_filter_le _ _

theorem srt_tail_ge (e : T) (L : List T) (h : srt (e :: L)) : ∀ x ∈ L, rk e ≤ rk x := by
  unfold srt at h; rw [List.pairwise_cons] at h; exact h.1

theorem srt_tail (e : T) (L : List T) (h : srt (e :: L)) : srt L := by
  unfold srt at h ⊢; rw [List.pairwise_cons] at h; exact h.2

/-- Lemma AB, one step -/
theorem ab3_step (a b c : T) (R : List T) (ha : head a = S) (hs : srt (a :: b :: c :: R))
    (h3 : 3 ≤ (Preg (a :: b :: c :: R)).length) : 3 ≤ (Preg (args a ++ c :: app b c :: R)).length := by
  have hab := srt_tail_ge a _ hs b (by simp)
  have hac := srt_tail_ge a _ hs c (by simp)
  have hbc := srt_tail_ge b _ (srt_tail a _ hs) c (by simp)
  have hcR := srt_tail_ge c _ (srt_tail b _ (srt_tail a _ hs))
  rw [Preg_append, List.length_append]
  simp only [Preg_cons] at h3 ⊢
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  rcases rk_cases c with hc | hc | hc
  · have ha0 : rk a = 0 := by omega
    have hb0 : rk b = 0 := by omega
    have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
    simp only [ha0, hb0, hc, hbc0] at h3 ⊢
    simp at h3 ⊢
    omega
  · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
    simp only [hc, hbc1, if_true, List.length_cons] at h3 ⊢
    rcases rk_cases a with ha' | ha' | ha'
    · have hb' : rk b = 0 ∨ rk b = 1 := by omega
      rcases hb' with hb' | hb' <;> simp [ha', hb'] at h3 <;> omega
    · obtain ⟨s, hs', hs1⟩ := P_has_P_arg a ha ha'
      have : 1 ≤ (Preg (args a)).length := by
        unfold Preg
        apply List.length_pos_iff_exists_mem.2
        exact ⟨s, by simp [hs', hs1]⟩
      omega
    · omega
  · -- rk c = 2: every element of R has rank 2, so at most a, b are P
    have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
    rw [hR] at h3
    rcases rk_cases a with ha' | ha' | ha' <;> rcases rk_cases b with hb' | hb' | hb' <;>
      simp [ha', hb', hc] at h3 <;> omega

theorem ab3_pos3 (f b d : T) (R : List T) (hs : srt (f :: b :: d :: R))
    (h3 : 3 ≤ (Preg (f :: b :: d :: R)).length) : rk d ≤ 1 := by
  rcases rk_cases d with hd | hd | hd
  · omega
  · omega
  · exfalso
    have hdR := srt_tail_ge d _ (srt_tail b _ (srt_tail f _ hs))
    have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hdR e he; omega)
    simp only [Preg_cons, hR, hd] at h3
    rcases rk_cases f with hf | hf | hf <;> rcases rk_cases b with hb | hb | hb <;> simp [hf, hb] at h3

theorem ab3_run : ∀ (k : Nat) (L L' : List T), Seg L → 3 ≤ (Preg L).length → run k L = some L' →
    3 ≤ (Preg L').length
  | 0, L, L', _, h3, hr => by simp [run] at hr; subst hr; exact h3
  | k + 1, L, L', hS, h3, hr => by
    obtain ⟨L1, hs, hr1⟩ := run_succ_some k L L' hr
    obtain ⟨a, b, c, R, rfl, ha, rfl⟩ := step_some _ L1 hs
    exact ab3_run k _ L' (seg_step a b c R ha hS) (ab3_step a b c R ha hS.1 h3) hr1

/-- before a proper transfer (a p-front whose third element contains x, y or r) the P-region has <= 2 elements -/
theorem ab3_bound (L1 : List T) (hS : Seg L1) (T' : Nat) (f b d : T) (R : List T)
    (hT : run T' L1 = some (f :: b :: d :: R)) (hd : rk d = 2) :
    ∀ t L, t ≤ T' → run t L1 = some L → (Preg L).length ≤ 2 := by
  intro t L ht hL
  rcases Nat.lt_or_ge (Preg L).length 3 with h3 | h3'
  · omega
  exfalso
  obtain ⟨Lt, hLt, hrest⟩ := run_prefix T' t L1 _ hT ht
  rw [hL] at hLt; injection hLt with hLt; subst hLt
  have hSL : Seg L := seg_run t L1 L hS hL
  have := ab3_run (T' - t) L _ hSL h3' hrest
  have hsT := (seg_run T' L1 _ hS hT).1
  have := ab3_pos3 f b d R hsT this
  omega

/-! ## S1 Part 3: spine and subterm toolkit -/

/-- subterm relation -/
def sub (u : T) : T → Prop
  | S => u = S
  | var n => u = var n
  | app f x => u = app f x ∨ sub u f ∨ sub u x

theorem sub_refl : ∀ t : T, sub t t
  | S => rfl
  | var _ => rfl
  | app _ _ => Or.inl rfl

theorem sub_trans : ∀ (u v t : T), sub u v → sub v t → sub u t
  | u, v, S, h1, h2 => by simp [sub] at h2; subst h2; exact h1
  | u, v, var n, h1, h2 => by simp [sub] at h2; subst h2; exact h1
  | u, v, app f x, h1, h2 => by
    rcases h2 with h2 | h2 | h2
    · subst h2; exact h1
    · exact Or.inr (Or.inl (sub_trans u v f h1 h2))
    · exact Or.inr (Or.inr (sub_trans u v x h1 h2))

theorem sub_left (f x : T) : sub f (app f x) := Or.inr (Or.inl (sub_refl f))
theorem sub_right (f x : T) : sub x (app f x) := Or.inr (Or.inr (sub_refl x))

theorem sub_of_args : ∀ (t s : T), s ∈ args t → sub s t
  | S, s, hs => by simp [args] at hs
  | var _, s, hs => by simp [args] at hs
  | app f x, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact sub_trans s f _ (sub_of_args f s hs) (sub_left f x)
    · subst hs; exact sub_right f s

/-- occurrence counts of subterms are bounded -/
theorem occN_sub_le (n : Nat) : ∀ (u t : T), sub u t → occN n u ≤ occN n t
  | u, S, h => by simp [sub] at h; subst h; exact Nat.le_refl _
  | u, var m, h => by simp [sub] at h; subst h; exact Nat.le_refl _
  | u, app f x, h => by
    rcases h with h | h | h
    · subst h; exact Nat.le_refl _
    · have := occN_sub_le n u f h; simp only [occN]; omega
    · have := occN_sub_le n u x h; simp only [occN]; omega

/-- the rank of an S-headed term is bounded by the ranks of its arguments -/
theorem rk_le_of_args (t : T) (hS : head t = S) (k : Nat) (h : ∀ s ∈ args t, rk s ≤ k) : rk t ≤ k := by
  have hsum : ∀ n, (∀ s ∈ args t, occN n s = 0) → occN n t = 0 := by
    intro n hn
    rw [occN_spine n t hS]
    have : ∀ (l : List T), (∀ s ∈ l, occN n s = 0) → (l.map (occN n)).sum = 0 := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => intro hl; simp [hl a (by simp), ih (fun s hs => hl s (by simp [hs]))]
    exact this _ hn
  have hm : ∀ m, (∀ s ∈ args t, occN m s = 0) → occN m t = 0 := hsum
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have e1 : occN 1 t = 0 := hm 1 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
    have e2 : occN 2 t = 0 := hm 2 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
    have e3 : occN 3 t = 0 := hm 3 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · have e0 : occN 0 t = 0 :=
        hm 0 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
      rcases rk_spec t with h' | h' | h' <;> omega
    · rcases rk_spec t with h' | h' | h' <;> omega
  · have := rk_le2 t; omega

/-- every sorted list of ranks splits as closed ++ P ++ Y -/
theorem srt_split : ∀ (L : List T), srt L → ∃ C P Y, L = C ++ P ++ Y ∧ (∀ e ∈ C, rk e = 0) ∧
    (∀ e ∈ P, rk e = 1) ∧ (∀ e ∈ Y, rk e = 2)
  | [], _ => ⟨[], [], [], by simp, by simp, by simp, by simp⟩
  | e :: L, h => by
    obtain ⟨C, P, Y, hL, hC, hP, hY⟩ := srt_split L (srt_tail e L h)
    have hge := srt_tail_ge e L h
    rcases rk_cases e with he | he | he
    · exact ⟨e :: C, P, Y, by simp [hL], by simp [he]; exact hC, hP, hY⟩
    · have hC0 : C = [] := by
        cases C with
        | nil => rfl
        | cons x C' => exfalso; have := hge x (by simp [hL]); have := hC x (by simp); omega
      exact ⟨[], e :: P, Y, by simp [hL, hC0], by simp, by simp [he]; exact hP, hY⟩
    · have hC0 : C = [] := by
        cases C with
        | nil => rfl
        | cons x C' => exfalso; have := hge x (by simp [hL]); have := hC x (by simp); omega
      have hP0 : P = [] := by
        cases P with
        | nil => rfl
        | cons x P' => exfalso; have := hge x (by simp [hL, hC0]); have := hP x (by simp); omega
      exact ⟨[], [], e :: Y, by simp [hL, hC0, hP0], by simp, by simp, by simp [he]; exact hY⟩

theorem Preg_split (C P Y : List T) (hC : ∀ e ∈ C, rk e = 0) (hP : ∀ e ∈ P, rk e = 1)
    (hY : ∀ e ∈ Y, rk e = 2) : Preg (C ++ P ++ Y) = P := by
  rw [Preg_append, Preg_append, Preg_nil_of C (fun e he => by rw [hC e he]; omega),
    Preg_nil_of Y (fun e he => by rw [hY e he]; omega)]
  unfold Preg
  simp only [List.nil_append, List.append_nil]
  rw [List.filter_eq_self]
  intro e he; simp [hP e he]

theorem Yl_split (C P Y : List T) (hC : ∀ e ∈ C, rk e = 0) (hP : ∀ e ∈ P, rk e = 1)
    (hY : ∀ e ∈ Y, rk e = 2) : Yl (C ++ P ++ Y) = Y := by
  rw [Yl_append, Yl_append, Yl_nil_of C (fun e he => by rw [hC e he]; omega),
    Yl_nil_of P (fun e he => by rw [hP e he]; omega)]
  unfold Yl
  simp only [List.nil_append]
  rw [List.filter_eq_self]
  intro e he; simp [hY e he]

/-- spine prefixes: an argument z of an S-headed term a sits on a left-spine prefix  M.z  of a -/
theorem spine_prefix : ∀ (a : T), head a = S → ∀ (A B : List T) (z : T), args a = A ++ z :: B →
    ∃ M, head M = S ∧ args M = A ∧ sub (app M z) a
  | S, _, A, B, z, h => by simp [args] at h
  | var _, hS, _, _, _, _ => by simp [head] at hS
  | app f x, hS, A, B, z, h => by
    simp only [head] at hS
    simp only [args] at h
    rcases List.eq_nil_or_concat B with hB | ⟨B', y', hB⟩
    · subst hB
      simp at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      exact ⟨f, hS, h1, sub_refl _⟩
    · subst hB
      rw [List.concat_eq_append] at h
      have h' : args f = A ++ z :: B' := by
        have := h
        rw [show A ++ z :: (B' ++ [y']) = (A ++ z :: B') ++ [y'] by simp] at this
        exact (List.append_inj' this rfl).1
      obtain ⟨M, hM, hMA, hsub⟩ := spine_prefix f hS A B' z h'
      exact ⟨M, hM, hMA, sub_trans _ _ _ hsub (sub_left f x)⟩

/-- if z is the LAST argument, a = M.z -/
theorem spine_last (a : T) (hS : head a = S) (A : List T) (z : T) (h : args a = A ++ [z]) :
    ∃ M, head M = S ∧ args M = A ∧ a = app M z := by
  match a, hS, h with
  | S, _, h => simp [args] at h
  | var _, hS, _ => simp [head] at hS
  | app f x, hS, h =>
    simp only [head] at hS
    simp only [args] at h
    have := List.append_inj' h rfl
    obtain ⟨h1, h2⟩ := this
    simp at h2; subst h2
    exact ⟨f, hS, h1, rfl⟩

/-! ## S1 Part 4: Claim C (no 2P term alone in the P-region; no subterm K.Z) -/

/-- a 2P term: an application of two P-terms -/
def twoP : T → Prop
  | app U V => rk U = 1 ∧ rk V = 1
  | _ => False

theorem twoP_rk (Z : T) (h : twoP Z) : rk Z = 1 := by
  match Z, h with
  | app U V, h => rw [rk_app, h.1, h.2]; rfl

/-- no subterm K.Z with K closed and Z a 2P term -/
def noKZ : T → Prop
  | app f x => noKZ f ∧ noKZ x ∧ ¬ (rk f = 0 ∧ twoP x)
  | _ => True

theorem noKZ_sub : ∀ (u t : T), noKZ t → sub u t → noKZ u
  | u, S, _, h => by simp [sub] at h; subst h; trivial
  | u, var n, _, h => by simp [sub] at h; subst h; trivial
  | u, app f x, hn, h => by
    rcases h with h | h | h
    · subst h; exact hn
    · exact noKZ_sub u f hn.1 h
    · exact noKZ_sub u x hn.2.1 h

def IC1 (L : List T) : Prop := ∀ Z, Preg L = [Z] → ¬ twoP Z
def IC2 (L : List T) : Prop := ∀ e ∈ L, noKZ e

/-- the first P-argument of a noKZ term is not 2P -/
theorem first_P_arg_not2P (a : T) (hS : head a = S) (ho : ordT a) (hn : noKZ a) (Z : T) (rest : List T)
    (hP : Preg (args a) = Z :: rest) : ¬ twoP Z := by
  intro hZ
  obtain ⟨C, P, Y, hs, hC, hPP, hY⟩ := srt_split (args a) (ordT_srt a ho hS)
  have hPe : Preg (args a) = P := by rw [hs]; exact Preg_split C P Y hC hPP hY
  rw [hPe] at hP; subst hP
  obtain ⟨M, hM, hMA, hsub⟩ := spine_prefix a hS C (rest ++ Y) Z (by rw [hs]; simp)
  have hM0 : rk M ≤ 0 := rk_le_of_args M hM 0 (fun s hs' => by rw [hMA] at hs'; exact Nat.le_of_eq (hC s hs'))
  have := noKZ_sub _ _ hn hsub
  exact this.2.2 ⟨by omega, hZ⟩

theorem srt3 (a b c : T) (R : List T) (h : srt (a :: b :: c :: R)) :
    rk a ≤ rk b ∧ rk b ≤ rk c ∧ ∀ x ∈ R, rk c ≤ rk x :=
  ⟨srt_tail_ge a _ h b (by simp), srt_tail_ge b _ (srt_tail a _ h) c (by simp),
   srt_tail_ge c _ (srt_tail b _ (srt_tail a _ h))⟩

theorem Preg_args_closed (a : T) (ha : rk a = 0) : Preg (args a) = [] :=
  Preg_nil_of _ (fun e he => by have := rk_args_le a e he; omega)

theorem Yl_args_le1 (a : T) (ha : rk a ≤ 1) : Yl (args a) = [] :=
  Yl_nil_of _ (fun e he => by have := rk_args_le a e he; omega)

theorem ic_step (a b c : T) (R : List T) (ha : head a = S) (hseg : Seg (a :: b :: c :: R))
    (h2 : (Preg (a :: b :: c :: R)).length ≤ 2) (h2' : (Preg (args a ++ c :: app b c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hc2 : IC2 (a :: b :: c :: R)) :
    IC1 (args a ++ c :: app b c :: R) ∧ IC2 (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hna : noKZ a := hc2 a (by simp)
  have hoa : ordT a := hseg.2 a (by simp)
  refine ⟨?_, ?_⟩
  · intro Z hZ hZ2
    rw [Preg_append] at hZ
    simp only [Preg_cons] at hZ h2
    rcases rk_cases c with hc | hc | hc
    · have ha0 : rk a = 0 := by omega
      have hb0 : rk b = 0 := by omega
      have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
      rw [Preg_args_closed a ha0] at hZ
      simp only [hc, hbc0] at hZ
      simp at hZ
      apply hc1 Z _ hZ2
      simp only [Preg_cons, ha0, hb0, hc]; simpa using hZ
    · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      simp only [hc, hbc1, if_true] at hZ
      have := congrArg List.length hZ
      simp at this
      omega
    · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
      have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
      simp only [hc, hbc2, hR] at hZ
      simp at hZ
      exact first_P_arg_not2P a ha hoa hna Z [] hZ hZ2
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact noKZ_sub e a hna (sub_of_args a e he)
    · rw [he]; exact hc2 c (by simp)
    · rw [he]
      refine ⟨hc2 b (by simp), hc2 c (by simp), ?_⟩
      rintro ⟨hb0, hc2P⟩
      have hc1' : rk c = 1 := twoP_rk c hc2P
      have ha0 : rk a = 0 := by omega
      have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      rw [Preg_append, Preg_args_closed a ha0] at h2'
      simp only [Preg_cons, hc1', hbc1, if_true, List.nil_append, List.length_cons] at h2'
      have hR : Preg R = [] := List.eq_nil_of_length_eq_zero (by omega)
      apply hc1 c _ hc2P
      simp only [Preg_cons, ha0, hb0, hc1', hR]; simp
    · exact hc2 e (by simp [he])

/-! ## S1 Part 5: FI-W (every pair-top above w and every P-prefix applied to w lies in the X-sequence of c0) -/

/-- U is the unique P-argument of the S-headed term M -/
def onlyP (M U : T) : Prop := head M = S ∧ Preg (args M) = [U]

/-- the X-sequence: X_0 = c0, X_{i+1} = the unique P-argument of X_i -/
inductive inX (c0 : T) : T → Prop
  | base : inX c0 c0
  | next (M U : T) : inX c0 M → onlyP M U → inX c0 U

def wsubOK (w c0 : T) : T → Prop
  | app f x => wsubOK w c0 f ∧ wsubOK w c0 x ∧ (x = w → rk f = 1 → inX c0 f)
  | _ => True

theorem wsubOK_sub (w c0 : T) : ∀ (u t : T), wsubOK w c0 t → sub u t → wsubOK w c0 u
  | u, S, _, h => by simp [sub] at h; subst h; trivial
  | u, var n, _, h => by simp [sub] at h; subst h; trivial
  | u, app f x, hn, h => by
    rcases h with h | h | h
    · subst h; exact hn
    · exact wsubOK_sub w c0 u f hn.1 h
    · exact wsubOK_sub w c0 u x hn.2.1 h

def IW (w c0 : T) (L : List T) : Prop := (∀ e ∈ L, wsubOK w c0 e) ∧ (∀ U, Preg L = [U, w] → inX c0 U)

/-- releasing the P-pair [U, z] from an S-headed front: the prefix M.z with M's unique P-argument U -/
theorem release_pair (a : T) (hS : head a = S) (ho : ordT a) (U z : T) (hP : Preg (args a) = [U, z]) :
    ∃ M, head M = S ∧ rk M = 1 ∧ onlyP M U ∧ sub (app M z) a ∧
      ∃ C Y, args a = C ++ U :: z :: Y ∧ args M = C ++ [U] ∧ (∀ e ∈ C, rk e = 0) ∧ (∀ e ∈ Y, rk e = 2) := by
  obtain ⟨C, P, Y, hs, hC, hPP, hY⟩ := srt_split (args a) (ordT_srt a ho hS)
  have hPe : Preg (args a) = P := by rw [hs]; exact Preg_split C P Y hC hPP hY
  rw [hPe] at hP; subst hP
  have hU : rk U = 1 := hPP U (by simp)
  obtain ⟨M, hM, hMA, hsub⟩ := spine_prefix a hS (C ++ [U]) Y z (by rw [hs]; simp)
  have hMle : rk M ≤ 1 := rk_le_of_args M hM 1 (fun s hs' => by
    rw [hMA] at hs'; simp at hs'
    rcases hs' with hs' | hs'
    · rw [hC s hs']; omega
    · rw [hs']; omega)
  have hMge : 1 ≤ rk M := by
    have := rk_args_le M U (by rw [hMA]; simp); omega
  refine ⟨M, hM, by omega, ⟨hM, ?_⟩, hsub, C, Y, by rw [hs]; simp, hMA, hC, hY⟩
  rw [hMA]
  have := Preg_split C [U] [] hC (by simp [hU]) (by simp)
  simpa using this

theorem iw_step (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1) (a b c : T) (R : List T) (ha : head a = S)
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (hiw : IW w c0 (a :: b :: c :: R)) : IW w c0 (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hoa : ordT a := hseg.2 a (by simp)
  have hwa : wsubOK w c0 a := hiw.1 a (by simp)
  refine ⟨?_, ?_⟩
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact wsubOK_sub w c0 e a hwa (sub_of_args a e he)
    · rw [he]; exact hiw.1 c (by simp)
    · rw [he]
      refine ⟨hiw.1 b (by simp), hiw.1 c (by simp), ?_⟩
      intro hcw hb1
      subst hcw
      have ha0 : rk a ≠ 1 := by
        intro ha1
        simp only [Preg_cons, ha1, hb1, hwr, if_true, List.length_cons] at h2; omega
      have ha0' : rk a = 0 := by omega
      have hR : Preg R = [] := by
        have h2'' := h2
        simp [Preg_cons, ha0', hb1, hwr] at h2''
        first | exact h2'' | exact List.eq_nil_of_length_eq_zero (by omega)
      apply hiw.2 b
      simp [Preg_cons, ha0', hb1, hwr, hR]
    · exact hiw.1 e (by simp [he])
  · intro U hU
    rw [Preg_append] at hU
    rcases rk_cases c with hc | hc | hc
    · have ha0 : rk a = 0 := by omega
      have hb0 : rk b = 0 := by omega
      have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
      rw [Preg_args_closed a ha0] at hU
      simp only [Preg_cons, hc, hbc0] at hU
      apply hiw.2 U
      simp only [Preg_cons, ha0, hb0, hc]; simpa using hU
    · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      have ha0 : rk a = 0 := by
        rcases rk_cases a with h | h | h
        · exact h
        · exfalso
          have hb1 : rk b = 1 := by omega
          simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
        · omega
      rw [Preg_args_closed a ha0] at hU
      simp only [Preg_cons, hc, hbc1, if_true, List.nil_append] at hU
      have h1 := List.cons.inj hU
      have h2' := List.cons.inj h1.2
      have hbcw : app b c = w := h2'.1
      rw [hw] at hbcw
      injection hbcw with _ hcc
      rw [← h1.1, hcc]
      exact inX.base
    · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
      have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
      simp only [Preg_cons, hc, hbc2, hR] at hU
      simp at hU
      obtain ⟨M, _, hM1, hMU, hsub, _⟩ := release_pair a ha hoa U w hU
      have hwM := wsubOK_sub w c0 _ a hwa hsub
      exact inX.next M U (hwM.2.2 rfl hM1) hMU

/-! ## S1 Part 6: FI-A (2P terms in the P-region over the bare y were created over the bare y) -/

/-- U.V was created at some time s <= t by a step with the bare y as Y-top: run s L1 = k :: U :: V :: y :: R -/
def Good (L1 : List T) (t : Nat) (U V : T) : Prop :=
  ∃ s, s ≤ t ∧ ∃ k R, run s L1 = some (k :: U :: V :: var 2 :: R)

/-- every 2P term on the right spine of a term is Good -/
def rsg (L1 : List T) (t : Nat) : T → Prop
  | app U V => (rk U = 1 ∧ rk V = 1) → (Good L1 t U V ∧ rsg L1 t V)
  | _ => True

theorem rsg_mono (L1 : List T) (t t' : Nat) (htt : t ≤ t') : ∀ Z, rsg L1 t Z → rsg L1 t' Z
  | S, _ => trivial
  | var _, _ => trivial
  | app U V, h => by
    intro hUV
    obtain ⟨⟨s, hs, hk⟩, hr⟩ := h hUV
    exact ⟨⟨s, by omega, hk⟩, rsg_mono L1 t t' htt V hr⟩

theorem rsg_of_not2P (L1 : List T) (t : Nat) (Z : T) (h : ¬ twoP Z) : rsg L1 t Z := by
  match Z, h with
  | S, _ => trivial
  | var _, _ => trivial
  | app U V, h => intro hUV; exact absurd hUV h

def IA (L1 : List T) (t : Nat) (L : List T) : Prop :=
  ∀ Z, twoP Z → ((Z ∈ Preg L ∧ Ytop L = some (var 2)) ∨ (∃ e ∈ L, sub (app Z (var 2)) e)) → rsg L1 t Z

/-- releasing a 2P term as the LOWER element of a P-pair: the front is M'.Z (P-front) or (M'.Z).y'... -/
theorem pair_prefix (a : T) (hS : head a = S) (ho : ordT a) (V' Z : T) (hP : Preg (args a) = [V', Z]) :
    ∃ M', rk M' = 1 ∧ (Yl (args a) = [] → a = app M' Z) ∧
      (∀ y' Y', Yl (args a) = y' :: Y' → sub (app (app M' Z) y') a) := by
  obtain ⟨C, P, Y, hs, hC, hPP, hY⟩ := srt_split (args a) (ordT_srt a ho hS)
  have hPe : Preg (args a) = P := by rw [hs]; exact Preg_split C P Y hC hPP hY
  have hYe : Yl (args a) = Y := by rw [hs]; exact Yl_split C P Y hC hPP hY
  rw [hPe] at hP; subst hP
  have hV : rk V' = 1 := hPP V' (by simp)
  -- the prefix with arguments C ++ [V']
  obtain ⟨M', hM', hMA', _⟩ := spine_prefix a hS (C ++ [V']) Y Z (by rw [hs]; simp)
  have hMle : rk M' ≤ 1 := rk_le_of_args M' hM' 1 (fun s hs' => by
    rw [hMA'] at hs'; simp at hs'
    rcases hs' with hs' | hs'
    · rw [hC s hs']; omega
    · rw [hs']; omega)
  have hMge : 1 ≤ rk M' := by have := rk_args_le M' V' (by rw [hMA']; simp); omega
  refine ⟨M', by omega, ?_, ?_⟩
  · intro hY0
    rw [hYe] at hY0; subst hY0
    obtain ⟨M2, hM2, hMA2, ha⟩ := spine_last a hS (C ++ [V']) Z (by rw [hs]; simp)
    -- M2 and M' have the same spine, hence are equal
    have : M2 = M' := by
      have key : ∀ (m1 m2 : T), head m1 = S → head m2 = S → args m1 = args m2 → m1 = m2 := by
        intro m1; induction m1 with
        | S => intro m2 _ h2 he
               match m2, h2, he with
               | S, _, _ => rfl
               | var _, h2, _ => simp [head] at h2
               | app f x, _, he => simp [args] at he
        | var _ => intro m2 h1; simp [head] at h1
        | app f x ihf _ =>
          intro m2 h1 h2 he
          match m2, h2, he with
          | S, _, he => simp [args] at he
          | var _, h2, _ => simp [head] at h2
          | app g z, h2, he =>
            simp only [args] at he
            have := List.append_inj' he rfl
            simp at this
            rw [ihf g (by simpa [head] using h1) (by simpa [head] using h2) this.1, this.2]
      exact key M2 M' hM2 hM' (by rw [hMA2, hMA'])
    rw [ha, this]
  · intro y' Y' hY'
    rw [hYe] at hY'; subst hY'
    obtain ⟨M2, hM2, hMA2, hsub⟩ := spine_prefix a hS (C ++ [V', Z]) Y' y' (by rw [hs]; try simp)
    obtain ⟨M3, hM3, hMA3, hM2e⟩ := spine_last M2 hM2 (C ++ [V']) Z (by rw [hMA2]; simp)
    have key : ∀ (m1 m2 : T), head m1 = S → head m2 = S → args m1 = args m2 → m1 = m2 := by
      intro m1; induction m1 with
      | S => intro m2 _ h2 he
             match m2, h2, he with
             | S, _, _ => rfl
             | var _, h2, _ => simp [head] at h2
             | app f x, _, he => simp [args] at he
      | var _ => intro m2 h1; simp [head] at h1
      | app f x ihf _ =>
        intro m2 h1 h2 he
        match m2, h2, he with
        | S, _, he => simp [args] at he
        | var _, h2, _ => simp [head] at h2
        | app g z, h2, he =>
          simp only [args] at he
          have := List.append_inj' he rfl
          simp at this
          rw [ihf g (by simpa [head] using h1) (by simpa [head] using h2) this.1, this.2]
    have : M3 = M' := key M3 M' hM3 hM' (by rw [hMA3, hMA'])
    rw [hM2e, this] at hsub
    exact hsub

theorem Ytop_third (a b c : T) (R : List T) (ha : rk a ≤ 1) (hb : rk b ≤ 1) (hc : rk c = 2) :
    Ytop (a :: b :: c :: R) = some c := by
  unfold Ytop
  simp only [Yl_cons]
  have ha' : rk a ≠ 2 := by omega
  have hb' : rk b ≠ 2 := by omega
  simp [ha', hb', hc]

theorem Yl_args_ne_nil (a : T) (hS : head a = S) (ha : rk a = 2) : Yl (args a) ≠ [] := by
  intro h
  have : rk a ≤ 1 := rk_le_of_args a hS 1 (fun s hs => by
    rcases rk_cases s with h' | h' | h'
    · omega
    · omega
    · exfalso
      have : s ∈ Yl (args a) := by unfold Yl; simp [hs, h']
      rw [h] at this; simp at this)
  omega

/-- a list of length <= 2 containing Z -/
theorem mem_short (P : List T) (Z : T) (hZ : Z ∈ P) (hl : P.length ≤ 2) :
    P = [Z] ∨ (∃ V, P = [Z, V]) ∨ (∃ V, P = [V, Z]) := by
  match P, hZ, hl with
  | [x], hZ, _ => simp at hZ; subst hZ; exact Or.inl rfl
  | [x1, x2], hZ, _ =>
    simp at hZ
    rcases hZ with h | h
    · subst h; exact Or.inr (Or.inl ⟨x2, rfl⟩)
    · subst h; exact Or.inr (Or.inr ⟨x1, rfl⟩)
  | _ :: _ :: _ :: _, _, hl => simp at hl

theorem rk_var2 : rk (var 2) = 2 := by unfold rk; simp [occN]

theorem ia_step (L1 : List T) (t : Nat) (a b c : T) (R : List T) (ha : head a = S)
    (hrun : run t L1 = some (a :: b :: c :: R))
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (h2' : (Preg (args a ++ c :: app b c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hc2 : IC2 (a :: b :: c :: R))
    (hc1' : IC1 (args a ++ c :: app b c :: R))
    (hia : IA L1 t (a :: b :: c :: R)) : IA L1 (t + 1) (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hna : noKZ a := hc2 a (by simp)
  have hoa : ordT a := hseg.2 a (by simp)
  have mono : ∀ Z, rsg L1 t Z → rsg L1 (t + 1) Z := rsg_mono L1 t (t + 1) (by omega)
  intro Z hZ hcase
  rcases hcase with ⟨hZin, hY⟩ | ⟨e, he, hsub⟩
  · rw [Preg_append] at hZin
    unfold Ytop at hY
    rw [Yl_append] at hY
    rcases rk_cases c with hc | hc | hc
    · have ha0 : rk a = 0 := by omega
      have hb0 : rk b = 0 := by omega
      have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
      rw [Preg_args_closed a ha0] at hZin
      rw [Yl_args_le1 a (by omega)] at hY
      simp only [Preg_cons, Yl_cons, hc, hbc0] at hZin hY
      simp at hZin hY
      apply mono; apply hia Z hZ; left
      refine ⟨by simp only [Preg_cons, ha0, hb0, hc]; simpa using hZin, ?_⟩
      unfold Ytop; simp only [Yl_cons, ha0, hb0, hc]; simpa using hY
    · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      have ha0 : rk a = 0 := by
        rcases rk_cases a with h | h | h
        · exact h
        · exfalso
          have hb1 : rk b = 1 := by omega
          simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
        · omega
      rw [Preg_args_closed a ha0] at hZin
      rw [Yl_args_le1 a (by omega)] at hY
      have hc2' : rk c ≠ 2 := by omega
      have hbc2 : rk (app b c) ≠ 2 := by omega
      simp only [Preg_cons, Yl_cons, hc, hbc1, hc2', hbc2, if_true, if_false, List.nil_append] at hZin hY
      simp at hY
      have hYL : Ytop (a :: b :: c :: R) = some (var 2) := by
        unfold Ytop; simp only [Yl_cons]
        have ha2 : rk a ≠ 2 := by omega
        have hb2 : rk b ≠ 2 := by omega
        simp [ha2, hb2, hc2', hY]
      simp at hZin
      rcases hZin with hZc | hZbc | hZR
      · subst hZc
        apply mono; apply hia Z hZ; left
        refine ⟨?_, hYL⟩
        simp only [Preg_cons, ha0, hc]
        by_cases hb1 : rk b = 1 <;> simp [hb1]
      · subst hZbc
        obtain ⟨hb1, _⟩ := hZ
        intro _
        have hR : Preg R = [] := by
          have h2'' := h2
          simp [Preg_cons, ha0, hb1, hc] at h2''
          first | exact h2'' | exact List.eq_nil_of_length_eq_zero (by omega)
        have hR2 : ∀ x ∈ R, rk x = 2 := by
          intro x hx
          have := hcR x hx
          rcases rk_cases x with h | h | h
          · omega
          · exfalso
            have : x ∈ Preg R := by unfold Preg; simp [hx, h]
            rw [hR] at this; simp at this
          · exact h
        have hYR : Yl R = R := by
          unfold Yl; rw [List.filter_eq_self]; intro x hx; simp [hR2 x hx]
        rw [hYR] at hY
        obtain ⟨R', hR'⟩ : ∃ R', R = var 2 :: R' := by
          match R, hY with
          | x :: R', hY => simp at hY; exact ⟨R', by rw [hY]⟩
        refine ⟨⟨t, by omega, a, R', by rw [hrun, hR']⟩, ?_⟩
        by_cases h2c : twoP c
        · apply mono; apply hia c h2c; left
          exact ⟨by simp only [Preg_cons, ha0, hb1, hc]; simp, hYL⟩
        · exact rsg_of_not2P L1 (t + 1) c h2c
      · apply mono; apply hia Z hZ; left
        refine ⟨?_, hYL⟩
        simp only [Preg_cons, ha0, hc]
        by_cases hb1 : rk b = 1 <;> simp [hb1, hZR]
    · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
      have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
      have hPL' : Preg (args a ++ c :: app b c :: R) = Preg (args a) := by
        rw [Preg_append]; simp only [Preg_cons, hc, hbc2, hR]; simp
      simp only [Preg_cons, hc, hbc2, hR] at hZin
      simp at hZin
      have hlen : (Preg (args a)).length ≤ 2 := by rw [← hPL']; exact h2'
      rcases rk_cases a with ha' | ha' | ha'
      · rw [Preg_args_closed a ha'] at hZin; simp at hZin
      · -- P-front
        rw [Yl_args_le1 a (by omega)] at hY
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        rcases mem_short _ Z hZin hlen with hP | ⟨V', hP⟩ | ⟨V', hP⟩
        · exact absurd hZ (hc1' Z (by rw [hPL', hP]))
        · exact absurd hZ (first_P_arg_not2P a ha hoa hna Z [V'] hP)
        · obtain ⟨M', hM'1, haM, _⟩ := pair_prefix a ha hoa V' Z hP
          have haeq : a = app M' Z := haM (Yl_args_le1 a (by omega))
          have hZ1 : rk Z = 1 := twoP_rk Z hZ
          have h2a : twoP a := by rw [haeq]; exact ⟨hM'1, hZ1⟩
          have hb1 : rk b = 1 := by
            rcases rk_cases b with h | h | h
            · omega
            · exact h
            · exfalso
              apply hc1 a _ h2a
              have hb2 : rk b ≠ 1 := by omega
              have hc2' : rk c ≠ 1 := by omega
              simp only [Preg_cons, ha', hb2, hc2', hR]; simp
          have hYL : Ytop (a :: b :: c :: R) = some (var 2) := by
            rw [Ytop_third a b c R (by omega) (by omega) hc, hY]
          have := hia a h2a (Or.inl ⟨by simp only [Preg_cons, ha']; simp, hYL⟩)
          rw [haeq] at this
          exact mono Z (this ⟨hM'1, hZ1⟩).2
      · -- Y-front
        obtain ⟨y', Y', hYa⟩ : ∃ y' Y', Yl (args a) = y' :: Y' := by
          have hne := Yl_args_ne_nil a ha ha'
          cases h : Yl (args a) with
          | nil => exact absurd h hne
          | cons y' Y' => exact ⟨y', Y', rfl⟩
        rw [hYa] at hY
        simp at hY
        subst hY
        rcases mem_short _ Z hZin hlen with hP | ⟨V', hP⟩ | ⟨V', hP⟩
        · exact absurd hZ (hc1' Z (by rw [hPL', hP]))
        · exact absurd hZ (first_P_arg_not2P a ha hoa hna Z [V'] hP)
        · obtain ⟨M', hM'1, _, hsubA⟩ := pair_prefix a ha hoa V' Z hP
          have h2M : twoP (app M' Z) := ⟨hM'1, twoP_rk Z hZ⟩
          have := hia (app M' Z) h2M (Or.inr ⟨a, by simp, hsubA _ _ hYa⟩)
          exact mono Z (this h2M).2
  · simp at he
    rcases he with he | he | he | he
    · exact mono Z (hia Z hZ (Or.inr ⟨a, by simp, sub_trans _ _ _ hsub (sub_of_args a e he)⟩))
    · rw [he] at hsub; exact mono Z (hia Z hZ (Or.inr ⟨c, by simp, hsub⟩))
    · rw [he] at hsub
      rcases hsub with h | h | h
      · injection h with hZb hyc
        subst hZb; subst hyc
        have hb1 : rk Z = 1 := twoP_rk Z hZ
        apply mono; apply hia Z hZ; left
        refine ⟨?_, Ytop_third a Z (var 2) R (by omega) (by omega) rk_var2⟩
        simp only [Preg_cons, hb1]
        by_cases ha1 : rk a = 1 <;> simp [ha1]
      · exact mono Z (hia Z hZ (Or.inr ⟨b, by simp, h⟩))
      · exact mono Z (hia Z hZ (Or.inr ⟨c, by simp, h⟩))
    · exact mono Z (hia Z hZ (Or.inr ⟨e, by simp [he], hsub⟩))

/-! ## S1 Part 7: FI-B, the main induction and the structural theorem (S1) -/

theorem spine_eq : ∀ (m1 m2 : T), head m1 = S → head m2 = S → args m1 = args m2 → m1 = m2
  | S, S, _, _, _ => rfl
  | S, var _, _, h2, _ => by simp [head] at h2
  | S, app f x, _, _, he => by simp [args] at he
  | var _, _, h1, _, _ => by simp [head] at h1
  | app f x, S, _, _, he => by simp [args] at he
  | app f x, var _, _, h2, _ => by simp [head] at h2
  | app f x, app g z, h1, h2, he => by
    simp only [args] at he
    have := List.append_inj' he rfl
    simp at this
    rw [spine_eq f g (by simpa [head] using h1) (by simpa [head] using h2) this.1, this.2]

/-- (S1) has occurred by time t: some list args(c0) ++ [w, y | B] -/
def S1occ (L1 : List T) (t : Nat) (c0 w : T) : Prop :=
  ∃ s, s ≤ t ∧ ∃ B, run s L1 = some (args c0 ++ w :: var 2 :: B)

def IB (L1 : List T) (w c0 : T) (t : Nat) (L : List T) : Prop :=
  ∀ U, Preg L = [U, w] → inX c0 U → U ≠ c0 → Ytop L = some (var 2) → S1occ L1 t c0 w

theorem run_succ_of (L1 : List T) (t : Nat) (L L' : List T) (h : run t L1 = some L) (hs : step L = some L') :
    run (t + 1) L1 = some L' := by
  rw [run_add t 1, h]; simp [run, hs]

theorem run_succ_split (L1 : List T) (t : Nat) (L' : List T) (h : run (t + 1) L1 = some L') :
    ∃ L, run t L1 = some L ∧ step L = some L' := by
  rw [run_add t 1] at h
  cases hr : run t L1 with
  | none => rw [hr] at h; simp at h
  | some L =>
    rw [hr] at h
    simp only [Option.bind_some, run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L2 =>
      rw [hs] at h
      simp at h
      exact ⟨L, rfl, by rw [hs, h]⟩

/-- at a GOOD time the P-region is the pair [M, w] over the bare y -/
theorem good_pair (k M w : T) (R : List T) (hS : Seg (k :: M :: w :: var 2 :: R))
    (h2 : (Preg (k :: M :: w :: var 2 :: R)).length ≤ 2) (hM : rk M = 1) (hw : rk w = 1) :
    Preg (k :: M :: w :: var 2 :: R) = [M, w] ∧ Ytop (k :: M :: w :: var 2 :: R) = some (var 2) := by
  have hkM := srt_tail_ge k _ hS.1 M (by simp)
  have hyR := srt_tail_ge (var 2) R (srt_tail w _ (srt_tail M _ (srt_tail k _ hS.1)))
  rw [rk_var2] at hyR
  have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hyR e he; omega)
  have hk0 : rk k = 0 := by
    rcases rk_cases k with h | h | h
    · exact h
    · exfalso; simp only [Preg_cons, h, hM, hw, if_true, List.length_cons] at h2; omega
    · omega
  have hk2 : rk k ≠ 2 := by omega
  have hM2 : rk M ≠ 2 := by omega
  have hw2 : rk w ≠ 2 := by omega
  refine ⟨?_, ?_⟩
  · simp only [Preg_cons, hk0, hM, hw, rk_var2, hR]; simp
  · unfold Ytop; simp only [Yl_cons, hk2, hM2, hw2, rk_var2]; simp

theorem ib_step (L1 : List T) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1) (t : Nat)
    (a b c : T) (R : List T) (ha : head a = S) (hrun : run t L1 = some (a :: b :: c :: R))
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hiw : IW w c0 (a :: b :: c :: R)) (hia : IA L1 t (a :: b :: c :: R))
    (hist : ∀ s Ls, s ≤ t → run s L1 = some Ls → IB L1 w c0 s Ls)
    (hbound : ∀ s Ls, s ≤ t → run s L1 = some Ls → (Preg Ls).length ≤ 2)
    (hsegs : ∀ s Ls, run s L1 = some Ls → Seg Ls) :
    IB L1 w c0 (t + 1) (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hoa : ordT a := hseg.2 a (by simp)
  have hwa : wsubOK w c0 a := hiw.1 a (by simp)
  have hstep : step (a :: b :: c :: R) = some (args a ++ c :: app b c :: R) := by simp [step, ha]
  have hrun' := run_succ_of L1 t _ _ hrun hstep
  have mono : S1occ L1 t c0 w → S1occ L1 (t + 1) c0 w := by
    rintro ⟨s, hs, B, hB⟩; exact ⟨s, by omega, B, hB⟩
  have monoS : ∀ s, s ≤ t → S1occ L1 s c0 w → S1occ L1 (t + 1) c0 w := by
    rintro s hst ⟨s', hs', B, hB⟩; exact ⟨s', by omega, B, hB⟩
  -- from a GOOD pair [M, w] at an earlier time to (S1)
  have fromGood : ∀ M, rk M = 1 → inX c0 M → M ≠ c0 → Good L1 t M w → S1occ L1 (t + 1) c0 w := by
    rintro M hM1 hXM hMc ⟨s, hs, k, R', hks⟩
    have hSs := hsegs s _ hks
    obtain ⟨hPs, hYs⟩ := good_pair k M w R' hSs (hbound s _ hs hks) hM1 hwr
    exact monoS s hs (hist s _ hs hks M hPs hXM hMc hYs)
  intro U hU hX hne hY
  have hU0 := hU
  rw [Preg_append] at hU
  rcases rk_cases c with hc | hc | hc
  · have ha0 : rk a = 0 := by omega
    have hb0 : rk b = 0 := by omega
    have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
    rw [Preg_args_closed a ha0] at hU
    simp only [Preg_cons, hc, hbc0] at hU
    apply mono
    apply hist t _ (Nat.le_refl t) hrun U _ hX hne
    · unfold Ytop at hY ⊢
      rw [Yl_append, Yl_args_le1 a (by omega)] at hY
      simp only [Yl_cons, ha0, hb0, hc, hbc0] at hY ⊢
      simpa using hY
    · simp only [Preg_cons, ha0, hb0, hc]; simpa using hU
  · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
    have ha0 : rk a = 0 := by
      rcases rk_cases a with h | h | h
      · exact h
      · exfalso
        have hb1 : rk b = 1 := by omega
        simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
      · omega
    rw [Preg_args_closed a ha0] at hU
    simp only [Preg_cons, hc, hbc1, if_true, List.nil_append] at hU
    have h1 := List.cons.inj hU
    have h2' := List.cons.inj h1.2
    have hbcw : app b c = w := h2'.1
    rw [hw] at hbcw
    injection hbcw with _ hcc
    exact absurd (by rw [← h1.1, hcc]) hne
  · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
    have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
    simp only [Preg_cons, hc, hbc2, hR] at hU
    simp at hU
    obtain ⟨M, hMS, hM1, hMU, hsub, C, Y, hargs, hMA, hC, hYY⟩ := release_pair a ha hoa U w hU
    have hXM : inX c0 M := (wsubOK_sub w c0 _ a hwa hsub).2.2 rfl hM1
    have hU1 : rk U = 1 := by
      have : U ∈ Preg (args a) := by rw [hU]; simp
      unfold Preg at this; simp at this; exact this.2
    have hYa : Yl (args a) = Y := by
      rw [hargs]
      have := Yl_split C [U, w] Y hC (by simp [hU1, hwr]) hYY
      simpa using this
    by_cases hMc : M = c0
    · -- the front has prefix c0.w: (S1) right now
      subst hMc
      refine ⟨t + 1, Nat.le_refl _, ?_⟩
      have hL' : args a ++ c :: app b c :: R = args M ++ w :: (Y ++ c :: app b c :: R) := by
        rw [hargs, hMA]; simp
      unfold Ytop at hY
      rw [Yl_append, hYa] at hY
      cases Y with
      | nil =>
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        subst hY
        exact ⟨app b (var 2) :: R, by rw [hrun', hL']; simp⟩
      | cons y' Y' =>
        simp at hY
        subst hY
        exact ⟨Y' ++ c :: app b c :: R, by rw [hrun', hL']; simp⟩
    · rcases rk_cases a with ha' | ha' | ha'
      · rw [Preg_args_closed a ha'] at hU; simp at hU
      · -- P-front a = M.w over the bare y
        have hY0 : Y = [] := by rw [← hYa]; exact Yl_args_le1 a (by omega)
        subst hY0
        obtain ⟨M2, hM2S, hM2A, haeq⟩ := spine_last a ha (C ++ [U]) w (by rw [hargs]; simp)
        have hM2 : M2 = M := spine_eq M2 M hM2S hMS (by rw [hM2A, hMA])
        rw [hM2] at haeq
        have h2a : twoP a := by rw [haeq]; exact ⟨hM1, hwr⟩
        have hb1 : rk b = 1 := by
          rcases rk_cases b with h | h | h
          · omega
          · exact h
          · exfalso
            apply hc1 a _ h2a
            have hb2 : rk b ≠ 1 := by omega
            have hc2' : rk c ≠ 1 := by omega
            simp only [Preg_cons, ha', hb2, hc2', hR]; simp
        unfold Ytop at hY
        rw [Yl_append, hYa] at hY
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        have hYL : Ytop (a :: b :: c :: R) = some (var 2) := by
          rw [Ytop_third a b c R (by omega) (by omega) hc, hY]
        have hr := hia a h2a (Or.inl ⟨by simp only [Preg_cons, ha']; simp, hYL⟩)
        rw [haeq] at hr
        exact fromGood M hM1 hXM hMc (hr ⟨hM1, hwr⟩).1
      · -- Y-front (M.w).y ...
        unfold Ytop at hY
        rw [Yl_append, hYa] at hY
        cases Y with
        | nil => exact absurd hYa (Yl_args_ne_nil a ha ha')
        | cons y' Y' =>
          simp at hY
          subst hY
          obtain ⟨M2, hM2S, hM2A, hsub2⟩ := spine_prefix a ha (C ++ [U, w]) Y' (var 2) (by rw [hargs]; simp)
          obtain ⟨M3, hM3S, hM3A, hM2e⟩ := spine_last M2 hM2S (C ++ [U]) w (by rw [hM2A]; simp)
          have hM3 : M3 = M := spine_eq M3 M hM3S hMS (by rw [hM3A, hMA])
          rw [hM2e, hM3] at hsub2
          have h2M : twoP (app M w) := ⟨hM1, hwr⟩
          have hr := hia (app M w) h2M (Or.inr ⟨a, by simp, hsub2⟩)
          exact fromGood M hM1 hXM hMc (hr h2M).1

/-! base case: a start list with at most one occurrence of p in total -/

theorem occN0_of_rk1 (t : T) (h : rk t = 1) : 1 ≤ occN 0 t := by
  have := (rk_eq1 t).1 h; omega

theorem twoP_occ (Z : T) (h : twoP Z) : 2 ≤ occN 0 Z := by
  match Z, h with
  | app U V, h =>
    have := occN0_of_rk1 U h.1; have := occN0_of_rk1 V h.2
    simp only [occN]; omega

theorem noKZ_of_le1 : ∀ e : T, occN 0 e ≤ 1 → noKZ e
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    simp only [occN] at h
    refine ⟨noKZ_of_le1 f (by omega), noKZ_of_le1 x (by omega), ?_⟩
    rintro ⟨_, hx⟩
    have := twoP_occ x hx; omega

theorem wsubOK_of_le1 (w c0 : T) (hwr : rk w = 1) : ∀ e : T, occN 0 e ≤ 1 → wsubOK w c0 e
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    simp only [occN] at h
    refine ⟨wsubOK_of_le1 w c0 hwr f (by omega), wsubOK_of_le1 w c0 hwr x (by omega), ?_⟩
    intro hxw hf
    subst hxw
    have := occN0_of_rk1 f hf; have := occN0_of_rk1 x hwr; omega

theorem Preg_len_le_occ : ∀ L : List T, (Preg L).length ≤ (L.map (occN 0)).sum
  | [] => by simp [Preg]
  | e :: L => by
    rw [Preg_cons]
    have := Preg_len_le_occ L
    by_cases h : rk e = 1
    · have := occN0_of_rk1 e h; simp [h]; omega
    · simp [h]; omega

theorem mem_occ_le (L : List T) (e : T) (he : e ∈ L) : occN 0 e ≤ (L.map (occN 0)).sum := by
  induction L with
  | nil => simp at he
  | cons x L ih =>
    simp at he
    rcases he with he | he
    · subst he; simp
    · have := ih he; simp; omega

theorem s1_base (L1 : List T) (w c0 : T) (hwr : rk w = 1) (hp : (L1.map (occN 0)).sum ≤ 1) :
    IC1 L1 ∧ IC2 L1 ∧ IW w c0 L1 ∧ IA L1 0 L1 ∧ IB L1 w c0 0 L1 := by
  have hel : ∀ e ∈ L1, occN 0 e ≤ 1 := fun e he => by have := mem_occ_le L1 e he; omega
  have hlen : (Preg L1).length ≤ 1 := by have := Preg_len_le_occ L1; omega
  refine ⟨?_, fun e he => noKZ_of_le1 e (hel e he), ⟨fun e he => wsubOK_of_le1 w c0 hwr e (hel e he), ?_⟩, ?_, ?_⟩
  · intro Z hZ h2Z
    have hZm : Z ∈ L1 := by
      have : Z ∈ Preg L1 := by rw [hZ]; simp
      unfold Preg at this; simp at this; exact this.1
    have := hel Z hZm; have := twoP_occ Z h2Z; omega
  · intro U hU; rw [hU] at hlen; simp at hlen
  · intro Z h2Z hcase
    exfalso
    rcases hcase with ⟨hZm, _⟩ | ⟨e, he, hsub⟩
    · have : Z ∈ L1 := by unfold Preg at hZm; simp at hZm; exact hZm.1
      have := hel Z this; have := twoP_occ Z h2Z; omega
    · have h1 := occN_sub_le 0 _ _ hsub
      have := hel e he; have := twoP_occ Z h2Z
      simp only [occN] at h1; omega
  · intro U hU; rw [hU] at hlen; simp at hlen

/-- the invariants hold at every time up to tmax -/
theorem s1_inv (L1 : List T) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1)
    (hS : Seg L1) (hp : (L1.map (occN 0)).sum ≤ 1) (tmax : Nat)
    (hbound : ∀ s Ls, s ≤ tmax → run s L1 = some Ls → (Preg Ls).length ≤ 2) :
    ∀ t, t ≤ tmax → ∀ s Ls, s ≤ t → run s L1 = some Ls →
      IC1 Ls ∧ IC2 Ls ∧ IW w c0 Ls ∧ IA L1 s Ls ∧ IB L1 w c0 s Ls := by
  have hsegs : ∀ s Ls, run s L1 = some Ls → Seg Ls := fun s Ls h => seg_run s L1 Ls hS h
  intro t
  induction t with
  | zero =>
    intro _ s Ls hs hr
    have : s = 0 := by omega
    subst this
    simp [run] at hr
    rw [← hr]
    exact s1_base L1 w c0 hwr hp
  | succ t ih =>
    intro ht s Ls hs hr
    rcases Nat.lt_or_ge s (t + 1) with hst | hst
    · exact ih (by omega) s Ls (by omega) hr
    · have hs1 : s = t + 1 := by omega
      subst hs1
      obtain ⟨L, hL, hstep⟩ := run_succ_split L1 t Ls hr
      obtain ⟨a, b, c, R, rfl, ha, rfl⟩ := step_some L _ hstep
      obtain ⟨hc1, hc2, hiw, hia, _⟩ := ih (by omega) t _ (Nat.le_refl t) hL
      have hseg := hsegs t _ hL
      have h2 := hbound t _ (by omega) hL
      have h2' := hbound (t + 1) _ ht hr
      obtain ⟨hc1', hc2'⟩ := ic_step a b c R ha hseg h2 h2' hc1 hc2
      refine ⟨hc1', hc2', iw_step w b0 c0 hw hwr a b c R ha hseg h2 hiw,
        ia_step L1 t a b c R ha hL hseg h2 h2' hc1 hc2 hc1' hia, ?_⟩
      exact ib_step L1 w b0 c0 hw hwr t a b c R ha hL hseg h2 hc1 hiw hia
        (fun s' Ls' hs' hr' => (ih (by omega) s' Ls' hs' hr').2.2.2.2)
        (fun s' Ls' hs' hr' => hbound s' Ls' (by omega) hr') hsegs

/-- **THEOREM S1 (structural claim, generic form).**  Let a run start from a list L1 that is rank-sorted with
    hereditarily sorted spines (Seg) and contains at most ONE occurrence of p in total, and let it reach, at time T',
    a list whose third element contains x, y or r (e.g. a proper transfer).  If at a time tg <= T' the run passes
    through a glue list a1 :: w :: y :: R0 with w = b0.c0 a P-term and a1 a P-term different from c0, then at some
    time s <= tg the run passes through args(c0) ++ w :: y :: B ('c0 runs on (w, y)'). -/
theorem s1_core (L1 : List T) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1)
    (hS : Seg L1) (hp : (L1.map (occN 0)).sum ≤ 1)
    (T' : Nat) (f b d : T) (R : List T) (hT : run T' L1 = some (f :: b :: d :: R)) (hd : rk d = 2)
    (tg : Nat) (htg : tg ≤ T') (a1 : T) (R0 : List T) (hg : run tg L1 = some (a1 :: w :: var 2 :: R0))
    (ha1 : rk a1 = 1) (hne : a1 ≠ c0) :
    ∃ s, s ≤ tg ∧ ∃ B, run s L1 = some (args c0 ++ w :: var 2 :: B) := by
  have hbound : ∀ s Ls, s ≤ T' → run s L1 = some Ls → (Preg Ls).length ≤ 2 :=
    fun s Ls hs hr => ab3_bound L1 hS T' f b d R hT hd s Ls hs hr
  obtain ⟨_, _, hiw, _, hib⟩ := s1_inv L1 w b0 c0 hw hwr hS hp T' hbound tg htg tg _ (Nat.le_refl _) hg
  have hSg := seg_run tg L1 _ hS hg
  have hyR := srt_tail_ge (var 2) R0 (srt_tail w _ (srt_tail a1 _ hSg.1))
  rw [rk_var2] at hyR
  have hR0 : Preg R0 = [] := Preg_nil_of R0 (fun e he => by have := hyR e he; omega)
  have hP : Preg (a1 :: w :: var 2 :: R0) = [a1, w] := by
    simp only [Preg_cons, ha1, hwr, rk_var2, hR0]; simp
  have hY : Ytop (a1 :: w :: var 2 :: R0) = some (var 2) := by
    have h1 : rk a1 ≠ 2 := by omega
    have h2 : rk w ≠ 2 := by omega
    unfold Ytop; simp only [Yl_cons, h1, h2, rk_var2]; simp
  exact hib a1 hP (hiw.2 a1 hP) hne hY

#print axioms s1_core
#print axioms s1_inv
#print axioms ab3_bound

/-! ## S1 Part 8: the single-wrapper consequences for phase 2 from an ordered single-occurrence datum -/

theorem occ2_eq : ∀ t : T, occ2 t = occN 2 t
  | S => rfl
  | var n => by simp [occ2, occN]
  | app f x => by simp [occ2, occN, occ2_eq f, occ2_eq x]

/-- an atom absent from every element stays absent along the run -/
theorem occ_run_zero (h : Nat) : ∀ (k : Nat) (L L' : List T), (∀ e ∈ L, occN h e = 0) → run k L = some L' →
    ∀ e ∈ L', occN h e = 0
  | 0, L, L', hz, hr => by simp [run] at hr; subst hr; exact hz
  | k + 1, L, L', hz, hr => by
    obtain ⟨L1, hs, hr1⟩ := run_succ_some k L L' hr
    obtain ⟨a, b, c, R, rfl, ha, rfl⟩ := step_some _ L1 hs
    apply occ_run_zero h k _ L' _ hr1
    intro e he
    simp at he
    rcases he with he | he | he | he
    · exact occN_args h a (hz a (by simp)) e he
    · rw [he]; exact hz c (by simp)
    · rw [he]; simp only [occN]; rw [hz b (by simp), hz c (by simp)]
    · exact hz e (by simp [he])

/-- a node U.V that is not a subterm of the start list is created by a step [a, U, V | R] -/
theorem creation (U V : T) : ∀ (T' : Nat) (L0 L : List T), run T' L0 = some L → (∃ e ∈ L, sub (app U V) e) →
    (∀ e ∈ L0, ¬ sub (app U V) e) → ∃ t, t < T' ∧ ∃ a R', run t L0 = some (a :: U :: V :: R')
  | 0, L0, L, hr, hL, h0 => by
    simp [run] at hr; subst hr
    obtain ⟨e, he, hs⟩ := hL; exact absurd hs (h0 e he)
  | T' + 1, L0, L, hr, hL, h0 => by
    obtain ⟨L', hL', hstep⟩ := run_succ_split L0 T' L hr
    by_cases hin : ∃ e ∈ L', sub (app U V) e
    · obtain ⟨t, ht, a, R', h⟩ := creation U V T' L0 L' hL' hin h0
      exact ⟨t, by omega, a, R', h⟩
    · obtain ⟨a, b, c, R, rfl, ha, rfl⟩ := step_some L' L hstep
      obtain ⟨e, he, hs⟩ := hL
      simp at he
      rcases he with he | he | he | he
      · exact absurd ⟨a, by simp, sub_trans _ _ _ hs (sub_of_args a e he)⟩ hin
      · rw [he] at hs; exact absurd ⟨c, by simp, hs⟩ hin
      · rw [he] at hs
        rcases hs with hs | hs | hs
        · injection hs with hU hV
          subst hU; subst hV
          exact ⟨T', by omega, a, R, hL'⟩
        · exact absurd ⟨b, by simp, hs⟩ hin
        · exact absurd ⟨c, by simp, hs⟩ hin
      · exact absurd ⟨e, by simp [he], hs⟩ hin

/-- a list from which the run continues has an S-headed front -/
theorem head_of_continue (L0 : List T) (t T' : Nat) (a b c : T) (R : List T)
    (ht : run t L0 = some (a :: b :: c :: R)) (htT : t < T') (L' : List T) (hT : run T' L0 = some L') :
    head a = S := by
  obtain ⟨Lt, hLt, hrest⟩ := run_prefix T' t L0 L' hT (by omega)
  rw [ht] at hLt; injection hLt with hLt; subst hLt
  have hk : T' - t = (T' - t - 1) + 1 := by omega
  rw [hk] at hrest
  obtain ⟨L2, hs, _⟩ := run_succ_some _ _ _ hrest
  obtain ⟨a', b', c', R', he, ha', _⟩ := step_some _ L2 hs
  injection he with h1; rw [h1]; exact ha'

theorem rk_le1_of (t : T) (h1 : occN 1 t = 0) (h2 : occN 2 t = 0) (h3 : occN 3 t = 0) : rk t ≤ 1 := by
  rcases rk_spec t with h | h | h <;> omega

theorem rk_xy : rk (app (var 1) (var 2)) = 2 := by unfold rk; simp [occN]
theorem rk_var3 : rk (var 3) = 2 := by unfold rk; simp [occN]

/-- the first list of phase 2 is segment-sorted and carries the datum's single p -/
theorem phase2_start (D : T) (hDS : head D = S) (hDo : ordT D) (hD1 : occN 1 D = 0) (hD2 : occN 2 D = 0)
    (hD3 : occN 3 D = 0) :
    Seg (args D ++ [var 2, app (var 1) (var 2), var 3]) ∧
      ((args D ++ [var 2, app (var 1) (var 2), var 3]).map (occN 0)).sum = occN 0 D := by
  have hDr : rk D ≤ 1 := rk_le1_of D hD1 hD2 hD3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold srt
    rw [List.pairwise_append]
    refine ⟨ordT_srt D hDo hDS, ?_, ?_⟩
    · simp [rk_var2, rk_xy, rk_var3]
    · intro x hx y hy
      have := rk_args_le D x hx
      simp at hy
      rcases hy with hy | hy | hy <;> subst hy
      · rw [rk_var2]; omega
      · rw [rk_xy]; omega
      · rw [rk_var3]; omega
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact ordT_args D hDo e he
    · subst he; trivial
    · subst he; exact ⟨trivial, trivial, by intro h; simp [head] at h⟩
    · subst he; trivial
  · rw [occN_spine 0 D hDS]; simp [occN]

theorem phase2_shift (D : T) (hDS : head D = S) (t : Nat) :
    run (t + 1) [D, var 1, var 2, var 3] = run t (args D ++ [var 2, app (var 1) (var 2), var 3]) := by
  simp [run, step, hDS]

/-- **THEOREM R3-SINGLE (single wrapper, ordered single-occurrence datum).**  Let D be S-headed, ordered (`ordT`),
    free of x, y, r, with at most one occurrence of p, and let phase 2 reach a p-front whose third element is the
    single-wrapper handler w.y, w = b0.c0 free of x, y, r with b0, c0 S-headed.  Then, provided c0 satisfies the
    handler-only condition H1ok, the next phase (datum w[p:=c].p') never makes a proper transfer: every p'-front has
    a y-free element or the bare y at position 3.  Proof: the node w.y was created by a glue [a1, w, y]; if a1 = c0
    this is pattern alpha (alpha_main), if a1 is closed it is CLOSEDGLUE (closedglue_main), and otherwise a1 is a
    P-term != c0 and THEOREM S1 (s1_core) shows that phase 2 ran c0 on (w, y) before, so BETA0 (beta_main) applies.
    H1ok is used only in the last case. -/
theorem r3_single (D b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : 4 ≤ h1) (hh2 : 4 ≤ h2)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H)
    (hDS : head D = S) (hDo : ordT D) (hD1 : occN 1 D = 0) (hD2 : occN 2 D = 0) (hD3 : occN 3 D = 0)
    (hDp : occN 0 D ≤ 1) (hDh1 : occN h1 D = 0) (hDh2 : occN h2 D = 0)
    (hb0S : head b0 = S) (hc0S : head c0 = S) (hw1 : occN 1 (app b0 c0) = 0) (hw2 : occN 2 (app b0 c0) = 0)
    (hw3 : occN 3 (app b0 c0) = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (T' : Nat) (f b : T) (R : List T)
    (hT : run T' [D, var 1, var 2, var 3] = some (f :: b :: app (app b0 c0) (var 2) :: R)) (hf : head f = var 0)
    (hH1 : ∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R')) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  have hh1' : h1 ≠ 0 := by omega
  have hh2' : h2 ≠ 0 := by omega
  -- basic facts about w
  have hw2' : occN 2 b0 = 0 ∧ occN 2 c0 = 0 := by simp only [occN] at hw2; omega
  have hy0 : occ2 b0 = 0 := by rw [occ2_eq]; exact hw2'.1
  have hy1 : occ2 c0 = 0 := by rw [occ2_eq]; exact hw2'.2
  -- fresh hole atoms stay absent along phase 2
  have hz : ∀ hh, 4 ≤ hh → occN hh D = 0 → ∀ (k : Nat) (L : List T), run k [D, var 1, var 2, var 3] = some L →
      ∀ e ∈ L, occN hh e = 0 := by
    intro hh h4 hD k L hk
    apply occ_run_zero hh k _ L _ hk
    intro e he
    simp at he
    rcases he with he | he | he | he <;> subst he
    · exact hD
    · simp [occN]; omega
    · simp [occN]; omega
    · simp [occN]; omega
  have hTm : app (app b0 c0) (var 2) ∈ f :: b :: app (app b0 c0) (var 2) :: R := by simp
  have hc0f1 : occN h1 c0 = 0 := by
    have := hz h1 hh1 hDh1 T' _ hT _ hTm
    simp only [occN] at this; omega
  have hc0f2 : occN h2 c0 = 0 := by
    have := hz h2 hh2 hDh2 T' _ hT _ hTm
    simp only [occN] at this; omega
  -- the glue that created the handler node w.y
  obtain ⟨tg, htg, a1, R0, hg⟩ := creation (app b0 c0) (var 2) T' _ _ hT
    ⟨_, hTm, sub_refl _⟩ (by
      intro e he hs
      simp at he
      rcases he with he | he | he | he <;> subst he
      · have := occN_sub_le 2 _ _ hs; simp [occN] at this; omega
      · simp [sub] at hs
      · simp [sub] at hs
      · simp [sub] at hs)
  have ha1S : head a1 = S := head_of_continue _ tg T' a1 _ _ R0 hg htg _ hT
  -- the glue is not the start list
  have htg1 : 1 ≤ tg := by
    rcases Nat.eq_zero_or_pos tg with h0 | h0
    · subst h0; simp [run] at hg
    · exact h0
  obtain ⟨hSeg, hocc⟩ := phase2_start D hDS hDo hD1 hD2 hD3
  have hg1 : run (tg - 1) (args D ++ [var 2, app (var 1) (var 2), var 3]) = some (a1 :: app b0 c0 :: var 2 :: R0) := by
    rw [← phase2_shift D hDS (tg - 1), show tg - 1 + 1 = tg by omega]; exact hg
  have hT1 : run (T' - 1) (args D ++ [var 2, app (var 1) (var 2), var 3]) = some (f :: b :: app (app b0 c0) (var 2) :: R) := by
    rw [← phase2_shift D hDS (T' - 1), show T' - 1 + 1 = T' by omega]; exact hT
  have hSg := seg_run _ _ _ hSeg hg1
  have hrank : rk a1 ≤ rk (app b0 c0) := srt_tail_ge a1 _ hSg.1 _ (by simp)
  have hwr : rk (app b0 c0) ≤ 1 := rk_le1_of _ hw1 hw2 hw3
  have ha1f1 : occN h1 a1 = 0 := hz h1 hh1 hDh1 tg _ hg a1 (by simp)
  have ha1f2 : occN h2 a1 = 0 := hz h2 hh2 hDh2 tg _ hg a1 (by simp)
  by_cases hac : a1 = c0
  · -- pattern alpha
    subst hac
    exact alpha_main b0 a1 c h1 h2 H hc hc2 hh1' hh2' h12 hH hb0S hc0S hy0 hy1 hc0f1 hc0f2 hV _ tg T' R0 hg htg
      f b _ R hT hf
  · rcases rk_cases a1 with ha0 | ha1 | ha2
    · -- closed glue front
      have ha10 : occN 0 a1 = 0 := ((rk_eq0 a1).1 ha0).2
      have hno := closedglue_main a1 (app b0 c0) c h1 h2 H hc hh1' hh2' h12 hH ha1S ha10 (by simp [head, hb0S])
        ha1f1 ha1f2 hV _ tg T' R0 hg htg f b _ R hT hf
      have hD3' : asub (sg3 c) (app (app b0 c0) (var 2)) = app (app (sb c b0) (sb c c0)) (var 0) := by
        simp [asub, asub_sg3_sb c b0 hy0, asub_sg3_sb c c0 hy1, sg3]
      intro m f' b' d' R' hm hf'
      rw [← hD3'] at hm
      exact absurd hf' (hno m f' _ hm)
    · -- P-front different from c0: THEOREM S1, then BETA0
      have hw1r : rk (app b0 c0) = 1 := by omega
      obtain ⟨s, hs, B, hsB⟩ := s1_core _ (app b0 c0) b0 c0 rfl hw1r hSeg (by rw [hocc]; exact hDp)
        (T' - 1) f b _ R hT1 (by rw [rk_app, rk_var2]; omega) (tg - 1) (by omega) a1 R0 hg1 ha1 hac
      have hs0 : run (s + 1) [D, var 1, var 2, var 3] = some (args c0 ++ app b0 c0 :: var 2 :: B) := by
        rw [phase2_shift D hDS s]; exact hsB
      exact beta_main b0 c0 c h1 h2 H hc hc2 hh1' hh2' h12 hH hb0S hc0S hy0 hy1 hc0f1 hc0f2 hV _ (s + 1) T' B hs0
        (by omega) f b _ R hT hf hH1
    · omega

#print axioms s1_core
#print axioms r3_single

/-! non-vacuity check: a concrete pattern-beta datum satisfies every hypothesis of r3_single -/
def exD : T := app (app (app S (app S (app S S))) S) (app S (app S (var 0)))
def exc0 : T := app S (app S (var 0))

example : run 6 [exD, var 1, var 2, var 3] = some [var 0, var 2, app (app S exc0) (var 2), app (app (app S exc0) (app exc0 (app S exc0))) (var 2), app (var 1) (var 2), var 3] := by
  decide

theorem exD_ordT : ordT exD := by
  simp [exD, ordT, args, head, rk, occN]

theorem exc0_H1ok (h1 h2 : Nat) (hh1 : 4 ≤ h1) (hh2 : 4 ≤ h2) :
    ∀ (k : Nat) (g : T) (L : List T), run k (args exc0 ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R') := by
  intro k g L hk hg
  rcases k with _ | _ | k
  · simp [run, exc0, args] at hk
    obtain ⟨rfl, -⟩ := hk
    simp [head] at hg
  · simp [run, step, exc0, args, head] at hk
    obtain ⟨rfl, -⟩ := hk
    simp [head] at hg; omega
  · exfalso
    simp [run, step, exc0, args, head] at hk

/-- non-vacuity: r3_single applies to the pattern-beta datum S(S(SS))S(S(Sp)) (glue front Sp != c0 = S(Sp)) -/
theorem r3_single_example : ∀ (m : Nat) (f' b' d' : T) (R' : List T),
    run m [app (app (sb 4 S) (sb 4 exc0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
    head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 :=
  r3_single exD S exc0 4 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) exD_ordT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide⟩
    6 (var 0) (var 2) [app (app (app S exc0) (app exc0 (app S exc0))) (var 2), app (var 1) (var 2), var 3]
    (by decide) (by decide) (exc0_H1ok 5 6 (by decide) (by decide))

#print axioms r3_single_example

/-! ## S1 Part 9: THEOREM PAXB (handler-only): if b0 never calls its FIRST hole, the next phase is safe -/

/-- the next-phase image of b0's two-hole run: p -> c, k1 -> c0', k2 -> p' (= var 0), other atoms fixed -/
def tauB (c k1 k2 : Nat) (c0' : T) : Nat → T := fun n =>
  if n = 0 then var c else if n = k1 then c0' else if n = k2 then var 0 else var n

theorem asub_tauB_sb (c k1 k2 : Nat) (c0' : T) (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) :
    ∀ t : T, occN k1 t = 0 → occN k2 t = 0 → asub (tauB c k1 k2 c0') t = sb c t
  | S, _, _ => by simp [asub, sb]
  | var n, ha, hb => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, tauB]
    · have n1 : n ≠ k1 := by intro e; subst e; simp [occN] at ha
      have n2 : n ≠ k2 := by intro e; subst e; simp [occN] at hb
      simp [asub, sb, tauB, h0, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, sb, asub_tauB_sb c k1 k2 c0' hk1 hk2 f (by omega) (by omega),
      asub_tauB_sb c k1 k2 c0' hk1 hk2 x (by omega) (by omega)]

theorem occ2_asub_tauB (c k1 k2 : Nat) (c0' : T) (hc2 : c ≠ 2) (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hk12 : k1 ≠ k2)
    (h0' : occ2 c0' = 0) : ∀ t : T, occ2 t = 0 → occ2 (asub (tauB c k1 k2 c0') t) = 0
  | S, _ => by simp [asub, occ2]
  | var n, h => by
    have hn : n ≠ 2 := by intro e; subst e; simp [occ2] at h
    by_cases h0 : n = 0
    · subst h0; simp [asub, tauB, occ2, hc2]
    · by_cases h1 : n = k1
      · subst h1; simp [asub, tauB, hk1, h0']
      · by_cases h2 : n = k2
        · subst h2; simp [asub, tauB, hk2, hk12.symm, occ2]
        · simp [asub, tauB, h0, h1, h2, occ2, hn]
  | app f x, h => by
    simp only [occ2] at h
    simp only [asub, occ2]
    rw [occ2_asub_tauB c k1 k2 c0' hc2 hk1 hk2 hk12 h0' f (by omega),
      occ2_asub_tauB c k1 k2 c0' hc2 hk1 hk2 hk12 h0' x (by omega)]

theorem head_asub_tauB (c k1 k2 : Nat) (c0' : T) (hc : c ≠ 0) (hc0' : head c0' = S) (hk1 : k1 ≠ 0)
    (hk12 : k1 ≠ k2) : ∀ g : T, head (asub (tauB c k1 k2 c0') g) = var 0 → head g = var k2
  | S, h => by simp [asub, head] at h
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, tauB, head] at h; exact absurd h hc
    · by_cases h1 : n = k1
      · subst h1; simp [asub, tauB, hk1, hc0'] at h
      · by_cases h2 : n = k2
        · subst h2; rfl
        · exfalso; simp [asub, tauB, h0, h1, h2, head] at h
  | app f x, h => by
    simp only [asub, head] at h ⊢
    exact head_asub_tauB c k1 k2 c0' hc hc0' hk1 hk12 f h

theorem nHB_two_first (h1 h2 : Nat) (g e : T) (h : 2 ≤ nHB h1 h2 [g, e]) : isHB h1 h2 g = true := by
  simp only [nHB] at h
  cases hg : isHB h1 h2 g <;> cases he : isHB h1 h2 e <;> simp [hg, he] at h ⊢

/-- the next phase follows b0's two-hole run as long as b0 never calls its first hole -/
theorem paxb_corr (b0 : T) (c k1 k2 : Nat) (c0' : T) (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) (hk12 : k1 ≠ k2) (hc0' : head c0' = S)
    (hNK1 : ∀ (m : Nat) (g : T) (L : List T), run m (args b0 ++ [var k1, var k2]) = some (g :: L) → head g ≠ var k1) :
    ∀ (j : Nat) (L' : List T),
      run j ((args b0 ++ [var k1, var k2]).map (asub (tauB c k1 k2 c0')) ++ [var 2, app (var 1) (var 2), var 3]) = some L' →
      ∃ Aj, run j (args b0 ++ [var k1, var k2]) = some Aj ∧
        L' = Aj.map (asub (tauB c k1 k2 c0')) ++ [var 2, app (var 1) (var 2), var 3] := by
  intro j
  induction j with
  | zero =>
    intro L' h
    refine ⟨_, rfl, ?_⟩
    simp only [run, Option.some.injEq] at h
    exact h.symm
  | succ j ih =>
    intro L' h
    obtain ⟨L'', hL'', hs⟩ := run_succ_split _ j L' h
    obtain ⟨Aj, hAj, hL''e⟩ := ih L'' hL''
    have hnb : 2 ≤ nHB k1 k2 Aj := by
      have := nHB_run k1 k2 j _ _ hAj
      have h0 : 2 ≤ nHB k1 k2 (args b0 ++ [var k1, var k2]) := by
        rw [nHB_append]
        have : nHB k1 k2 [var k1, var k2] = 2 := by simp [nHB, isHB, head]
        omega
      omega
    rw [hL''e] at hs
    obtain ⟨a, b, d, R, hlist, haS, hL'⟩ := step_some _ L' hs
    match Aj, hnb, hlist, hAj with
    | [], hnb, _, _ => simp [nHB] at hnb
    | [g], hnb, _, _ => have := nHB_le_length k1 k2 [g]; simp at this; omega
    | [g, e2], hnb, hlist, hAj =>
      exfalso
      have hg : isHB k1 k2 g = true := nHB_two_first k1 k2 g e2 hnb
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at hlist
      obtain ⟨hga, _⟩ := hlist
      unfold isHB at hg
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
      rcases hg with hg | hg
      · exact hNK1 j g [e2] hAj hg
      · rw [← hga, asub_headvar _ k2 g hg] at haS
        have : tauB c k1 k2 c0' k2 = var 0 := by simp [tauB, hk12.symm, hk2]
        rw [this] at haS; simp [head] at haS
    | g :: e2 :: e3 :: rest, _, hlist, hAj =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hlist
      obtain ⟨hga, hgb, hgd, hR⟩ := hlist
      have hgS : head g = S := by
        rcases head_cases g with hg | ⟨n, hn⟩
        · exact hg
        · exfalso
          rw [← hga, asub_headvar _ n g hn] at haS
          by_cases h1 : n = k1
          · subst h1; exact hNK1 j g _ hAj hn
          · have : head (tauB c k1 k2 c0' n) ≠ S := by
              simp only [tauB]
              by_cases h0 : n = 0
              · rw [if_pos h0]; simp [head]
              · by_cases h2 : n = k2
                · rw [if_neg h0, if_neg h1, if_pos h2]; simp [head]
                · rw [if_neg h0, if_neg h1, if_neg h2]; simp [head]
            exact this haS
      have hstepA : step (g :: e2 :: e3 :: rest) = some (args g ++ e3 :: app e2 e3 :: rest) := by
        simp [step, hgS]
      refine ⟨args g ++ e3 :: app e2 e3 :: rest, run_succ_of (args b0 ++ [var k1, var k2]) j _ _ hAj hstepA, ?_⟩
      rw [hL', ← hga, ← hgb, ← hgd, ← hR]
      rw [asub_args _ g hgS]
      simp [asub]

/-- **THEOREM PAXB.**  Single wrapper w = b0.c0 (b0, c0 S-headed, y-free).  If the two-hole run of b0
    (args(b0) ++ [k1, k2], k1, k2 fresh) never reaches a k1-headed front - b0 never calls its first argument, so the
    next phase never runs c0' - then every p'-headed front of the next phase has a y-free element or the bare y at
    position 3.  (A handler-only condition on b0; no hypothesis on the earlier phase.) -/
theorem paxb_main (b0 c0 : T) (c k1 k2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hk1 : 4 ≤ k1) (hk2 : 4 ≤ k2)
    (hk12 : k1 ≠ k2) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN k1 b0 = 0) (hf2 : occN k2 b0 = 0)
    (hNK1 : ∀ (m : Nat) (g : T) (L : List T), run m (args b0 ++ [var k1, var k2]) = some (g :: L) →
      head g ≠ var k1) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hk1' : k1 ≠ 0 := by omega
  have hk2' : k2 ≠ 0 := by omega
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hA : (args b0 ++ [var k1, var k2]).map (asub (tauB c k1 k2 (sb c c0))) =
      args (sb c b0) ++ [sb c c0, var 0] := by
    rw [sb_args c b0 hb0S]
    simp only [List.map_append, List.map_cons, List.map_nil]
    have hargs : (args b0).map (asub (tauB c k1 k2 (sb c c0))) = (args b0).map (sb c) := by
      apply List.map_congr_left
      intro s hs
      exact asub_tauB_sb c k1 k2 (sb c c0) hk1' hk2' s (occN_args k1 b0 hf1 s hs) (occN_args k2 b0 hf2 s hs)
    rw [hargs]
    simp [asub, tauB, hk1', hk2', hk12.symm]
  have hstep0 : step [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] =
      some (args (sb c b0) ++ [sb c c0, var 0] ++ [var 2, app (var 1) (var 2), var 3]) := by
    simp [step, head, hb0', args]
  match m, hm with
  | 0, hm =>
    simp [run] at hm
    rw [← hm.1] at hf; simp [head, hb0'] at hf
  | m' + 1, hm =>
    simp only [run, hstep0] at hm
    rw [← hA] at hm
    obtain ⟨Aj, hAj, hLe⟩ := paxb_corr b0 c k1 k2 (sb c c0) hk1' hk2' hk12 hc0' hNK1 m' _ hm
    have hnb : 2 ≤ nHB k1 k2 Aj := by
      have := nHB_run k1 k2 m' _ _ hAj
      have h0 : 2 ≤ nHB k1 k2 (args b0 ++ [var k1, var k2]) := by
        rw [nHB_append]
        have : nHB k1 k2 [var k1, var k2] = 2 := by simp [nHB, isHB, head]
        omega
      omega
    have hy2A : ∀ e ∈ Aj, occ2 e = 0 := by
      have hz := occ_run_zero 2 m' _ Aj (by
        intro e he
        simp at he
        rcases he with he | he | he
        · rw [← occ2_eq]; exact occ2_args b0 hy0 e he
        · subst he; simp [occN]; omega
        · subst he; simp [occN]; omega) hAj
      intro e he; rw [occ2_eq]; exact hz e he
    match Aj, hnb, hLe, hy2A with
    | [], hnb, _, _ => simp [nHB] at hnb
    | [g], hnb, _, _ => have := nHB_le_length k1 k2 [g]; simp at this; omega
    | [g, e2], _, hLe, _ =>
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at hLe
      right; exact hLe.2.2.1
    | g :: e2 :: e3 :: rest, _, hLe, hy2A =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hLe
      left
      rw [hLe.2.2.1]
      exact occ2_asub_tauB c k1 k2 (sb c c0) hc2 hk1' hk2' hk12 hy1' e3 (hy2A e3 (by simp))

/-- **THEOREM R3-SINGLE' (`r3_single2`).**  As r3_single, with the handler-only condition weakened to
    'H1ok(c0) OR b0 never calls its first hole' (in the latter case PAXB applies with no phase-2 hypothesis). -/
theorem r3_single2 (D b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : 4 ≤ h1) (hh2 : 4 ≤ h2)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H)
    (hDS : head D = S) (hDo : ordT D) (hD1 : occN 1 D = 0) (hD2 : occN 2 D = 0) (hD3 : occN 3 D = 0)
    (hDp : occN 0 D ≤ 1) (hDh1 : occN h1 D = 0) (hDh2 : occN h2 D = 0)
    (hb0S : head b0 = S) (hc0S : head c0 = S) (hw1 : occN 1 (app b0 c0) = 0) (hw2 : occN 2 (app b0 c0) = 0)
    (hw3 : occN 3 (app b0 c0) = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (T' : Nat) (f b : T) (R : List T)
    (hT : run T' [D, var 1, var 2, var 3] = some (f :: b :: app (app b0 c0) (var 2) :: R)) (hf : head f = var 0)
    (hcond : (∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R')) ∨
      (∀ (m : Nat) (g : T) (L : List T), run m (args b0 ++ [var h1, var h2]) = some (g :: L) → head g ≠ var h1)) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  rcases hcond with hH1 | hNK1
  · exact r3_single D b0 c0 c h1 h2 H hc hc2 hh1 hh2 h12 hH hDS hDo hD1 hD2 hD3 hDp hDh1 hDh2 hb0S hc0S hw1 hw2
      hw3 hV T' f b R hT hf hH1
  · -- fresh holes are absent from b0 (it is part of the handler, built from D, x, y, r)
    have hz : ∀ hh, 4 ≤ hh → occN hh D = 0 → occN hh b0 = 0 := by
      intro hh h4 hD
      have hzr := occ_run_zero hh T' _ _ (by
        intro e he
        simp at he
        rcases he with he | he | he | he <;> subst he
        · exact hD
        · simp [occN]; omega
        · simp [occN]; omega
        · simp [occN]; omega) hT (app (app b0 c0) (var 2)) (by simp)
      simp only [occN] at hzr; omega
    have hy0 : occ2 b0 = 0 := by rw [occ2_eq]; simp only [occN] at hw2; omega
    have hy1 : occ2 c0 = 0 := by rw [occ2_eq]; simp only [occN] at hw2; omega
    exact paxb_main b0 c0 c h1 h2 hc hc2 hh1 hh2 h12 hb0S hc0S hy0 hy1 (hz h1 hh1 hDh1) (hz h2 hh2 hDh2) hNK1

#print axioms paxb_main
#print axioms r3_single2

/-! ## S1 Part 10: LEMMA YT (pair chain), machine-checked.
    With rank-sorted lists and |P| <= 2, a two-element P-region [U, V] with closed code above and Y-top Yt evolves
    only by chain steps [X, Z] -> [Z, X.Z] until the run reaches [E_j, E_{j+1}, Yt | R] (E_0 = U, E_1 = V,
    E_{j+2} = E_j.E_{j+1}); opening E_j there keeps |P| <= 2 only for j <= 3 (S-headed U, V). -/

def chainE (U V : T) : Nat → T
  | 0 => U
  | 1 => V
  | n + 2 => app (chainE U V n) (chainE U V (n + 1))

theorem chainE_rk (U V : T) (hU : rk U = 1) (hV : rk V = 1) : ∀ n, rk (chainE U V n) = 1
  | 0 => hU
  | 1 => hV
  | n + 2 => by
    simp only [chainE]
    rw [rk_app, chainE_rk U V hU hV n, chainE_rk U V hU hV (n + 1)]; rfl

/-- the run proceeds by closed-code steps and chain steps until the pair is at the front -/
theorem yt_chain (L1 : List T) (hS : Seg L1) (T' : Nat) (f b d : T) (RT : List T)
    (hT : run T' L1 = some (f :: b :: d :: RT)) (hd : rk d = 2)
    (hbound : ∀ s Ls, s ≤ T' → run s L1 = some Ls → (Preg Ls).length ≤ 2)
    (U V Yt : T) (R : List T) (hU : rk U = 1) (hV : rk V = 1) :
    ∀ (n : Nat) (t j : Nat) (K : List T), T' - t = n → t ≤ T' → (∀ k ∈ K, rk k = 0) →
      run t L1 = some (K ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) →
      ∃ t' j', t ≤ t' ∧ t' ≤ T' ∧ run t' L1 = some (chainE U V j' :: chainE U V (j' + 1) :: Yt :: R) := by
  intro n
  induction n with
  | zero =>
    intro t j K hn ht hK hr
    have htT : t = T' := by omega
    subst htT
    rw [hT] at hr
    injection hr with hr
    -- at the transfer time the third element has rank 2, so K must be empty
    match K, hK, hr with
    | [], _, hr => exact ⟨t, j, Nat.le_refl _, Nat.le_refl _, by rw [hT, hr]; simp⟩
    | [k1], _, hr =>
      simp at hr; obtain ⟨_, _, hd', _⟩ := hr
      rw [hd', chainE_rk U V hU hV] at hd; omega
    | [k1, k2], _, hr =>
      simp at hr; obtain ⟨_, _, hd', _⟩ := hr
      rw [hd', chainE_rk U V hU hV] at hd; omega
    | k1 :: k2 :: k3 :: K', hK, hr =>
      simp at hr; obtain ⟨_, _, hd', _⟩ := hr
      rw [hd', hK k3 (by simp)] at hd; omega
  | succ n ih =>
    intro t j K hn ht hK hr
    match K, hK, hr with
    | [], _, hr => exact ⟨t, j, Nat.le_refl _, ht, hr⟩
    | [k1], hK, hr =>
      -- (CL,P,P): a chain step
      have htT : t < T' := by omega
      have hk1S : head k1 = S := head_of_continue L1 t T' k1 _ _ _ hr htT _ hT
      have hstep : step ([k1] ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) =
          some (args k1 ++ chainE U V (j + 1) :: chainE U V (j + 2) :: Yt :: R) := by
        simp [step, hk1S, chainE]
      have hr' := run_succ_of L1 t _ _ hr hstep
      obtain ⟨t', j', h1, h2, h3⟩ := ih (t + 1) (j + 1) (args k1) (by omega) (by omega)
        (fun k hk => by have := rk_args_le k1 k hk; rw [hK k1 (by simp)] at this; omega) hr'
      exact ⟨t', j', by omega, h2, h3⟩
    | [k1, k2], hK, hr =>
      -- (CL,CL,P) would make |P| = 3
      exfalso
      have htT : t < T' := by omega
      have hk1S : head k1 = S := head_of_continue L1 t T' k1 _ _ _ hr htT _ hT
      have hstep : step ([k1, k2] ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) =
          some (args k1 ++ chainE U V j :: app k2 (chainE U V j) :: chainE U V (j + 1) :: Yt :: R) := by
        simp [step, hk1S]
      have hr' := run_succ_of L1 t _ _ hr hstep
      have hb := hbound (t + 1) _ (by omega) hr'
      have hk20 : rk k2 = 0 := hK k2 (by simp)
      have hk1a : Preg (args k1) = [] := Preg_args_closed k1 (hK k1 (by simp))
      have hj := chainE_rk U V hU hV j
      have hj1 := chainE_rk U V hU hV (j + 1)
      have hk2j : rk (app k2 (chainE U V j)) = 1 := by rw [rk_app, hk20, hj]; rfl
      rw [Preg_append, hk1a] at hb
      simp only [Preg_cons, hj, hk2j, hj1, if_true, List.nil_append, List.length_cons] at hb
      omega
    | k1 :: k2 :: k3 :: K', hK, hr =>
      -- (CL,CL,CL): a closed-code step
      have htT : t < T' := by omega
      have hk1S : head k1 = S := head_of_continue L1 t T' k1 _ _ _ hr htT _ hT
      have hstep : step ((k1 :: k2 :: k3 :: K') ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) =
          some ((args k1 ++ k3 :: app k2 k3 :: K') ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) := by
        simp [step, hk1S]
      have hr' := run_succ_of L1 t _ _ hr hstep
      have hk0 : ∀ k ∈ args k1 ++ k3 :: app k2 k3 :: K', rk k = 0 := by
        intro k hk
        simp at hk
        rcases hk with hk | hk | hk | hk
        · have := rk_args_le k1 k hk; rw [hK k1 (by simp)] at this; omega
        · rw [hk]; exact hK k3 (by simp)
        · rw [hk, rk_app, hK k2 (by simp), hK k3 (by simp)]; rfl
        · exact hK k (by simp [hk])
      obtain ⟨t', j', h1, h2, h3⟩ := ih (t + 1) j _ (by omega) (by omega) hk0 hr'
      exact ⟨t', j', by omega, h2, h3⟩

/-- P-arguments of chain elements: Preg(args E_{j+2}) = Preg(args E_j) ++ [E_{j+1}] -/
theorem Preg_args_chainE (U V : T) (hU : rk U = 1) (hV : rk V = 1) (j : Nat) :
    Preg (args (chainE U V (j + 2))) = Preg (args (chainE U V j)) ++ [chainE U V (j + 1)] := by
  simp only [chainE, args]
  rw [Preg_append]
  simp [Preg_cons, chainE_rk U V hU hV (j + 1), Preg]

theorem Preg_args_chainE_len (U V : T) (hU : rk U = 1) (hV : rk V = 1)
    (hU1 : 1 ≤ (Preg (args U)).length) (hV1 : 1 ≤ (Preg (args V)).length) :
    ∀ j, j / 2 + 1 ≤ (Preg (args (chainE U V j))).length
  | 0 => by simpa [chainE] using hU1
  | 1 => by simpa [chainE] using hV1
  | j + 2 => by
    rw [Preg_args_chainE U V hU hV j, List.length_append]
    have := Preg_args_chainE_len U V hU hV hU1 hV1 j
    simp; omega

/-- **LEMMA YT (machine-checked).**  If at time t the list is K ++ [U, V, Yt | R] with K closed, U, V S-headed
    P-terms and Yt of rank 2, then before the proper transfer the run reaches [E_j, E_{j+1}, Yt | R] and, if this is
    before the transfer time, the chain index satisfies j <= 3. -/
theorem yt_main (L1 : List T) (hS : Seg L1) (T' : Nat) (f b d : T) (RT : List T)
    (hT : run T' L1 = some (f :: b :: d :: RT)) (hd : rk d = 2)
    (hbound : ∀ s Ls, s ≤ T' → run s L1 = some Ls → (Preg Ls).length ≤ 2)
    (U V Yt : T) (R : List T) (hU : rk U = 1) (hV : rk V = 1) (hUS : head U = S) (hVS : head V = S)
    (hYt : rk Yt = 2) (t : Nat) (ht : t ≤ T') (K : List T) (hK : ∀ k ∈ K, rk k = 0)
    (hr : run t L1 = some (K ++ U :: V :: Yt :: R)) :
    ∃ t' j, t ≤ t' ∧ t' ≤ T' ∧ run t' L1 = some (chainE U V j :: chainE U V (j + 1) :: Yt :: R) ∧
      (t' < T' → j ≤ 3) := by
  obtain ⟨t', j, h1, h2, h3⟩ := yt_chain L1 hS T' f b d RT hT hd hbound U V Yt R hU hV (T' - t) t 0 K rfl ht hK
    (by simpa [chainE] using hr)
  refine ⟨t', j, h1, h2, h3, ?_⟩
  intro htT
  have hU1 : 1 ≤ (Preg (args U)).length := by
    obtain ⟨s, hs, hs1⟩ := P_has_P_arg U hUS hU
    unfold Preg; apply List.length_pos_iff_exists_mem.2; exact ⟨s, by simp [hs, hs1]⟩
  have hV1 : 1 ≤ (Preg (args V)).length := by
    obtain ⟨s, hs, hs1⟩ := P_has_P_arg V hVS hV
    unfold Preg; apply List.length_pos_iff_exists_mem.2; exact ⟨s, by simp [hs, hs1]⟩
  have hlen := Preg_args_chainE_len U V hU hV hU1 hV1 j
  -- the front E_j is opened at t' (t' < T'), giving P-region Preg(args E_j)
  have hEj : head (chainE U V j) = S := head_of_continue L1 t' T' _ _ _ _ h3 htT _ hT
  have hstep : step (chainE U V j :: chainE U V (j + 1) :: Yt :: R) =
      some (args (chainE U V j) ++ Yt :: app (chainE U V (j + 1)) Yt :: R) := by simp [step, hEj]
  have hr' := run_succ_of L1 t' _ _ h3 hstep
  have hb := hbound (t' + 1) _ (by omega) hr'
  have hSg := seg_run (t' + 1) L1 _ hS hr'
  have hYtR : ∀ e ∈ Yt :: app (chainE U V (j + 1)) Yt :: R, rk e = 2 := by
    have hs3 := hSg.1
    unfold srt at hs3
    rw [List.pairwise_append] at hs3
    intro e he
    simp at he
    rcases he with he | he | he
    · rw [he]; exact hYt
    · rw [he, rk_app, hYt]; have := rk_le2 (chainE U V (j + 1)); omega
    · have hsrt := (seg_run t' L1 _ hS h3).1
      have := srt_tail_ge Yt R (srt_tail _ _ (srt_tail _ _ hsrt)) e he
      rw [hYt] at this; have := rk_le2 e; omega
  rw [Preg_append, Preg_nil_of (Yt :: app (chainE U V (j + 1)) Yt :: R) (fun e he => by rw [hYtR e he]; omega)] at hb
  simp at hb
  omega

#print axioms yt_main

/-! ## S1 Part 11: two wrappers glued in nested pattern alpha (structural reduction of NHALL's hypothesis) -/

def sg2 (h1 h2 : Nat) (e1 e2 : T) : Nat → T := fun n => if n = h1 then e1 else if n = h2 then e2 else var n

theorem asub_sg2_id (h1 h2 : Nat) (e1 e2 : T) :
    ∀ t : T, occN h1 t = 0 → occN h2 t = 0 → asub (sg2 h1 h2 e1 e2) t = t
  | S, _, _ => by simp [asub]
  | var n, ha, hb => by
    have n1 : n ≠ h1 := by intro e; subst e; simp [occN] at ha
    have n2 : n ≠ h2 := by intro e; subst e; simp [occN] at hb
    simp [asub, sg2, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, asub_sg2_id h1 h2 e1 e2 f (by omega) (by omega), asub_sg2_id h1 h2 e1 e2 x (by omega) (by omega)]

theorem wpre_asub_head (sg : Nat → T) (n : Nat) (hn : ∃ f x, sg n = app f x) :
    ∀ g : T, head g = var n → wpre (sg n) (asub sg g)
  | S, h => by simp [head] at h
  | var m, h => by
    simp [head] at h; subst h
    obtain ⟨f, x, hfx⟩ := hn
    simp [asub, hfx, wpre]
  | app f x, h => by
    simp only [asub, wpre]
    exact Or.inr (wpre_asub_head sg n hn f (by simpa [head] using h))

/-- the two-hole run of a code c started at a glue list c :: v :: e1 :: R0 (one step later the earlier phase is
    the sg2-image of args c ++ [h1, h2], h1 -> e1, h2 -> v.e1): either c never calls its holes, or the earlier
    phase reaches the image of a hole-front at some time <= T'. -/
theorem code_hole_front (c v e1 : T) (h1 h2 : Nat) (h12 : h1 ≠ h2) (hf1 : occN h1 c = 0) (hf2 : occN h2 c = 0)
    (hcS : head c = S) (L0 : List T) (t T' : Nat) (R0 : List T)
    (hglue : run t L0 = some (c :: v :: e1 :: R0)) (htT : t < T')
    (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    NHc c h1 h2 ∨ ∃ k g Lk, t + 1 + k ≤ T' ∧
      run (t + 1 + k) L0 = some ((g :: Lk).map (asub (sg2 h1 h2 e1 (app v e1))) ++ R0) ∧
      (head g = var h1 ∨ head g = var h2) := by
  rcases Classical.em (NHc c h1 h2) with hNH | hNH
  · exact Or.inl hNH
  · right
    have hex : ∃ k g L, run k (args c ++ [var h1, var h2]) = some (g :: L) ∧
        (head g = var h1 ∨ head g = var h2) := by
      apply Classical.byContradiction
      intro hno
      apply hNH
      intro k g L hk
      constructor
      · intro e; exact hno ⟨k, g, L, hk, Or.inl e⟩
      · intro e; exact hno ⟨k, g, L, hk, Or.inr e⟩
    obtain ⟨k, g, Lk, hk, hg⟩ := hex
    have hs1 : sg2 h1 h2 e1 (app v e1) h1 = e1 := by simp [sg2]
    have hs2 : sg2 h1 h2 e1 (app v e1) h2 = app v e1 := by simp [sg2, Ne.symm h12]
    have hA2 : (args c ++ [var h1, var h2]).map (asub (sg2 h1 h2 e1 (app v e1))) ++ R0 =
        args c ++ e1 :: app v e1 :: R0 := by
      have hargs : (args c).map (asub (sg2 h1 h2 e1 (app v e1))) = args c := by
        have : (args c).map (asub (sg2 h1 h2 e1 (app v e1))) = (args c).map id := by
          apply List.map_congr_left
          intro e he'
          exact asub_sg2_id h1 h2 _ _ e (occN_args h1 c hf1 e he') (occN_args h2 c hf2 e he')
        simpa using this
      simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs1, hs2]
      simp
    have ht1 : run (t + 1) L0 = some ((args c ++ [var h1, var h2]).map
        (asub (sg2 h1 h2 e1 (app v e1))) ++ R0) := by
      rw [hA2, run_add t 1, hglue, Option.bind_some]
      simp [run, step, hcS]
    obtain ⟨_, hearly⟩ := image_stuck _ _ R0 L0 (t + 1) T' (by omega) ht1 f b d R hT hf k (g :: Lk) hk
    have p2k : run (t + 1 + k) L0 =
        some ((g :: Lk).map (asub (sg2 h1 h2 e1 (app v e1))) ++ R0) := by
      rw [run_add (t + 1) k, ht1, Option.bind_some]
      exact run_append k _ _ R0 (asub_run _ k _ _ hk)
    exact ⟨k, g, Lk, Nat.le_of_not_lt hearly, p2k, hg⟩

/-- **THEOREM MW-ALPHA2.**  A two-wrapper handler V = v1.(v2.y) (v_i = b_i.c_i, S-headed codes, y-free) whose
    inner wrapper was glued in pattern alpha ([c2, v2, y]) and whose outer wrapper was glued in pattern alpha onto
    L2 = v2.y ([c1, v1, L2]), in an earlier phase (ANY run from L0) that later reaches a p-front at T'.  Unless the
    earlier phase opens an L2-prefixed front after the inner glue (the re-opening case I-L2), the next phase
    (datum v1'.(v2'.p')) never makes a proper transfer: by the two codes' hole-fronts, either both c-codes never
    call their holes (NHALL), or the earlier phase lays out args(V) (IGEN). -/
theorem mw_alpha2 (b1 c1 b2 c2 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H)
    (hb1S : head b1 = S) (hc1S : head c1 = S) (hb2S : head b2 = S) (hc2S : head c2 = S)
    (hy0 : occ2 b1 = 0) (hy1 : occ2 c1 = 0) (hy2 : occ2 b2 = 0) (hy3 : occ2 c2 = 0)
    (hf1 : occN h1 c1 = 0) (hf2 : occN h2 c1 = 0) (hf3 : occN h1 c2 = 0) (hf4 : occN h2 c2 = 0)
    (hV : fresh3 H (app (app b1 c1) (app (app b2 c2) (var 2))))
    (L0 : List T) (t2 t1 T' : Nat) (R0 R1 : List T)
    (hg2 : run t2 L0 = some (c2 :: app b2 c2 :: var 2 :: R0))
    (hg1 : run t1 L0 = some (c1 :: app b1 c1 :: app (app b2 c2) (var 2) :: R1))
    (h21 : t2 < t1) (h1T : t1 < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R))
    (hf : head f = var 0)
    (hNoL2 : ∀ (t : Nat) (g : T) (L : List T), t2 < t → t ≤ T' → run t L0 = some (g :: L) →
      ¬ wpre (app (app b2 c2) (var 2)) g) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [rcombT ([app b1 c1, app b2 c2].map (sb c)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  have hL2app : ∃ f x, app (app b2 c2) (var 2) = app f x := ⟨_, _, rfl⟩
  have hVapp : ∃ f x, app (app b1 c1) (app (app b2 c2) (var 2)) = app f x := ⟨_, _, rfl⟩
  -- inner code c2, started at the inner glue (h1 -> y, h2 -> L2)
  have hNH2 : NHc c2 h1 h2 := by
    rcases code_hole_front c2 (app b2 c2) (var 2) h1 h2 h12 hf3 hf4 hc2S L0 t2 T' R0 hg2 (by omega) f b d R hT hf
      with h | ⟨k, g, Lk, hkT, hrun, hg⟩
    · exact h
    · exfalso
      rcases hg with hg | hg
      · -- a y-front of the earlier phase before its p-front: impossible
        have hy : head (asub (sg2 h1 h2 (var 2) (app (app b2 c2) (var 2))) g) = var 2 := by
          rw [asub_headvar _ h1 g hg]; simp [sg2, head]
        rcases Nat.lt_or_ge (t2 + 1 + k) T' with hlt | hge
        · obtain ⟨Ln, hLn, _⟩ := run_prefix T' (t2 + 1 + k + 1) L0 _ hT (by omega)
          rw [run_add (t2 + 1 + k) 1, hrun, Option.bind_some] at hLn
          simp only [List.map_cons, List.cons_append, run] at hLn
          rw [step_head_ne _ _ (by rw [hy]; simp)] at hLn
          simp at hLn
        · have : t2 + 1 + k = T' := by omega
          rw [this, hT] at hrun
          simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at hrun
          rw [hrun.1, hy] at hf; injection hf with e; omega
      · -- an L2-prefixed front after the inner glue: excluded
        have hw := wpre_asub_head (sg2 h1 h2 (var 2) (app (app b2 c2) (var 2))) h2 (by simp [sg2, Ne.symm h12])
          g hg
        simp only [sg2, Ne.symm h12, if_false, if_true] at hw
        exact hNoL2 (t2 + 1 + k) _ _ (by omega) hkT hrun hw
  -- outer code c1, started at the outer glue (h1 -> L2, h2 -> V)
  rcases code_hole_front c1 (app b1 c1) (app (app b2 c2) (var 2)) h1 h2 h12 hf1 hf2 hc1S L0 t1 T' R1 hg1 h1T
      f b d R hT hf with hNH1 | ⟨k, g, Lk, hkT, hrun, hg⟩
  · -- NHALL
    have hw1 : WOK h1 h2 (app b1 c1) := ⟨b1, c1, rfl, hb1S, hc1S, hy0, hy1, hf1, hf2, hNH1⟩
    have hw2 : WOK h1 h2 (app b2 c2) := ⟨b2, c2, rfl, hb2S, hc2S, hy2, hy3, hf3, hf4, hNH2⟩
    exact nhall_main [app b1 c1, app b2 c2] c h1 h2 hc hc2 hh1 hh2 h12 (by simp)
      (by intro u hu; simp at hu; rcases hu with hu | hu <;> subst hu <;> assumption)
  · rcases hg with hg | hg
    · -- c1 calls its first hole: an L2-prefixed front after the inner glue: excluded
      exfalso
      have hw := wpre_asub_head (sg2 h1 h2 (app (app b2 c2) (var 2))
        (app (app b1 c1) (app (app b2 c2) (var 2)))) h1 (by simp [sg2]) g hg
      simp only [sg2, if_true] at hw
      exact hNoL2 (t1 + 1 + k) _ _ (by omega) hkT hrun hw
    · -- c1 calls its second hole: the earlier phase opens V, i.e. lays out args(V): IGEN
      have hVS : head (app (app b1 c1) (app (app b2 c2) (var 2))) = S := by simp [head, hb1S]
      have hs2' : sg2 h1 h2 (app (app b2 c2) (var 2)) (app (app b1 c1) (app (app b2 c2) (var 2))) h2 =
          app (app b1 c1) (app (app b2 c2) (var 2)) := by simp [sg2, Ne.symm h12]
      have hGS : head (asub (sg2 h1 h2 (app (app b2 c2) (var 2)) (app (app b1 c1) (app (app b2 c2) (var 2)))) g) = S := by
        rw [asub_headvar _ h2 g hg, hs2']; exact hVS
      have hTgt : t1 + 1 + k < T' := by
        rcases Nat.lt_or_ge (t1 + 1 + k) T' with hlt | hge
        · exact hlt
        · exfalso
          have : t1 + 1 + k = T' := by omega
          rw [this, hT] at hrun
          simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at hrun
          rw [hrun.1, hGS] at hf; simp at hf
      obtain ⟨Ln, hLn, _⟩ := run_prefix T' (t1 + 1 + k + 1) L0 _ hT (by omega)
      have hstep : step ((g :: Lk).map (asub (sg2 h1 h2 (app (app b2 c2) (var 2))
          (app (app b1 c1) (app (app b2 c2) (var 2))))) ++ R1) = some Ln := by
        rw [run_add (t1 + 1 + k) 1, hrun, Option.bind_some] at hLn
        simp only [run] at hLn
        cases hs : step ((g :: Lk).map (asub (sg2 h1 h2 (app (app b2 c2) (var 2))
            (app (app b1 c1) (app (app b2 c2) (var 2))))) ++ R1) with
        | none => rw [hs] at hLn; simp at hLn
        | some L1 => rw [hs] at hLn; simpa using hLn
      have hargsG := asub_args_var (sg2 h1 h2 (app (app b2 c2) (var 2)) (app (app b1 c1) (app (app b2 c2) (var 2))))
        h2 (by rw [hs2']; exact hVS) g hg
      rw [hs2'] at hargsG
      have hLn_form : ∃ B2, Ln = args (app (app b1 c1) (app (app b2 c2) (var 2))) ++ B2 := by
        simp only [List.map_cons, List.cons_append] at hstep
        match hrest : Lk.map (asub (sg2 h1 h2 (app (app b2 c2) (var 2))
            (app (app b1 c1) (app (app b2 c2) (var 2))))) ++ R1, hstep with
        | b2' :: d2 :: R2, hstep =>
          simp only [step, hGS, ite_true, Option.some.injEq] at hstep
          rw [hargsG] at hstep
          exact ⟨List.map (asub (sg2 h1 h2 (app (app b2 c2) (var 2)) (app (app b1 c1) (app (app b2 c2) (var 2)))))
            (args g) ++ d2 :: app b2' d2 :: R2, by rw [← hstep, List.append_assoc]⟩
        | [], hstep => simp [step] at hstep
        | [_], hstep => simp [step] at hstep
      obtain ⟨B2, hB2⟩ := hLn_form
      rw [hB2] at hLn
      have hVa : args (app (app b1 c1) (app (app b2 c2) (var 2))) ≠ [] := by simp [args]
      have hno := igen_main (app (app b1 c1) (app (app b2 c2) (var 2))) c H hc hH hVS hVa hV L0
        (t1 + 1 + k + 1) T' B2 (by omega) hLn f b d R hT hf
      have hD3 : asub (sg3 c) (app (app b1 c1) (app (app b2 c2) (var 2))) =
          rcombT ([app b1 c1, app b2 c2].map (sb c)) (var 0) := by
        simp [asub, asub_sg3_sb c b1 hy0, asub_sg3_sb c c1 hy1, asub_sg3_sb c b2 hy2, asub_sg3_sb c c2 hy3, sg3,
          rcombT, sb]
      intro m f' b' d' R' hm hf'
      rw [← hD3] at hm
      exact absurd hf' (hno m f' _ hm)

#print axioms mw_alpha2

/-! ## S1 Part 12: THEOREM IL-ATOM - the earlier phase re-opens the innermost level, whose c-code is an atom -/

/-- with both holes mapped to atoms, the image of a two-hole run is followed step by step (no hypothesis on calls) -/
theorem corr_atoms (A : List T) (k1 k2 : Nat) (sg : Nat → T) (hA : 2 ≤ nHB k1 k2 A)
    (hk1 : ∀ n, head (sg n) ≠ S) (B : List T) :
    ∀ (j : Nat) (L' : List T), run j (A.map (asub sg) ++ B) = some L' →
      ∃ Aj, run j A = some Aj ∧ L' = Aj.map (asub sg) ++ B := by
  intro j
  induction j with
  | zero => intro L' h; refine ⟨A, rfl, ?_⟩; simp only [run, Option.some.injEq] at h; exact h.symm
  | succ j ih =>
    intro L' h
    obtain ⟨L'', hL'', hs⟩ := run_succ_split _ j L' h
    obtain ⟨Aj, hAj, hL''e⟩ := ih L'' hL''
    have hnb : 2 ≤ nHB k1 k2 Aj := Nat.le_trans hA (nHB_run k1 k2 j _ _ hAj)
    rw [hL''e] at hs
    obtain ⟨a, b, d, R, hlist, haS, hL'⟩ := step_some _ L' hs
    match Aj, hnb, hlist, hAj with
    | [], hnb, _, _ => simp [nHB] at hnb
    | [g], hnb, _, _ => have := nHB_le_length k1 k2 [g]; simp at this; omega
    | [g, e2], hnb, hlist, _ =>
      exfalso
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at hlist
      obtain ⟨hga, _⟩ := hlist
      have hg : isHB k1 k2 g = true := nHB_two_first k1 k2 g e2 hnb
      unfold isHB at hg
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
      rcases hg with hg | hg
      · rw [← hga, asub_headvar _ k1 g hg] at haS; exact hk1 k1 haS
      · rw [← hga, asub_headvar _ k2 g hg] at haS; exact hk1 k2 haS
    | g :: e2 :: e3 :: rest, _, hlist, hAj =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hlist
      obtain ⟨hga, hgb, hgd, hR⟩ := hlist
      have hgS : head g = S := by
        rcases head_cases g with hg | ⟨n, hn⟩
        · exact hg
        · exfalso; rw [← hga, asub_headvar _ n g hn] at haS; exact hk1 n haS
      have hstepA : step (g :: e2 :: e3 :: rest) = some (args g ++ e3 :: app e2 e3 :: rest) := by
        simp [step, hgS]
      refine ⟨args g ++ e3 :: app e2 e3 :: rest, run_succ_of A j _ _ hAj hstepA, ?_⟩
      rw [hL', ← hga, ← hgb, ← hgd, ← hR]
      rw [asub_args _ g hgS]
      simp [asub]

/-- the next-phase image of the innermost code bn: p -> c, k1 -> the frozen c-code atom, k2 -> p' -/
def tauI (c k1 k2 : Nat) (cn' : T) : Nat → T := fun n =>
  if n = 0 then var c else if n = k1 then cn' else if n = k2 then var 0 else var n

/-- the earlier-phase image: k1 -> the c-code atom, k2 -> y -/
def sigI (k1 k2 : Nat) (cn : T) : Nat → T := fun n =>
  if n = k1 then cn else if n = k2 then var 2 else var n

theorem asub_tauI_sb (c k1 k2 : Nat) (cn' : T) (hk1 : k1 ≠ 0) (hk2 : k2 ≠ 0) :
    ∀ t : T, occN k1 t = 0 → occN k2 t = 0 → asub (tauI c k1 k2 cn') t = sb c t
  | S, _, _ => by simp [asub, sb]
  | var n, ha, hb => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, tauI]
    · have n1 : n ≠ k1 := by intro e; subst e; simp [occN] at ha
      have n2 : n ≠ k2 := by intro e; subst e; simp [occN] at hb
      simp [asub, sb, tauI, h0, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, sb, asub_tauI_sb c k1 k2 cn' hk1 hk2 f (by omega) (by omega),
      asub_tauI_sb c k1 k2 cn' hk1 hk2 x (by omega) (by omega)]

theorem occN0_sb (c : Nat) (hc : c ≠ 0) : ∀ t : T, occN 0 (sb c t) = 0
  | S => by simp [sb, occN]
  | var n => by
    by_cases h : n = 0
    · subst h; simp [sb, occN, hc]
    · simp [sb, occN, h]
  | app f x => by simp [sb, occN, occN0_sb c hc f, occN0_sb c hc x]

theorem guarded_rcombT (c : Nat) (hc : c ≠ 0) (vn' : T) : ∀ ws : List T,
    guarded (app vn' (var 0)) (rcombT (ws.map (sb c)) (app vn' (var 0)))
  | [] => Or.inl rfl
  | u :: ws => Or.inr ⟨guarded_free _ _ (occN0_sb c hc u), guarded_rcombT c hc vn' ws⟩

theorem rcombT_append (xs : List T) (v t : T) : rcombT (xs ++ [v]) t = rcombT xs (app v t) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rcombT, ih]

/-- **THEOREM IL-ATOM.**  Handler V = v1.(...(vn.y)) with ANY number of wrappers, innermost vn = bn.cn with bn
    S-headed, y-free, and cn ATOM-HEADED with head other than y (the live p - frozen to c in the next phase - or a frozen atom).
    If the earlier phase (any run from L0) re-opens the innermost level, i.e. reaches args(bn) ++ [cn, y] ++ B2
    (= args(vn.y) ++ B2), at a time before its p-front, then the next phase has NO p'-headed front at all.
    (Before its first innermost-level opening the next phase has no p'-front (guarded phase); from that opening on
    it is the image of bn's two-hole run with both holes mapped to atoms; a p'-front would be a second-hole front,
    whose earlier-phase image is a y-front before the transfer.) -/
theorem il_atom (ws : List T) (bn cn : T) (n0 c k1 k2 : Nat) (hc : c ≠ 0) (hn0 : n0 ≠ 2)
    (hk1 : 4 ≤ k1) (hk2 : 4 ≤ k2) (hk12 : k1 ≠ k2) (hcnh : head cn = var n0)
    (hbnS : head bn = S) (hfb1 : occN k1 bn = 0) (hfb2 : occN k2 bn = 0)
    (L0 : List T) (tI T' : Nat) (B2 : List T) (hI : run tI L0 = some (args bn ++ cn :: var 2 :: B2))
    (htT : tI ≤ T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T),
      run m [rcombT ((ws ++ [app bn cn]).map (sb c)) (var 0), var 1, var 2, var 3] = some (f' :: L') →
      head f' ≠ var 0 := by
  intro m f' L' hm hf'
  have hk1' : k1 ≠ 0 := by omega
  have hk2' : k2 ≠ 0 := by omega
  obtain ⟨cn', hcn'⟩ : ∃ cn', cn' = sb c cn := ⟨_, rfl⟩
  have hsbh : ∀ t : T, head t = var n0 → head (sb c t) = if n0 = 0 then var c else var n0 := by
    intro t; induction t with
    | S => intro h; simp [head] at h
    | var n => intro h; simp [head] at h; subst h; by_cases h0 : n = 0 <;> simp [sb, head, h0]
    | app f x ihf _ => intro h; simp only [sb, head] at h ⊢; exact ihf h
  have hcn'atom : head cn' ≠ S ∧ head cn' ≠ var 0 := by
    rw [hcn', hsbh cn hcnh]; by_cases h : n0 = 0
    · simp [h, hc]
    · simp [h]
  obtain ⟨Ln', hLn'⟩ : ∃ Ln', Ln' = app (app (sb c bn) cn') (var 0) := ⟨_, rfl⟩
  have hD3 : rcombT ((ws ++ [app bn cn]).map (sb c)) (var 0) = rcombT (ws.map (sb c)) Ln' := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [rcombT_append, hLn', hcn']; simp [sb]
  rw [hD3] at hm
  have hbn' : head (sb c bn) = S := sb_head c bn hbnS
  have hLnS : head Ln' = S := by simp [hLn', head, hbn']
  have h0 : ∀ e ∈ [rcombT (ws.map (sb c)) Ln', var 1, var 2, var 3], guarded Ln' e := by
    intro e he
    simp at he
    rcases he with he | he | he | he <;> subst he
    · rw [hLn']; exact guarded_rcombT c hc _ ws
    · simp [guarded]
    · simp [guarded]
    · simp [guarded]
  rcases guarded_phase Ln' hLnS _ h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exact guarded_head Ln' (by rw [hLnS]; simp) f' (hG f' (by simp)) hf'
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    obtain ⟨us, hus, _⟩ := guarded_prefix_args Ln' f1 hwp (hg1 f1 (by rw [hL1]; simp))
    have hf1S : head f1 = S := by rw [wpre_headeq Ln' f1 hwp]; exact hLnS
    rw [hL1] at hs2
    simp only [step, hf1S, ite_true, Option.some.injEq] at hs2
    -- the list after the first innermost-level opening is the tauI-image of args bn ++ [k1, k2]
    have hA : (args bn ++ [var k1, var k2]).map (asub (tauI c k1 k2 cn')) = args Ln' := by
      have hargsLn : args Ln' = args (sb c bn) ++ [cn', var 0] := by simp [hLn', args]
      rw [hargsLn, sb_args c bn hbnS]
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hargs : (args bn).map (asub (tauI c k1 k2 cn')) = (args bn).map (sb c) := by
        apply List.map_congr_left
        intro s hs
        exact asub_tauI_sb c k1 k2 cn' hk1' hk2' s (occN_args k1 bn hfb1 s hs) (occN_args k2 bn hfb2 s hs)
      rw [hargs]
      simp [asub, tauI, hk1', hk2', hk12.symm]
    have hL2 : L2 = (args bn ++ [var k1, var k2]).map (asub (tauI c k1 k2 cn')) ++ (us ++ d1 :: app b1 d1 :: R1) := by
      rw [← hs2, hus, hA]; simp
    rw [hL2] at hrest
    have hnbA : 2 ≤ nHB k1 k2 (args bn ++ [var k1, var k2]) := by
      rw [nHB_append]
      have : nHB k1 k2 [var k1, var k2] = 2 := by simp [nHB, isHB, head]
      omega
    have hatoms : ∀ n, head (tauI c k1 k2 cn' n) ≠ S := by
      intro n
      simp only [tauI]
      by_cases h0 : n = 0
      · rw [if_pos h0]; simp [head]
      · by_cases h1 : n = k1
        · rw [if_neg h0, if_pos h1]; exact hcn'atom.1
        · by_cases h2 : n = k2
          · rw [if_neg h0, if_neg h1, if_pos h2]; simp [head]
          · rw [if_neg h0, if_neg h1, if_neg h2]; simp [head]
    obtain ⟨Aj, hAj, hLe⟩ := corr_atoms _ k1 k2 _ hnbA hatoms _ _ _ hrest
    have hnbj : 2 ≤ nHB k1 k2 Aj := Nat.le_trans hnbA (nHB_run k1 k2 _ _ _ hAj)
    match Aj, hnbj, hLe, hAj with
    | [], hnbj, _, _ => simp [nHB] at hnbj
    | g :: rest, _, hLe, hAj =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hLe
      have hgk2 : head g = var k2 := by
        rw [hLe.1] at hf'
        rcases head_cases g with hg | ⟨n, hn⟩
        · rw [asub_headS _ g hg] at hf'; simp at hf'
        · rw [asub_headvar _ n g hn] at hf'
          by_cases h2 : n = k2
          · rw [hn, h2]
          · exfalso
            simp only [tauI] at hf'
            by_cases h0 : n = 0
            · rw [if_pos h0] at hf'; simp [head] at hf'; exact hc hf'
            · by_cases h1 : n = k1
              · rw [if_neg h0, if_pos h1] at hf'; exact hcn'atom.2 hf'
              · rw [if_neg h0, if_neg h1, if_neg h2] at hf'; simp [head] at hf'; exact h0 hf'
      -- the earlier phase at the corresponding time has a y-front: impossible before its p-front
      have hI' : run tI L0 = some ((args bn ++ [var k1, var k2]).map (asub (sigI k1 k2 cn)) ++ B2) := by
        rw [hI]
        have hargs : (args bn).map (asub (sigI k1 k2 cn)) = args bn := by
          have : (args bn).map (asub (sigI k1 k2 cn)) = (args bn).map id := by
            apply List.map_congr_left
            intro s hs
            have := asub_sgA_id k1 k2 (var 2) s (occN_args k1 bn hfb1 s hs) (occN_args k2 bn hfb2 s hs)
            have e : ∀ t : T, occN k1 t = 0 → occN k2 t = 0 → asub (sigI k1 k2 cn) t = t := by
              intro t; induction t with
              | S => intro _ _; simp [asub]
              | var n =>
                intro ha hb
                have n1 : n ≠ k1 := by intro e; subst e; simp [occN] at ha
                have n2 : n ≠ k2 := by intro e; subst e; simp [occN] at hb
                simp [asub, sigI, n1, n2]
              | app f x ihf ihx =>
                intro ha hb
                simp only [occN] at ha hb
                simp [asub, ihf (by omega) (by omega), ihx (by omega) (by omega)]
            exact e s (occN_args k1 bn hfb1 s hs) (occN_args k2 bn hfb2 s hs)
          simpa using this
        simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, sigI, Ne.symm hk12]
        simp
      obtain ⟨hstuckE, _⟩ := image_stuck _ _ B2 L0 tI T' htT hI' f b d R hT hf _ (g :: rest) hAj
      have p2 : run (tI + (m - m1 - 1)) L0 =
          some ((g :: rest).map (asub (sigI k1 k2 cn)) ++ B2) := by
        rw [run_add tI _, hI', Option.bind_some]
        exact run_append _ _ _ B2 (asub_run _ _ _ _ hAj)
      have hy : head (asub (sigI k1 k2 cn) g) = var 2 := by
        rw [asub_headvar _ k2 g hgk2]; simp [sigI, Ne.symm hk12, head]
      have hnone : run (tI + (m - m1 - 1) + 1) L0 = none := by
        rw [run_add (tI + (m - m1 - 1)) 1, p2, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ (by rw [hy]; simp)]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      rw [← he.1, hy] at hf; injection hf with e; omega

#print axioms il_atom

/-! ## S1 Part 13: THEOREM IL-NH - the earlier phase re-opens the innermost level, whose c-code never calls its
    holes -/

/-- **THEOREM IL-NH.**  Handler V = v1.(...(vn.y)) with ANY number of wrappers, innermost vn = bn.cn with bn, cn
    S-headed and y-free, and cn never calling its holes (NHc, handler-only).  If the earlier phase (any run from L0)
    re-opens the innermost level, i.e. reaches args(bn) ++ [cn, y] ++ B2 (= args(vn.y) ++ B2) before its p-front,
    then the next phase has NO p'-headed front at all.  (Guarded phase until the first innermost-level opening;
    then bn's two-hole run: a second-hole front would be a y-front of the earlier phase, a first-hole front runs
    cn', which never reaches a p'-front by paf_post.) -/
theorem il_nh (ws : List T) (bn cn : T) (c k1 k2 : Nat) (hc : c ≠ 0)
    (hk1 : 4 ≤ k1) (hk2 : 4 ≤ k2) (hk12 : k1 ≠ k2)
    (hbnS : head bn = S) (hcnS : head cn = S) (hfb1 : occN k1 bn = 0) (hfb2 : occN k2 bn = 0)
    (hfc1 : occN k1 cn = 0) (hfc2 : occN k2 cn = 0) (hNH : NHc cn k1 k2)
    (L0 : List T) (tI T' : Nat) (B2 : List T) (hI : run tI L0 = some (args bn ++ cn :: var 2 :: B2))
    (htT : tI ≤ T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T),
      run m [rcombT ((ws ++ [app bn cn]).map (sb c)) (var 0), var 1, var 2, var 3] = some (f' :: L') →
      head f' ≠ var 0 := by
  intro m f' L' hm hf'
  have hk1' : k1 ≠ 0 := by omega
  have hk2' : k2 ≠ 0 := by omega
  obtain ⟨Ln', hLn'⟩ : ∃ Ln', Ln' = app (app (sb c bn) (sb c cn)) (var 0) := ⟨_, rfl⟩
  have hD3 : rcombT ((ws ++ [app bn cn]).map (sb c)) (var 0) = rcombT (ws.map (sb c)) Ln' := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [rcombT_append, hLn']; simp [sb]
  rw [hD3] at hm
  have hbn' : head (sb c bn) = S := sb_head c bn hbnS
  have hcn' : head (sb c cn) = S := sb_head c cn hcnS
  have hLnS : head Ln' = S := by simp [hLn', head, hbn']
  have h0 : ∀ e ∈ [rcombT (ws.map (sb c)) Ln', var 1, var 2, var 3], guarded Ln' e := by
    intro e he
    simp at he
    rcases he with he | he | he | he <;> subst he
    · rw [hLn']; exact guarded_rcombT c hc _ ws
    · simp [guarded]
    · simp [guarded]
    · simp [guarded]
  rcases guarded_phase Ln' hLnS _ h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exact guarded_head Ln' (by rw [hLnS]; simp) f' (hG f' (by simp)) hf'
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    obtain ⟨us, hus, _⟩ := guarded_prefix_args Ln' f1 hwp (hg1 f1 (by rw [hL1]; simp))
    have hf1S : head f1 = S := by rw [wpre_headeq Ln' f1 hwp]; exact hLnS
    have hrunL2 : run (m1 + 1) [rcombT (ws.map (sb c)) Ln', var 1, var 2, var 3] = some L2 :=
      run_succ_of _ m1 L1 L2 hr1 hs2
    rw [hL1] at hs2
    simp only [step, hf1S, ite_true, Option.some.injEq] at hs2
    -- after the first innermost-level opening: the tauB-image of args bn ++ [k1, k2] over the bottom B3
    have hA : (args bn ++ [var k1, var k2]).map (asub (tauB c k1 k2 (sb c cn))) = args Ln' := by
      have hargsLn : args Ln' = args (sb c bn) ++ [sb c cn, var 0] := by simp [hLn', args]
      rw [hargsLn, sb_args c bn hbnS]
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hargs : (args bn).map (asub (tauB c k1 k2 (sb c cn))) = (args bn).map (sb c) := by
        apply List.map_congr_left
        intro s hs
        exact asub_tauB_sb c k1 k2 (sb c cn) hk1' hk2' s (occN_args k1 bn hfb1 s hs) (occN_args k2 bn hfb2 s hs)
      rw [hargs]
      simp [asub, tauB, hk1', hk2', hk12.symm]
    obtain ⟨B3, hB3⟩ : ∃ B3, B3 = us ++ d1 :: app b1 d1 :: R1 := ⟨_, rfl⟩
    have hL2 : L2 = (args bn ++ [var k1, var k2]).map (asub (tauB c k1 k2 (sb c cn))) ++ B3 := by
      rw [← hs2, hus, hA, hB3]; simp
    rw [hL2] at hrest
    have hB3ne : B3 ≠ [] := by rw [hB3]; simp
    -- the earlier-phase image of the same two-hole run: k1 -> cn, k2 -> y
    have hI' : run tI L0 = some ((args bn ++ [var k1, var k2]).map (asub (sg2 k1 k2 cn (var 2))) ++ B2) := by
      rw [hI]
      have hargs : (args bn).map (asub (sg2 k1 k2 cn (var 2))) = args bn := by
        have : (args bn).map (asub (sg2 k1 k2 cn (var 2))) = (args bn).map id := by
          apply List.map_congr_left
          intro s hs
          exact asub_sg2_id k1 k2 _ _ s (occN_args k1 bn hfb1 s hs) (occN_args k2 bn hfb2 s hs)
        simpa using this
      simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, sg2, Ne.symm hk12]
      simp
    have hnbA : 2 ≤ nHB k1 k2 (args bn ++ [var k1, var k2]) := by
      rw [nHB_append]
      have : nHB k1 k2 [var k1, var k2] = 2 := by simp [nHB, isHB, head]
      omega
    -- follow the next phase along bn's two-hole run until its first atom front
    have key : ∀ (j : Nat) (L'' : List T),
        run j ((args bn ++ [var k1, var k2]).map (asub (tauB c k1 k2 (sb c cn))) ++ B3) = some L'' →
        (∃ Aj, run j (args bn ++ [var k1, var k2]) = some Aj ∧
          L'' = Aj.map (asub (tauB c k1 k2 (sb c cn))) ++ B3) ∨
        (∃ j0 g rest, j0 < j ∧ run j0 (args bn ++ [var k1, var k2]) = some (g :: rest) ∧ head g = var k1) := by
      intro j
      induction j with
      | zero => intro L'' h; left; refine ⟨_, rfl, ?_⟩; simp only [run, Option.some.injEq] at h; exact h.symm
      | succ j ih =>
        intro L'' h
        obtain ⟨L3, hL3, hs⟩ := run_succ_split _ j L'' h
        rcases ih L3 hL3 with ⟨Aj, hAj, hL3e⟩ | ⟨j0, g, rest, hj0, hr0, hg0⟩
        · have hnb : 2 ≤ nHB k1 k2 Aj := Nat.le_trans hnbA (nHB_run k1 k2 j _ _ hAj)
          rw [hL3e] at hs
          obtain ⟨a, b', d', R', hlist, haS, hL''⟩ := step_some _ L'' hs
          match Aj, hnb, hlist, hAj with
          | [], hnb, _, _ => simp [nHB] at hnb
          | [g], hnb, _, _ => have := nHB_le_length k1 k2 [g]; simp at this; omega
          | g :: e2 :: rest, hnb, hlist, hAj =>
            rcases head_cases g with hg | ⟨n, hn⟩
            · -- S-headed abstract front: both runs step
              match rest, hnb, hlist, hAj with
              | [], hnb, _, hAj =>
                exfalso
                have hgb : isHB k1 k2 g = true := nHB_two_first k1 k2 g e2 hnb
                unfold isHB at hgb
                simp only [Bool.or_eq_true, decide_eq_true_eq] at hgb
                rcases hgb with hgb | hgb <;> rw [hgb] at hg <;> simp at hg
              | e3 :: rest', _, hlist, hAj =>
                left
                simp only [List.map_cons, List.cons_append, List.cons.injEq] at hlist
                obtain ⟨hga, hgb, hgd, hR⟩ := hlist
                have hstepA : step (g :: e2 :: e3 :: rest') = some (args g ++ e3 :: app e2 e3 :: rest') := by
                  simp [step, hg]
                refine ⟨args g ++ e3 :: app e2 e3 :: rest', run_succ_of _ j _ _ hAj hstepA, ?_⟩
                rw [hL'', ← hga, ← hgb, ← hgd, ← hR, asub_args _ g hg]
                simp [asub]
            · by_cases h1 : n = k1
              · subst h1; right; exact ⟨j, g, e2 :: rest, by omega, hAj, hn⟩
              · exfalso
                simp only [List.map_cons, List.cons_append, List.cons.injEq] at hlist
                rw [← hlist.1, asub_headvar _ n g hn] at haS
                simp only [tauB] at haS
                by_cases h0 : n = 0
                · rw [if_pos h0] at haS; simp [head] at haS
                · rw [if_neg h0, if_neg h1] at haS
                  by_cases h2 : n = k2
                  · rw [if_pos h2] at haS; simp [head] at haS
                  · rw [if_neg h2] at haS; simp [head] at haS
        · right; exact ⟨j0, g, rest, by omega, hr0, hg0⟩
    -- a second-hole front of bn's run would give the earlier phase a y-front before its p-front
    have no_k2 : ∀ j g rest, run j (args bn ++ [var k1, var k2]) = some (g :: rest) → head g ≠ var k2 := by
      intro j g rest hj hg2
      obtain ⟨hstuckE, _⟩ := image_stuck _ _ B2 L0 tI T' htT hI' f b d R hT hf j (g :: rest) hj
      have p2 : run (tI + j) L0 = some ((g :: rest).map (asub (sg2 k1 k2 cn (var 2))) ++ B2) := by
        rw [run_add tI _, hI', Option.bind_some]
        exact run_append _ _ _ B2 (asub_run _ _ _ _ hj)
      have hy : head (asub (sg2 k1 k2 cn (var 2)) g) = var 2 := by
        rw [asub_headvar _ k2 g hg2]; simp [sg2, Ne.symm hk12, head]
      have hnone : run (tI + j + 1) L0 = none := by
        rw [run_add (tI + j) 1, p2, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ (by rw [hy]; simp)]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      rw [← he.1, hy] at hf; injection hf with e; omega
    rcases key _ _ hrest with ⟨Aj, hAj, hLe⟩ | ⟨j0, g, rest, hj0, hr0, hg0⟩
    · -- still following bn's run: the p'-front would be a second-hole front
      match Aj, hLe, hAj with
      | [], _, hAj0 =>
        exfalso
        have hnb : 2 ≤ nHB k1 k2 ([] : List T) := Nat.le_trans hnbA (nHB_run k1 k2 _ _ _ hAj0)
        simp [nHB] at hnb
      | g :: rest, hLe, hAj =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hLe
        rw [hLe.1] at hf'
        rcases head_cases g with hg | ⟨n, hn⟩
        · rw [asub_headS _ g hg] at hf'; simp at hf'
        · rw [asub_headvar _ n g hn] at hf'
          by_cases h2 : n = k2
          · exact no_k2 _ g rest hAj (by rw [hn, h2])
          · simp only [tauB] at hf'
            by_cases h0 : n = 0
            · rw [if_pos h0] at hf'; simp [head] at hf'; exact hc hf'
            · rw [if_neg h0] at hf'
              by_cases h1 : n = k1
              · rw [if_pos h1] at hf'; rw [hcn'] at hf'; simp at hf'
              · rw [if_neg h1, if_neg h2] at hf'; simp [head] at hf'; exact h0 hf'
    · -- bn called its first hole at abstract time j0: from then on the next phase runs cn' (paf_post)
      have hnb : 2 ≤ nHB k1 k2 (g :: rest) := Nat.le_trans hnbA (nHB_run k1 k2 _ _ _ hr0)
      obtain ⟨x2, rest', hrest'⟩ : ∃ x2 rest', rest = x2 :: rest' := by
        match rest, hnb with
        | [], hnb => have := nHB_le_length k1 k2 [g]; simp at this; omega
        | x2 :: rest', _ => exact ⟨x2, rest', rfl⟩
      subst hrest'
      obtain ⟨x3, B4, hB4⟩ : ∃ x3 B4, rest'.map (asub (tauB c k1 k2 (sb c cn))) ++ B3 = x3 :: B4 := by
        cases rest' with
        | nil =>
          cases hb3 : B3 with
          | nil => exact absurd hb3 hB3ne
          | cons x B => exact ⟨x, B, by simp⟩
        | cons x r => exact ⟨asub (tauB c k1 k2 (sb c cn)) x, r.map (asub (tauB c k1 k2 (sb c cn))) ++ B3, by simp⟩
      have hrun0 : run (m1 + 1 + j0) [rcombT (ws.map (sb c)) Ln', var 1, var 2, var 3] =
          some (asub (tauB c k1 k2 (sb c cn)) g :: asub (tauB c k1 k2 (sb c cn)) x2 :: x3 :: B4) := by
        rw [run_add (m1 + 1) j0, hrunL2, Option.bind_some, hL2]
        have := run_append _ _ _ B3 (asub_run (tauB c k1 k2 (sb c cn)) _ _ _ hr0)
        rw [this]
        simp only [List.map_cons, List.cons_append]
        rw [hB4]
      have htk1 : tauB c k1 k2 (sb c cn) k1 = sb c cn := by simp [tauB, hk1']
      have hgS : head (asub (tauB c k1 k2 (sb c cn)) g) = S := by
        rw [asub_headvar _ k1 g hg0, htk1]; exact hcn'
      have hargsg := asub_args_var (tauB c k1 k2 (sb c cn)) k1 (by rw [htk1]; exact hcn') g hg0
      rw [htk1] at hargsg
      have hstep1 : step (asub (tauB c k1 k2 (sb c cn)) g :: asub (tauB c k1 k2 (sb c cn)) x2 :: x3 :: B4) =
          some (args (sb c cn) ++ ((args g).map (asub (tauB c k1 k2 (sb c cn))) ++
            x3 :: app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4)) := by
        simp [step, hgS, hargsg]
      have hrun1 := run_succ_of _ (m1 + 1 + j0) _ _ hrun0 hstep1
      obtain ⟨e1, e2, B', he⟩ : ∃ e1 e2 B', (args g).map (asub (tauB c k1 k2 (sb c cn))) ++
          x3 :: app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4 = e1 :: e2 :: B' := by
        cases hag : (args g).map (asub (tauB c k1 k2 (sb c cn))) with
        | nil => exact ⟨x3, app (asub (tauB c k1 k2 (sb c cn)) x2) x3, B4, by simp⟩
        | cons a1 rest2 =>
          cases rest2 with
          | nil => exact ⟨a1, x3, app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4, by simp⟩
          | cons a2 rest3 => exact ⟨a1, a2, rest3 ++ x3 :: app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4, by simp⟩
      rw [he] at hrun1
      obtain ⟨Lr, hLr, hrem⟩ := run_prefix m (m1 + 1 + j0 + 1) _ _ hm (by omega)
      rw [hrun1] at hLr; injection hLr with hLr; subst hLr
      exact paf_post cn c k1 k2 hc hk1' hk2' hk12 hcnS hfc1 hfc2 hNH e1 e2 B' _ f' L' hrem hf'

#print axioms il_nh

/-- **THEOREM IL-GEN.**  As IL-NH, with the handler-only condition weakened to 'cn never calls its holes OR bn
    never calls its first hole'. -/
theorem il_gen (ws : List T) (bn cn : T) (c k1 k2 : Nat) (hc : c ≠ 0)
    (hk1 : 4 ≤ k1) (hk2 : 4 ≤ k2) (hk12 : k1 ≠ k2)
    (hbnS : head bn = S) (hcnS : head cn = S) (hfb1 : occN k1 bn = 0) (hfb2 : occN k2 bn = 0)
    (hfc1 : occN k1 cn = 0) (hfc2 : occN k2 cn = 0)
    (hcond : NHc cn k1 k2 ∨ ∀ (j : Nat) (g : T) (L : List T), run j (args bn ++ [var k1, var k2]) = some (g :: L) → head g ≠ var k1)
    (L0 : List T) (tI T' : Nat) (B2 : List T) (hI : run tI L0 = some (args bn ++ cn :: var 2 :: B2))
    (htT : tI ≤ T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T),
      run m [rcombT ((ws ++ [app bn cn]).map (sb c)) (var 0), var 1, var 2, var 3] = some (f' :: L') →
      head f' ≠ var 0 := by
  intro m f' L' hm hf'
  have hk1' : k1 ≠ 0 := by omega
  have hk2' : k2 ≠ 0 := by omega
  obtain ⟨Ln', hLn'⟩ : ∃ Ln', Ln' = app (app (sb c bn) (sb c cn)) (var 0) := ⟨_, rfl⟩
  have hD3 : rcombT ((ws ++ [app bn cn]).map (sb c)) (var 0) = rcombT (ws.map (sb c)) Ln' := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [rcombT_append, hLn']; simp [sb]
  rw [hD3] at hm
  have hbn' : head (sb c bn) = S := sb_head c bn hbnS
  have hcn' : head (sb c cn) = S := sb_head c cn hcnS
  have hLnS : head Ln' = S := by simp [hLn', head, hbn']
  have h0 : ∀ e ∈ [rcombT (ws.map (sb c)) Ln', var 1, var 2, var 3], guarded Ln' e := by
    intro e he
    simp at he
    rcases he with he | he | he | he <;> subst he
    · rw [hLn']; exact guarded_rcombT c hc _ ws
    · simp [guarded]
    · simp [guarded]
    · simp [guarded]
  rcases guarded_phase Ln' hLnS _ h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exact guarded_head Ln' (by rw [hLnS]; simp) f' (hG f' (by simp)) hf'
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    obtain ⟨us, hus, _⟩ := guarded_prefix_args Ln' f1 hwp (hg1 f1 (by rw [hL1]; simp))
    have hf1S : head f1 = S := by rw [wpre_headeq Ln' f1 hwp]; exact hLnS
    have hrunL2 : run (m1 + 1) [rcombT (ws.map (sb c)) Ln', var 1, var 2, var 3] = some L2 :=
      run_succ_of _ m1 L1 L2 hr1 hs2
    rw [hL1] at hs2
    simp only [step, hf1S, ite_true, Option.some.injEq] at hs2
    -- after the first innermost-level opening: the tauB-image of args bn ++ [k1, k2] over the bottom B3
    have hA : (args bn ++ [var k1, var k2]).map (asub (tauB c k1 k2 (sb c cn))) = args Ln' := by
      have hargsLn : args Ln' = args (sb c bn) ++ [sb c cn, var 0] := by simp [hLn', args]
      rw [hargsLn, sb_args c bn hbnS]
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hargs : (args bn).map (asub (tauB c k1 k2 (sb c cn))) = (args bn).map (sb c) := by
        apply List.map_congr_left
        intro s hs
        exact asub_tauB_sb c k1 k2 (sb c cn) hk1' hk2' s (occN_args k1 bn hfb1 s hs) (occN_args k2 bn hfb2 s hs)
      rw [hargs]
      simp [asub, tauB, hk1', hk2', hk12.symm]
    obtain ⟨B3, hB3⟩ : ∃ B3, B3 = us ++ d1 :: app b1 d1 :: R1 := ⟨_, rfl⟩
    have hL2 : L2 = (args bn ++ [var k1, var k2]).map (asub (tauB c k1 k2 (sb c cn))) ++ B3 := by
      rw [← hs2, hus, hA, hB3]; simp
    rw [hL2] at hrest
    have hB3ne : B3 ≠ [] := by rw [hB3]; simp
    -- the earlier-phase image of the same two-hole run: k1 -> cn, k2 -> y
    have hI' : run tI L0 = some ((args bn ++ [var k1, var k2]).map (asub (sg2 k1 k2 cn (var 2))) ++ B2) := by
      rw [hI]
      have hargs : (args bn).map (asub (sg2 k1 k2 cn (var 2))) = args bn := by
        have : (args bn).map (asub (sg2 k1 k2 cn (var 2))) = (args bn).map id := by
          apply List.map_congr_left
          intro s hs
          exact asub_sg2_id k1 k2 _ _ s (occN_args k1 bn hfb1 s hs) (occN_args k2 bn hfb2 s hs)
        simpa using this
      simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, sg2, Ne.symm hk12]
      simp
    have hnbA : 2 ≤ nHB k1 k2 (args bn ++ [var k1, var k2]) := by
      rw [nHB_append]
      have : nHB k1 k2 [var k1, var k2] = 2 := by simp [nHB, isHB, head]
      omega
    -- follow the next phase along bn's two-hole run until its first atom front
    have key : ∀ (j : Nat) (L'' : List T),
        run j ((args bn ++ [var k1, var k2]).map (asub (tauB c k1 k2 (sb c cn))) ++ B3) = some L'' →
        (∃ Aj, run j (args bn ++ [var k1, var k2]) = some Aj ∧
          L'' = Aj.map (asub (tauB c k1 k2 (sb c cn))) ++ B3) ∨
        (∃ j0 g rest, j0 < j ∧ run j0 (args bn ++ [var k1, var k2]) = some (g :: rest) ∧ head g = var k1) := by
      intro j
      induction j with
      | zero => intro L'' h; left; refine ⟨_, rfl, ?_⟩; simp only [run, Option.some.injEq] at h; exact h.symm
      | succ j ih =>
        intro L'' h
        obtain ⟨L3, hL3, hs⟩ := run_succ_split _ j L'' h
        rcases ih L3 hL3 with ⟨Aj, hAj, hL3e⟩ | ⟨j0, g, rest, hj0, hr0, hg0⟩
        · have hnb : 2 ≤ nHB k1 k2 Aj := Nat.le_trans hnbA (nHB_run k1 k2 j _ _ hAj)
          rw [hL3e] at hs
          obtain ⟨a, b', d', R', hlist, haS, hL''⟩ := step_some _ L'' hs
          match Aj, hnb, hlist, hAj with
          | [], hnb, _, _ => simp [nHB] at hnb
          | [g], hnb, _, _ => have := nHB_le_length k1 k2 [g]; simp at this; omega
          | g :: e2 :: rest, hnb, hlist, hAj =>
            rcases head_cases g with hg | ⟨n, hn⟩
            · -- S-headed abstract front: both runs step
              match rest, hnb, hlist, hAj with
              | [], hnb, _, hAj =>
                exfalso
                have hgb : isHB k1 k2 g = true := nHB_two_first k1 k2 g e2 hnb
                unfold isHB at hgb
                simp only [Bool.or_eq_true, decide_eq_true_eq] at hgb
                rcases hgb with hgb | hgb <;> rw [hgb] at hg <;> simp at hg
              | e3 :: rest', _, hlist, hAj =>
                left
                simp only [List.map_cons, List.cons_append, List.cons.injEq] at hlist
                obtain ⟨hga, hgb, hgd, hR⟩ := hlist
                have hstepA : step (g :: e2 :: e3 :: rest') = some (args g ++ e3 :: app e2 e3 :: rest') := by
                  simp [step, hg]
                refine ⟨args g ++ e3 :: app e2 e3 :: rest', run_succ_of _ j _ _ hAj hstepA, ?_⟩
                rw [hL'', ← hga, ← hgb, ← hgd, ← hR, asub_args _ g hg]
                simp [asub]
            · by_cases h1 : n = k1
              · subst h1; right; exact ⟨j, g, e2 :: rest, by omega, hAj, hn⟩
              · exfalso
                simp only [List.map_cons, List.cons_append, List.cons.injEq] at hlist
                rw [← hlist.1, asub_headvar _ n g hn] at haS
                simp only [tauB] at haS
                by_cases h0 : n = 0
                · rw [if_pos h0] at haS; simp [head] at haS
                · rw [if_neg h0, if_neg h1] at haS
                  by_cases h2 : n = k2
                  · rw [if_pos h2] at haS; simp [head] at haS
                  · rw [if_neg h2] at haS; simp [head] at haS
        · right; exact ⟨j0, g, rest, by omega, hr0, hg0⟩
    -- a second-hole front of bn's run would give the earlier phase a y-front before its p-front
    have no_k2 : ∀ j g rest, run j (args bn ++ [var k1, var k2]) = some (g :: rest) → head g ≠ var k2 := by
      intro j g rest hj hg2
      obtain ⟨hstuckE, _⟩ := image_stuck _ _ B2 L0 tI T' htT hI' f b d R hT hf j (g :: rest) hj
      have p2 : run (tI + j) L0 = some ((g :: rest).map (asub (sg2 k1 k2 cn (var 2))) ++ B2) := by
        rw [run_add tI _, hI', Option.bind_some]
        exact run_append _ _ _ B2 (asub_run _ _ _ _ hj)
      have hy : head (asub (sg2 k1 k2 cn (var 2)) g) = var 2 := by
        rw [asub_headvar _ k2 g hg2]; simp [sg2, Ne.symm hk12, head]
      have hnone : run (tI + j + 1) L0 = none := by
        rw [run_add (tI + j) 1, p2, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ (by rw [hy]; simp)]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      rw [← he.1, hy] at hf; injection hf with e; omega
    rcases key _ _ hrest with ⟨Aj, hAj, hLe⟩ | ⟨j0, g, rest, hj0, hr0, hg0⟩
    · -- still following bn's run: the p'-front would be a second-hole front
      match Aj, hLe, hAj with
      | [], _, hAj0 =>
        exfalso
        have hnb : 2 ≤ nHB k1 k2 ([] : List T) := Nat.le_trans hnbA (nHB_run k1 k2 _ _ _ hAj0)
        simp [nHB] at hnb
      | g :: rest, hLe, hAj =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hLe
        rw [hLe.1] at hf'
        rcases head_cases g with hg | ⟨n, hn⟩
        · rw [asub_headS _ g hg] at hf'; simp at hf'
        · rw [asub_headvar _ n g hn] at hf'
          by_cases h2 : n = k2
          · exact no_k2 _ g rest hAj (by rw [hn, h2])
          · simp only [tauB] at hf'
            by_cases h0 : n = 0
            · rw [if_pos h0] at hf'; simp [head] at hf'; exact hc hf'
            · rw [if_neg h0] at hf'
              by_cases h1 : n = k1
              · rw [if_pos h1] at hf'; rw [hcn'] at hf'; simp at hf'
              · rw [if_neg h1, if_neg h2] at hf'; simp [head] at hf'; exact h0 hf'
    · -- bn called its first hole at abstract time j0: from then on the next phase runs cn' (paf_post)
      have hNH : NHc cn k1 k2 := by
        rcases hcond with h | hNK1
        · exact h
        · exact absurd hg0 (hNK1 j0 g rest hr0)
      have hnb : 2 ≤ nHB k1 k2 (g :: rest) := Nat.le_trans hnbA (nHB_run k1 k2 _ _ _ hr0)
      obtain ⟨x2, rest', hrest'⟩ : ∃ x2 rest', rest = x2 :: rest' := by
        match rest, hnb with
        | [], hnb => have := nHB_le_length k1 k2 [g]; simp at this; omega
        | x2 :: rest', _ => exact ⟨x2, rest', rfl⟩
      subst hrest'
      obtain ⟨x3, B4, hB4⟩ : ∃ x3 B4, rest'.map (asub (tauB c k1 k2 (sb c cn))) ++ B3 = x3 :: B4 := by
        cases rest' with
        | nil =>
          cases hb3 : B3 with
          | nil => exact absurd hb3 hB3ne
          | cons x B => exact ⟨x, B, by simp⟩
        | cons x r => exact ⟨asub (tauB c k1 k2 (sb c cn)) x, r.map (asub (tauB c k1 k2 (sb c cn))) ++ B3, by simp⟩
      have hrun0 : run (m1 + 1 + j0) [rcombT (ws.map (sb c)) Ln', var 1, var 2, var 3] =
          some (asub (tauB c k1 k2 (sb c cn)) g :: asub (tauB c k1 k2 (sb c cn)) x2 :: x3 :: B4) := by
        rw [run_add (m1 + 1) j0, hrunL2, Option.bind_some, hL2]
        have := run_append _ _ _ B3 (asub_run (tauB c k1 k2 (sb c cn)) _ _ _ hr0)
        rw [this]
        simp only [List.map_cons, List.cons_append]
        rw [hB4]
      have htk1 : tauB c k1 k2 (sb c cn) k1 = sb c cn := by simp [tauB, hk1']
      have hgS : head (asub (tauB c k1 k2 (sb c cn)) g) = S := by
        rw [asub_headvar _ k1 g hg0, htk1]; exact hcn'
      have hargsg := asub_args_var (tauB c k1 k2 (sb c cn)) k1 (by rw [htk1]; exact hcn') g hg0
      rw [htk1] at hargsg
      have hstep1 : step (asub (tauB c k1 k2 (sb c cn)) g :: asub (tauB c k1 k2 (sb c cn)) x2 :: x3 :: B4) =
          some (args (sb c cn) ++ ((args g).map (asub (tauB c k1 k2 (sb c cn))) ++
            x3 :: app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4)) := by
        simp [step, hgS, hargsg]
      have hrun1 := run_succ_of _ (m1 + 1 + j0) _ _ hrun0 hstep1
      obtain ⟨e1, e2, B', he⟩ : ∃ e1 e2 B', (args g).map (asub (tauB c k1 k2 (sb c cn))) ++
          x3 :: app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4 = e1 :: e2 :: B' := by
        cases hag : (args g).map (asub (tauB c k1 k2 (sb c cn))) with
        | nil => exact ⟨x3, app (asub (tauB c k1 k2 (sb c cn)) x2) x3, B4, by simp⟩
        | cons a1 rest2 =>
          cases rest2 with
          | nil => exact ⟨a1, x3, app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4, by simp⟩
          | cons a2 rest3 => exact ⟨a1, a2, rest3 ++ x3 :: app (asub (tauB c k1 k2 (sb c cn)) x2) x3 :: B4, by simp⟩
      rw [he] at hrun1
      obtain ⟨Lr, hLr, hrem⟩ := run_prefix m (m1 + 1 + j0 + 1) _ _ hm (by omega)
      rw [hrun1] at hLr; injection hLr with hLr; subst hLr
      exact paf_post cn c k1 k2 hc hk1' hk2' hk12 hcnS hfc1 hfc2 hNH e1 e2 B' _ f' L' hrem hf'

#print axioms il_gen


/-! ## S1 Part 14: R3-RC for single-wrapper handlers - right combs over p with closed wrappers -/

theorem ordT_closed : ∀ t : T, rk t = 0 → ordT t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    have hf : rk f = 0 := by have := rk_app_left f x; omega
    have hx : rk x = 0 := by have := rk_app_right f x; omega
    refine ⟨ordT_closed f hf, ordT_closed x hx, ?_⟩
    intro _ a ha
    have := rk_args_le f a ha; omega

theorem rcombT_rk_occ (ds : List T) (hds : ∀ d ∈ ds, rk d = 0) :
    ordT (rcombT ds (var 0)) ∧ occN 0 (rcombT ds (var 0)) = 1 ∧ occN 1 (rcombT ds (var 0)) = 0 ∧
      occN 2 (rcombT ds (var 0)) = 0 ∧ occN 3 (rcombT ds (var 0)) = 0 ∧ rk (rcombT ds (var 0)) = 1 := by
  induction ds with
  | nil => simp [rcombT, ordT, occN, rk]
  | cons d ds ih =>
    obtain ⟨ho, h0, h1, h2, h3, hr⟩ := ih (fun d' hd' => hds d' (by simp [hd']))
    have hd : rk d = 0 := hds d (by simp)
    have hd' := (rk_eq0 d).1 hd
    simp only [rcombT, occN]
    refine ⟨⟨ordT_closed d hd, ho, ?_⟩, by omega, by omega, by omega, by omega, ?_⟩
    · intro _ a ha; have := rk_args_le d a ha; omega
    · rw [rk_app, hd, hr]; rfl

/-- **R3-RC (single-wrapper handlers).**  For every S-headed right comb D = d1.(d2.(...(dk.p))) over p whose
    wrappers d_i are closed (free of p, x, y, r; frozen atoms allowed) - in particular for every datum of a Church
    chain after its first transfer - if phase 2 transfers a single-wrapper handler (b0.c0).y (b0, c0 S-headed,
    b0.c0 free of x, y, r) and H1ok(c0) or 'b0 never calls its first hole' holds, then the next phase never makes a
    proper transfer.  (r3_single2 with ordT and the single occurrence of p derived from the comb shape.) -/
theorem r3_rc_single (ds : List T) (b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : 4 ≤ h1)
    (hh2 : 4 ≤ h2) (h12 : h1 ≠ h2) (hH : 4 ≤ H) (hds : ∀ d ∈ ds, rk d = 0)
    (hDS : head (rcombT ds (var 0)) = S) (hDh1 : occN h1 (rcombT ds (var 0)) = 0)
    (hDh2 : occN h2 (rcombT ds (var 0)) = 0)
    (hb0S : head b0 = S) (hc0S : head c0 = S) (hw1 : occN 1 (app b0 c0) = 0) (hw2 : occN 2 (app b0 c0) = 0)
    (hw3 : occN 3 (app b0 c0) = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (T' : Nat) (f b : T) (R : List T)
    (hT : run T' [rcombT ds (var 0), var 1, var 2, var 3] = some (f :: b :: app (app b0 c0) (var 2) :: R))
    (hf : head f = var 0)
    (hcond : (∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R')) ∨
      (∀ (m : Nat) (g : T) (L : List T), run m (args b0 ++ [var h1, var h2]) = some (g :: L) → head g ≠ var h1)) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  obtain ⟨ho, h0, h1', h2', h3', _⟩ := rcombT_rk_occ ds hds
  exact r3_single2 (rcombT ds (var 0)) b0 c0 c h1 h2 H hc hc2 hh1 hh2 h12 hH hDS ho h1' h2' h3' (by omega)
    hDh1 hDh2 hb0S hc0S hw1 hw2 hw3 hV T' f b R hT hf hcond

#print axioms r3_rc_single

/-! non-vacuity of il_atom: the datum S(S(S(S(SS))S))(S(SS)p) (handler S.((S(SS)p).y), innermost c-code p) -/
def exD2 : T := app (app S (app S (app (app S (app S (app S S))) S))) (app (app S (app S S)) (var 0))
def exL2 : T := app (app (app S (app S S)) (var 0)) (var 2)

theorem exD2_reopen : run 7 [exD2, var 1, var 2, var 3] = some (args (app S (app S S)) ++ var 0 :: var 2 ::
    [app S exL2, app (var 2) exL2, app (app (app S exL2) (app exL2 (app S exL2))) (app (var 2) exL2),
     app (var 1) (var 2), var 3]) := by decide

theorem exD2_transfer : run 9 [exD2, var 1, var 2, var 3] = some (app (var 0) (var 2) ::
    app (var 2) (app (var 0) (var 2)) :: app S exL2 ::
    [app (var 2) exL2, app (app (app S exL2) (app exL2 (app S exL2))) (app (var 2) exL2),
     app (var 1) (var 2), var 3]) := by decide

/-- non-vacuity: il_atom applies to S(S(S(S(SS))S))(S(SS)p) - the next phase of its two-wrapper handler
    S.((S(SS)p).y) has no p'-front at all -/
theorem il_atom_example : ∀ (m : Nat) (f' : T) (L' : List T),
    run m [rcombT (([S] ++ [app (app S (app S S)) (var 0)]).map (sb 4)) (var 0), var 1, var 2, var 3] =
      some (f' :: L') → head f' ≠ var 0 :=
  il_atom [S] (app S (app S S)) (var 0) 0 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) [exD2, var 1, var 2, var 3] 7 9 _ exD2_reopen (by decide) _ _ _ _
    exD2_transfer rfl

#print axioms il_atom_example

/-! non-vacuity of mw_alpha2: the datum SSS(S(SS(SS)(Sp))) (handler SS(Sp).(S(S(SS(SS)(Sp))).y), nested alpha) -/
def exD3 : T := app (app (app S S) S) (app S (app (app (app S S) (app S S)) (app S (var 0))))
def exc2 : T := app S (app (app (app S S) (app S S)) (app S (var 0)))

theorem noPre_of_check (w : T) (L0 : List T) (t : Nat)
    (h : (match run t L0 with | some (g :: _) => wpreB w g | _ => false) = false) :
    ∀ g L, run t L0 = some (g :: L) → ¬ wpre w g := by
  intro g L hr hw
  rw [hr] at h
  simp only at h
  rw [(wpreB_iff w g).2 hw] at h
  exact Bool.noConfusion h

theorem exD3_inner : run 2 [exD3, var 1, var 2, var 3] =
    some (exc2 :: app S exc2 :: var 2 :: [app (var 1) (var 2), var 3]) := by decide

theorem exD3_outer : run 5 [exD3, var 1, var 2, var 3] =
    some (app S (var 0) :: app (app S S) (app S (var 0)) :: app (app S exc2) (var 2) ::
      [app (var 2) (app (app S exc2) (var 2)), app (var 1) (var 2), var 3]) := by decide

theorem exD3_transfer : run 6 [exD3, var 1, var 2, var 3] =
    some (var 0 :: app (app S exc2) (var 2) ::
      app (app (app S S) (app S (var 0))) (app (app S exc2) (var 2)) ::
      [app (var 2) (app (app S exc2) (var 2)), app (var 1) (var 2), var 3]) := by decide

/-- non-vacuity: mw_alpha2 applies to SSS(S(SS(SS)(Sp))) -/
theorem mw_alpha2_example : ∀ (m : Nat) (f' b' d' : T) (R' : List T),
    run m [rcombT ([app (app S S) (app S (var 0)), app S exc2].map (sb 4)) (var 0), var 1, var 2, var 3] =
      some (f' :: b' :: d' :: R') → head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 :=
  mw_alpha2 (app S S) (app S (var 0)) S exc2 4 5 6 7 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide⟩
    [exD3, var 1, var 2, var 3] 2 5 6 _ _ exD3_inner exD3_outer (by decide) (by decide) _ _ _ _ exD3_transfer rfl
    (by
      intro t g L h1 h2 hr
      have ht : t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
      rcases ht with rfl | rfl | rfl | rfl
      · exact noPre_of_check _ _ _ (by decide) g L hr
      · exact noPre_of_check _ _ _ (by decide) g L hr
      · exact noPre_of_check _ _ _ (by decide) g L hr
      · exact noPre_of_check _ _ _ (by decide) g L hr)

#print axioms mw_alpha2_example

/-! ## S1 Part 15: THEOREM S1 with an arbitrary rank-2 Y-top Λ (for outer levels of multi-wrapper handlers) -/

/-- U.V was created at some time s <= t by a step with the bare y as Y-top: run s L1 = k :: U :: V :: y :: R -/
def GoodL (L1 : List T) (Λ : T) (t : Nat) (U V : T) : Prop :=
  ∃ s, s ≤ t ∧ ∃ k R, run s L1 = some (k :: U :: V :: Λ :: R)

/-- every 2P term on the right spine of a term is GoodL -/
def rsgL (L1 : List T) (Λ : T) (t : Nat) : T → Prop
  | app U V => (rk U = 1 ∧ rk V = 1) → (GoodL L1 Λ t U V ∧ rsgL L1 Λ t V)
  | _ => True

theorem rsg_monoL (L1 : List T) (Λ : T) (hΛ : rk Λ = 2) (t t' : Nat) (htt : t ≤ t') : ∀ Z, rsgL L1 Λ t Z → rsgL L1 Λ t' Z
  | S, _ => trivial
  | var _, _ => trivial
  | app U V, h => by
    intro hUV
    obtain ⟨⟨s, hs, hk⟩, hr⟩ := h hUV
    exact ⟨⟨s, by omega, hk⟩, rsg_monoL L1 Λ hΛ t t' htt V hr⟩

theorem rsg_of_not2PL (L1 : List T) (Λ : T) (hΛ : rk Λ = 2) (t : Nat) (Z : T) (h : ¬ twoP Z) : rsgL L1 Λ t Z := by
  match Z, h with
  | S, _ => trivial
  | var _, _ => trivial
  | app U V, h => intro hUV; exact absurd hUV h

def IAL (L1 : List T) (Λ : T) (t : Nat) (L : List T) : Prop :=
  ∀ Z, twoP Z → ((Z ∈ Preg L ∧ Ytop L = some (Λ)) ∨ (∃ e ∈ L, sub (app Z (Λ)) e)) → rsgL L1 Λ t Z

theorem ia_stepL (L1 : List T) (Λ : T) (hΛ : rk Λ = 2) (t : Nat) (a b c : T) (R : List T) (ha : head a = S)
    (hrun : run t L1 = some (a :: b :: c :: R))
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (h2' : (Preg (args a ++ c :: app b c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hc2 : IC2 (a :: b :: c :: R))
    (hc1' : IC1 (args a ++ c :: app b c :: R))
    (hia : IAL L1 Λ t (a :: b :: c :: R)) : IAL L1 Λ (t + 1) (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hna : noKZ a := hc2 a (by simp)
  have hoa : ordT a := hseg.2 a (by simp)
  have mono : ∀ Z, rsgL L1 Λ t Z → rsgL L1 Λ (t + 1) Z := rsg_monoL L1 Λ hΛ t (t + 1) (by omega)
  intro Z hZ hcase
  rcases hcase with ⟨hZin, hY⟩ | ⟨e, he, hsub⟩
  · rw [Preg_append] at hZin
    unfold Ytop at hY
    rw [Yl_append] at hY
    rcases rk_cases c with hc | hc | hc
    · have ha0 : rk a = 0 := by omega
      have hb0 : rk b = 0 := by omega
      have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
      rw [Preg_args_closed a ha0] at hZin
      rw [Yl_args_le1 a (by omega)] at hY
      simp only [Preg_cons, Yl_cons, hc, hbc0] at hZin hY
      simp at hZin hY
      apply mono; apply hia Z hZ; left
      refine ⟨by simp only [Preg_cons, ha0, hb0, hc]; simpa using hZin, ?_⟩
      unfold Ytop; simp only [Yl_cons, ha0, hb0, hc]; simpa using hY
    · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      have ha0 : rk a = 0 := by
        rcases rk_cases a with h | h | h
        · exact h
        · exfalso
          have hb1 : rk b = 1 := by omega
          simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
        · omega
      rw [Preg_args_closed a ha0] at hZin
      rw [Yl_args_le1 a (by omega)] at hY
      have hc2' : rk c ≠ 2 := by omega
      have hbc2 : rk (app b c) ≠ 2 := by omega
      simp only [Preg_cons, Yl_cons, hc, hbc1, hc2', hbc2, if_true, if_false, List.nil_append] at hZin hY
      simp at hY
      have hYL : Ytop (a :: b :: c :: R) = some (Λ) := by
        unfold Ytop; simp only [Yl_cons]
        have ha2 : rk a ≠ 2 := by omega
        have hb2 : rk b ≠ 2 := by omega
        simp [ha2, hb2, hc2', hY]
      simp at hZin
      rcases hZin with hZc | hZbc | hZR
      · subst hZc
        apply mono; apply hia Z hZ; left
        refine ⟨?_, hYL⟩
        simp only [Preg_cons, ha0, hc]
        by_cases hb1 : rk b = 1 <;> simp [hb1]
      · subst hZbc
        obtain ⟨hb1, _⟩ := hZ
        intro _
        have hR : Preg R = [] := by
          have h2'' := h2
          simp [Preg_cons, ha0, hb1, hc] at h2''
          first | exact h2'' | exact List.eq_nil_of_length_eq_zero (by omega)
        have hR2 : ∀ x ∈ R, rk x = 2 := by
          intro x hx
          have := hcR x hx
          rcases rk_cases x with h | h | h
          · omega
          · exfalso
            have : x ∈ Preg R := by unfold Preg; simp [hx, h]
            rw [hR] at this; simp at this
          · exact h
        have hYR : Yl R = R := by
          unfold Yl; rw [List.filter_eq_self]; intro x hx; simp [hR2 x hx]
        rw [hYR] at hY
        obtain ⟨R', hR'⟩ : ∃ R', R = Λ :: R' := by
          match R, hY with
          | x :: R', hY => simp at hY; exact ⟨R', by rw [hY]⟩
        refine ⟨⟨t, by omega, a, R', by rw [hrun, hR']⟩, ?_⟩
        by_cases h2c : twoP c
        · apply mono; apply hia c h2c; left
          exact ⟨by simp only [Preg_cons, ha0, hb1, hc]; simp, hYL⟩
        · exact rsg_of_not2PL L1 Λ hΛ (t + 1) c h2c
      · apply mono; apply hia Z hZ; left
        refine ⟨?_, hYL⟩
        simp only [Preg_cons, ha0, hc]
        by_cases hb1 : rk b = 1 <;> simp [hb1, hZR]
    · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
      have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
      have hPL' : Preg (args a ++ c :: app b c :: R) = Preg (args a) := by
        rw [Preg_append]; simp only [Preg_cons, hc, hbc2, hR]; simp
      simp only [Preg_cons, hc, hbc2, hR] at hZin
      simp at hZin
      have hlen : (Preg (args a)).length ≤ 2 := by rw [← hPL']; exact h2'
      rcases rk_cases a with ha' | ha' | ha'
      · rw [Preg_args_closed a ha'] at hZin; simp at hZin
      · -- P-front
        rw [Yl_args_le1 a (by omega)] at hY
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        rcases mem_short _ Z hZin hlen with hP | ⟨V', hP⟩ | ⟨V', hP⟩
        · exact absurd hZ (hc1' Z (by rw [hPL', hP]))
        · exact absurd hZ (first_P_arg_not2P a ha hoa hna Z [V'] hP)
        · obtain ⟨M', hM'1, haM, _⟩ := pair_prefix a ha hoa V' Z hP
          have haeq : a = app M' Z := haM (Yl_args_le1 a (by omega))
          have hZ1 : rk Z = 1 := twoP_rk Z hZ
          have h2a : twoP a := by rw [haeq]; exact ⟨hM'1, hZ1⟩
          have hb1 : rk b = 1 := by
            rcases rk_cases b with h | h | h
            · omega
            · exact h
            · exfalso
              apply hc1 a _ h2a
              have hb2 : rk b ≠ 1 := by omega
              have hc2' : rk c ≠ 1 := by omega
              simp only [Preg_cons, ha', hb2, hc2', hR]; simp
          have hYL : Ytop (a :: b :: c :: R) = some (Λ) := by
            rw [Ytop_third a b c R (by omega) (by omega) hc, hY]
          have := hia a h2a (Or.inl ⟨by simp only [Preg_cons, ha']; simp, hYL⟩)
          rw [haeq] at this
          exact mono Z (this ⟨hM'1, hZ1⟩).2
      · -- Y-front
        obtain ⟨y', Y', hYa⟩ : ∃ y' Y', Yl (args a) = y' :: Y' := by
          have hne := Yl_args_ne_nil a ha ha'
          cases h : Yl (args a) with
          | nil => exact absurd h hne
          | cons y' Y' => exact ⟨y', Y', rfl⟩
        rw [hYa] at hY
        simp at hY
        subst hY
        rcases mem_short _ Z hZin hlen with hP | ⟨V', hP⟩ | ⟨V', hP⟩
        · exact absurd hZ (hc1' Z (by rw [hPL', hP]))
        · exact absurd hZ (first_P_arg_not2P a ha hoa hna Z [V'] hP)
        · obtain ⟨M', hM'1, _, hsubA⟩ := pair_prefix a ha hoa V' Z hP
          have h2M : twoP (app M' Z) := ⟨hM'1, twoP_rk Z hZ⟩
          have := hia (app M' Z) h2M (Or.inr ⟨a, by simp, hsubA _ _ hYa⟩)
          exact mono Z (this h2M).2
  · simp at he
    rcases he with he | he | he | he
    · exact mono Z (hia Z hZ (Or.inr ⟨a, by simp, sub_trans _ _ _ hsub (sub_of_args a e he)⟩))
    · rw [he] at hsub; exact mono Z (hia Z hZ (Or.inr ⟨c, by simp, hsub⟩))
    · rw [he] at hsub
      rcases hsub with h | h | h
      · injection h with hZb hyc
        subst hZb; subst hyc
        have hb1 : rk Z = 1 := twoP_rk Z hZ
        apply mono; apply hia Z hZ; left
        refine ⟨?_, Ytop_third a Z (Λ) R (by omega) (by omega) hΛ⟩
        simp only [Preg_cons, hb1]
        by_cases ha1 : rk a = 1 <;> simp [ha1]
      · exact mono Z (hia Z hZ (Or.inr ⟨b, by simp, h⟩))
      · exact mono Z (hia Z hZ (Or.inr ⟨c, by simp, h⟩))
    · exact mono Z (hia Z hZ (Or.inr ⟨e, by simp [he], hsub⟩))

/-- (S1) has occurred by time t: some list args(c0) ++ [w, y | B] -/
def S1occL (L1 : List T) (Λ : T) (t : Nat) (c0 w : T) : Prop :=
  ∃ s, s ≤ t ∧ ∃ B, run s L1 = some (args c0 ++ w :: Λ :: B)

def IBL (L1 : List T) (Λ : T) (w c0 : T) (t : Nat) (L : List T) : Prop :=
  ∀ U, Preg L = [U, w] → inX c0 U → U ≠ c0 → Ytop L = some (Λ) → S1occL L1 Λ t c0 w

/-- at a GOOD time the P-region is the pair [M, w] over the bare y -/
theorem good_pairL (Λ : T) (hΛ : rk Λ = 2) (k M w : T) (R : List T) (hS : Seg (k :: M :: w :: Λ :: R))
    (h2 : (Preg (k :: M :: w :: Λ :: R)).length ≤ 2) (hM : rk M = 1) (hw : rk w = 1) :
    Preg (k :: M :: w :: Λ :: R) = [M, w] ∧ Ytop (k :: M :: w :: Λ :: R) = some (Λ) := by
  have hkM := srt_tail_ge k _ hS.1 M (by simp)
  have hyR := srt_tail_ge (Λ) R (srt_tail w _ (srt_tail M _ (srt_tail k _ hS.1)))
  rw [hΛ] at hyR
  have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hyR e he; omega)
  have hk0 : rk k = 0 := by
    rcases rk_cases k with h | h | h
    · exact h
    · exfalso; simp only [Preg_cons, h, hM, hw, if_true, List.length_cons] at h2; omega
    · omega
  have hk2 : rk k ≠ 2 := by omega
  have hM2 : rk M ≠ 2 := by omega
  have hw2 : rk w ≠ 2 := by omega
  refine ⟨?_, ?_⟩
  · simp only [Preg_cons, hk0, hM, hw, hΛ, hR]; simp
  · unfold Ytop; simp only [Yl_cons, hk2, hM2, hw2, hΛ]; simp

theorem ib_stepL (L1 : List T) (Λ : T) (hΛ : rk Λ = 2) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1) (t : Nat)
    (a b c : T) (R : List T) (ha : head a = S) (hrun : run t L1 = some (a :: b :: c :: R))
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hiw : IW w c0 (a :: b :: c :: R)) (hia : IAL L1 Λ t (a :: b :: c :: R))
    (hist : ∀ s Ls, s ≤ t → run s L1 = some Ls → IBL L1 Λ w c0 s Ls)
    (hbound : ∀ s Ls, s ≤ t → run s L1 = some Ls → (Preg Ls).length ≤ 2)
    (hsegs : ∀ s Ls, run s L1 = some Ls → Seg Ls) :
    IBL L1 Λ w c0 (t + 1) (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hoa : ordT a := hseg.2 a (by simp)
  have hwa : wsubOK w c0 a := hiw.1 a (by simp)
  have hstep : step (a :: b :: c :: R) = some (args a ++ c :: app b c :: R) := by simp [step, ha]
  have hrun' := run_succ_of L1 t _ _ hrun hstep
  have mono : S1occL L1 Λ t c0 w → S1occL L1 Λ (t + 1) c0 w := by
    rintro ⟨s, hs, B, hB⟩; exact ⟨s, by omega, B, hB⟩
  have monoS : ∀ s, s ≤ t → S1occL L1 Λ s c0 w → S1occL L1 Λ (t + 1) c0 w := by
    rintro s hst ⟨s', hs', B, hB⟩; exact ⟨s', by omega, B, hB⟩
  -- from a GOOD pair [M, w] at an earlier time to (S1)
  have fromGood : ∀ M, rk M = 1 → inX c0 M → M ≠ c0 → GoodL L1 Λ t M w → S1occL L1 Λ (t + 1) c0 w := by
    rintro M hM1 hXM hMc ⟨s, hs, k, R', hks⟩
    have hSs := hsegs s _ hks
    obtain ⟨hPs, hYs⟩ := good_pairL Λ hΛ k M w R' hSs (hbound s _ hs hks) hM1 hwr
    exact monoS s hs (hist s _ hs hks M hPs hXM hMc hYs)
  intro U hU hX hne hY
  have hU0 := hU
  rw [Preg_append] at hU
  rcases rk_cases c with hc | hc | hc
  · have ha0 : rk a = 0 := by omega
    have hb0 : rk b = 0 := by omega
    have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
    rw [Preg_args_closed a ha0] at hU
    simp only [Preg_cons, hc, hbc0] at hU
    apply mono
    apply hist t _ (Nat.le_refl t) hrun U _ hX hne
    · unfold Ytop at hY ⊢
      rw [Yl_append, Yl_args_le1 a (by omega)] at hY
      simp only [Yl_cons, ha0, hb0, hc, hbc0] at hY ⊢
      simpa using hY
    · simp only [Preg_cons, ha0, hb0, hc]; simpa using hU
  · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
    have ha0 : rk a = 0 := by
      rcases rk_cases a with h | h | h
      · exact h
      · exfalso
        have hb1 : rk b = 1 := by omega
        simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
      · omega
    rw [Preg_args_closed a ha0] at hU
    simp only [Preg_cons, hc, hbc1, if_true, List.nil_append] at hU
    have h1 := List.cons.inj hU
    have h2' := List.cons.inj h1.2
    have hbcw : app b c = w := h2'.1
    rw [hw] at hbcw
    injection hbcw with _ hcc
    exact absurd (by rw [← h1.1, hcc]) hne
  · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
    have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
    simp only [Preg_cons, hc, hbc2, hR] at hU
    simp at hU
    obtain ⟨M, hMS, hM1, hMU, hsub, C, Y, hargs, hMA, hC, hYY⟩ := release_pair a ha hoa U w hU
    have hXM : inX c0 M := (wsubOK_sub w c0 _ a hwa hsub).2.2 rfl hM1
    have hU1 : rk U = 1 := by
      have : U ∈ Preg (args a) := by rw [hU]; simp
      unfold Preg at this; simp at this; exact this.2
    have hYa : Yl (args a) = Y := by
      rw [hargs]
      have := Yl_split C [U, w] Y hC (by simp [hU1, hwr]) hYY
      simpa using this
    by_cases hMc : M = c0
    · -- the front has prefix c0.w: (S1) right now
      subst hMc
      refine ⟨t + 1, Nat.le_refl _, ?_⟩
      have hL' : args a ++ c :: app b c :: R = args M ++ w :: (Y ++ c :: app b c :: R) := by
        rw [hargs, hMA]; simp
      unfold Ytop at hY
      rw [Yl_append, hYa] at hY
      cases Y with
      | nil =>
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        subst c
        exact ⟨app b (Λ) :: R, by rw [hrun', hL']; simp⟩
      | cons y' Y' =>
        simp at hY
        subst y'
        exact ⟨Y' ++ c :: app b c :: R, by rw [hrun', hL']; simp⟩
    · rcases rk_cases a with ha' | ha' | ha'
      · rw [Preg_args_closed a ha'] at hU; simp at hU
      · -- P-front a = M.w over the bare y
        have hY0 : Y = [] := by rw [← hYa]; exact Yl_args_le1 a (by omega)
        subst hY0
        obtain ⟨M2, hM2S, hM2A, haeq⟩ := spine_last a ha (C ++ [U]) w (by rw [hargs]; simp)
        have hM2 : M2 = M := spine_eq M2 M hM2S hMS (by rw [hM2A, hMA])
        rw [hM2] at haeq
        have h2a : twoP a := by rw [haeq]; exact ⟨hM1, hwr⟩
        have hb1 : rk b = 1 := by
          rcases rk_cases b with h | h | h
          · omega
          · exact h
          · exfalso
            apply hc1 a _ h2a
            have hb2 : rk b ≠ 1 := by omega
            have hc2' : rk c ≠ 1 := by omega
            simp only [Preg_cons, ha', hb2, hc2', hR]; simp
        unfold Ytop at hY
        rw [Yl_append, hYa] at hY
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        have hYL : Ytop (a :: b :: c :: R) = some (Λ) := by
          rw [Ytop_third a b c R (by omega) (by omega) hc, hY]
        have hr := hia a h2a (Or.inl ⟨by simp only [Preg_cons, ha']; simp, hYL⟩)
        rw [haeq] at hr
        exact fromGood M hM1 hXM hMc (hr ⟨hM1, hwr⟩).1
      · -- Y-front (M.w).y ...
        unfold Ytop at hY
        rw [Yl_append, hYa] at hY
        cases Y with
        | nil => exact absurd hYa (Yl_args_ne_nil a ha ha')
        | cons y' Y' =>
          simp at hY
          subst y'
          obtain ⟨M2, hM2S, hM2A, hsub2⟩ := spine_prefix a ha (C ++ [U, w]) Y' (Λ) (by rw [hargs]; simp)
          obtain ⟨M3, hM3S, hM3A, hM2e⟩ := spine_last M2 hM2S (C ++ [U]) w (by rw [hM2A]; simp)
          have hM3 : M3 = M := spine_eq M3 M hM3S hMS (by rw [hM3A, hMA])
          rw [hM2e, hM3] at hsub2
          have h2M : twoP (app M w) := ⟨hM1, hwr⟩
          have hr := hia (app M w) h2M (Or.inr ⟨a, by simp, hsub2⟩)
          exact fromGood M hM1 hXM hMc (hr h2M).1

theorem s1_baseL (L1 : List T) (Λ : T) (hΛ : rk Λ = 2) (w c0 : T) (hwr : rk w = 1) (hp : (L1.map (occN 0)).sum ≤ 1) :
    IC1 L1 ∧ IC2 L1 ∧ IW w c0 L1 ∧ IAL L1 Λ 0 L1 ∧ IBL L1 Λ w c0 0 L1 := by
  have hel : ∀ e ∈ L1, occN 0 e ≤ 1 := fun e he => by have := mem_occ_le L1 e he; omega
  have hlen : (Preg L1).length ≤ 1 := by have := Preg_len_le_occ L1; omega
  refine ⟨?_, fun e he => noKZ_of_le1 e (hel e he), ⟨fun e he => wsubOK_of_le1 w c0 hwr e (hel e he), ?_⟩, ?_, ?_⟩
  · intro Z hZ h2Z
    have hZm : Z ∈ L1 := by
      have : Z ∈ Preg L1 := by rw [hZ]; simp
      unfold Preg at this; simp at this; exact this.1
    have := hel Z hZm; have := twoP_occ Z h2Z; omega
  · intro U hU; rw [hU] at hlen; simp at hlen
  · intro Z h2Z hcase
    exfalso
    rcases hcase with ⟨hZm, _⟩ | ⟨e, he, hsub⟩
    · have : Z ∈ L1 := by unfold Preg at hZm; simp at hZm; exact hZm.1
      have := hel Z this; have := twoP_occ Z h2Z; omega
    · have h1 := occN_sub_le 0 _ _ hsub
      have := hel e he; have := twoP_occ Z h2Z
      simp only [occN] at h1; omega
  · intro U hU; rw [hU] at hlen; simp at hlen

/-- the invariants hold at every time up to tmax -/
theorem s1_invL (L1 : List T) (Λ : T) (hΛ : rk Λ = 2) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1)
    (hS : Seg L1) (hp : (L1.map (occN 0)).sum ≤ 1) (tmax : Nat)
    (hbound : ∀ s Ls, s ≤ tmax → run s L1 = some Ls → (Preg Ls).length ≤ 2) :
    ∀ t, t ≤ tmax → ∀ s Ls, s ≤ t → run s L1 = some Ls →
      IC1 Ls ∧ IC2 Ls ∧ IW w c0 Ls ∧ IAL L1 Λ s Ls ∧ IBL L1 Λ w c0 s Ls := by
  have hsegs : ∀ s Ls, run s L1 = some Ls → Seg Ls := fun s Ls h => seg_run s L1 Ls hS h
  intro t
  induction t with
  | zero =>
    intro _ s Ls hs hr
    have : s = 0 := by omega
    subst this
    simp [run] at hr
    rw [← hr]
    exact s1_baseL L1 Λ hΛ w c0 hwr hp
  | succ t ih =>
    intro ht s Ls hs hr
    rcases Nat.lt_or_ge s (t + 1) with hst | hst
    · exact ih (by omega) s Ls (by omega) hr
    · have hs1 : s = t + 1 := by omega
      subst hs1
      obtain ⟨L, hL, hstep⟩ := run_succ_split L1 t Ls hr
      obtain ⟨a, b, c, R, rfl, ha, rfl⟩ := step_some L _ hstep
      obtain ⟨hc1, hc2, hiw, hia, _⟩ := ih (by omega) t _ (Nat.le_refl t) hL
      have hseg := hsegs t _ hL
      have h2 := hbound t _ (by omega) hL
      have h2' := hbound (t + 1) _ ht hr
      obtain ⟨hc1', hc2'⟩ := ic_step a b c R ha hseg h2 h2' hc1 hc2
      refine ⟨hc1', hc2', iw_step w b0 c0 hw hwr a b c R ha hseg h2 hiw,
        ia_stepL L1 Λ hΛ t a b c R ha hL hseg h2 h2' hc1 hc2 hc1' hia, ?_⟩
      exact ib_stepL L1 Λ hΛ w b0 c0 hw hwr t a b c R ha hL hseg h2 hc1 hiw hia
        (fun s' Ls' hs' hr' => (ih (by omega) s' Ls' hs' hr').2.2.2.2)
        (fun s' Ls' hs' hr' => hbound s' Ls' (by omega) hr') hsegs

/-- **THEOREM S1 (structural claim, generic form).**  Let a run start from a list L1 that is rank-sorted with
    hereditarily sorted spines (Seg) and contains at most ONE occurrence of p in total, and let it reach, at time T',
    a list whose third element contains x, y or r (e.g. a proper transfer).  If at a time tg <= T' the run passes
    through a glue list a1 :: w :: y :: R0 with w = b0.c0 a P-term and a1 a P-term different from c0, then at some
    time s <= tg the run passes through args(c0) ++ w :: y :: B ('c0 runs on (w, y)'). -/
theorem s1_coreL (L1 : List T) (Λ : T) (hΛ : rk Λ = 2) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1)
    (hS : Seg L1) (hp : (L1.map (occN 0)).sum ≤ 1)
    (T' : Nat) (f b d : T) (R : List T) (hT : run T' L1 = some (f :: b :: d :: R)) (hd : rk d = 2)
    (tg : Nat) (htg : tg ≤ T') (a1 : T) (R0 : List T) (hg : run tg L1 = some (a1 :: w :: Λ :: R0))
    (ha1 : rk a1 = 1) (hne : a1 ≠ c0) :
    ∃ s, s ≤ tg ∧ ∃ B, run s L1 = some (args c0 ++ w :: Λ :: B) := by
  have hbound : ∀ s Ls, s ≤ T' → run s L1 = some Ls → (Preg Ls).length ≤ 2 :=
    fun s Ls hs hr => ab3_bound L1 hS T' f b d R hT hd s Ls hs hr
  obtain ⟨_, _, hiw, _, hib⟩ := s1_invL L1 Λ hΛ w b0 c0 hw hwr hS hp T' hbound tg htg tg _ (Nat.le_refl _) hg
  have hSg := seg_run tg L1 _ hS hg
  have hyR := srt_tail_ge (Λ) R0 (srt_tail w _ (srt_tail a1 _ hSg.1))
  rw [hΛ] at hyR
  have hR0 : Preg R0 = [] := Preg_nil_of R0 (fun e he => by have := hyR e he; omega)
  have hP : Preg (a1 :: w :: Λ :: R0) = [a1, w] := by
    simp only [Preg_cons, ha1, hwr, hΛ, hR0]; simp
  have hY : Ytop (a1 :: w :: Λ :: R0) = some (Λ) := by
    have h1 : rk a1 ≠ 2 := by omega
    have h2 : rk w ≠ 2 := by omega
    unfold Ytop; simp only [Yl_cons, h1, h2, hΛ]; simp
  exact hib a1 hP (hiw.2 a1 hP) hne hY

#print axioms s1_coreL

#print axioms s1_coreL

/-! ## S1 Part 16: R3 for EVERY single-wrapper handler of an ordered single-occurrence datum -/

theorem head_sb_var (c n : Nat) (hc : c ≠ 0) : ∀ t : T, head t = var n → head (sb c t) ≠ var 0 ∧ head (sb c t) ≠ S
  | S, h => by simp [head] at h
  | var m, h => by
    simp [head] at h; subst h
    by_cases h0 : m = 0
    · subst h0; simp [sb, head, hc]
    · simp [sb, head, h0]
  | app f x, h => by
    simp only [head] at h
    simp only [sb, head]
    exact head_sb_var c n hc f h

/-- **THEOREM R3-SINGLE-ALL.**  For an S-headed ordered datum D free of x, y, r with at most one p, and ANY
    single-wrapper handler (b0.c0).y of a phase-2 transfer (b0.c0 free of x, y, r): the next phase never makes a
    proper transfer, provided - only when b0 and c0 are both S-headed - 'H1ok(c0) OR b0 never calls its first hole'.
    (b0 atom-headed: the next datum is atom-headed; c0 atom-headed: pah_main; both S-headed: r3_single2, where the
    condition is used only for a glue front that is a P-term other than c0.) -/
theorem r3_single_all (D b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : 4 ≤ h1) (hh2 : 4 ≤ h2)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H)
    (hDS : head D = S) (hDo : ordT D) (hD1 : occN 1 D = 0) (hD2 : occN 2 D = 0) (hD3 : occN 3 D = 0)
    (hDp : occN 0 D ≤ 1) (hDh1 : occN h1 D = 0) (hDh2 : occN h2 D = 0)
    (hw1 : occN 1 (app b0 c0) = 0) (hw2 : occN 2 (app b0 c0) = 0)
    (hw3 : occN 3 (app b0 c0) = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (T' : Nat) (f b : T) (R : List T)
    (hT : run T' [D, var 1, var 2, var 3] = some (f :: b :: app (app b0 c0) (var 2) :: R)) (hf : head f = var 0)
    (hcond : head b0 = S → head c0 = S →
      ((∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
        head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R')) ∨
       (∀ (m : Nat) (g : T) (L : List T), run m (args b0 ++ [var h1, var h2]) = some (g :: L) →
        head g ≠ var h1))) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  have hy0 : occ2 b0 = 0 := by rw [occ2_eq]; simp only [occN] at hw2; omega
  have hy1 : occ2 c0 = 0 := by rw [occ2_eq]; simp only [occN] at hw2; omega
  rcases head_cases b0 with hb0S | ⟨n, hn⟩
  · rcases head_cases c0 with hc0S | ⟨n', hn'⟩
    · exact r3_single2 D b0 c0 c h1 h2 H hc hc2 hh1 hh2 h12 hH hDS hDo hD1 hD2 hD3 hDp hDh1 hDh2 hb0S hc0S hw1 hw2
        hw3 hV T' f b R hT hf (hcond hb0S hc0S)
    · have hn2 : n' ≠ 2 := by
        intro e; subst e
        have : occ2 c0 ≠ 0 := by
          have key : ∀ t : T, head t = var 2 → occ2 t ≠ 0 := by
            intro t; induction t with
            | S => intro h; simp [head] at h
            | var m => intro h; simp [head] at h; subst h; simp [occ2]
            | app f x ihf _ => intro h; simp only [head] at h; simp only [occ2]; have := ihf h; omega
          exact key c0 hn'
        exact this hy1
      exact pah_main b0 c0 c n' hc2 hb0S hy0 hy1 hn' hn2
  · -- b0 atom-headed: the next datum is atom-headed, its run never moves
    intro m f' b' d' R' hm hf'
    obtain ⟨hne0, hneS⟩ := head_sb_var c n hc b0 hn
    have hD'h : head (app (app (sb c b0) (sb c c0)) (var 0)) = head (sb c b0) := rfl
    match m, hm with
    | 0, hm =>
      simp only [run, Option.some.injEq, List.cons.injEq] at hm
      rw [← hm.1, hD'h] at hf'; exact absurd hf' hne0
    | m' + 1, hm =>
      simp only [run] at hm
      rw [step_head_ne _ _ (by rw [hD'h]; exact hneS)] at hm
      simp at hm

#print axioms r3_single_all

/-! ## S1 Part 17: the abstract side of Lemma YT, and the B-form residual (BF -> NK1)
    If c0's two-hole run reaches the 'B-form' front h1.(X.h1) followed by h2 (X an S-headed hole-free P-term), then
    in pattern beta the earlier phase reaches args(b0) ++ [c0, X.w, y | R]; Lemma YT on the pair (c0, X.w), read on
    b0's abstract two-hole run, shows that b0's first hole front is its SECOND hole: NK1(b0) is DERIVED. -/

theorem run_two (a b : T) : ∀ (s : Nat) (g : T) (L : List T), run s [a, b] = some (g :: L) → g = a
  | 0, g, L, h => by simp [run] at h; exact h.1.symm
  | s + 1, g, L, h => by simp [run, step] at h

theorem chainE_headS (U V : T) (hU : head U = S) (hV : head V = S) : ∀ n, head (chainE U V n) = S
  | 0 => hU
  | 1 => hV
  | n + 2 => by simp only [chainE, head]; exact chainE_headS U V hU hV n

/-- **LEMMA YT, abstract side.**  Along the YT chain the abstract run of K ++ [U0, V0] (same closed code K, the pair
    replaced by U0, V0) has, at every reachable list, a front that is either free of the atom h (a K-element) or the
    chain element chainE U0 V0 j' where j' is the index at which the concrete run reaches its pair. -/
theorem yt_abs (L1 : List T) (T' : Nat) (f b d : T) (RT : List T)
    (hT : run T' L1 = some (f :: b :: d :: RT)) (hd : rk d = 2)
    (hbound : ∀ s Ls, s ≤ T' → run s L1 = some Ls → (Preg Ls).length ≤ 2)
    (U V Yt : T) (R : List T) (hU : rk U = 1) (hV : rk V = 1) (U0 V0 : T) (h : Nat) :
    ∀ (n : Nat) (t j : Nat) (K : List T), T' - t = n → t ≤ T' → (∀ k ∈ K, rk k = 0) →
      (∀ k ∈ K, occN h k = 0) →
      run t L1 = some (K ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) →
      ∃ t' j', t ≤ t' ∧ t' ≤ T' ∧ run t' L1 = some (chainE U V j' :: chainE U V (j' + 1) :: Yt :: R) ∧
        ∀ s g L, run s (K ++ [chainE U0 V0 j, chainE U0 V0 (j + 1)]) = some (g :: L) →
          occN h g = 0 ∨ g = chainE U0 V0 j' := by
  intro n
  induction n with
  | zero =>
    intro t j K hn ht hK hKh hr
    have htT : t = T' := by omega
    subst htT
    rw [hT] at hr
    injection hr with hr
    match K, hK, hKh, hr with
    | [], _, _, hr =>
      refine ⟨t, j, Nat.le_refl _, Nat.le_refl _, by rw [hT, hr]; simp, ?_⟩
      intro s g L hs
      right; exact run_two _ _ s g L (by simpa using hs)
    | [k1], _, _, hr =>
      simp at hr; obtain ⟨_, _, hd', _⟩ := hr
      rw [hd', chainE_rk U V hU hV] at hd; omega
    | [k1, k2], _, _, hr =>
      simp at hr; obtain ⟨_, _, hd', _⟩ := hr
      rw [hd', chainE_rk U V hU hV] at hd; omega
    | k1 :: k2 :: k3 :: K', hK, _, hr =>
      simp at hr; obtain ⟨_, _, hd', _⟩ := hr
      rw [hd', hK k3 (by simp)] at hd; omega
  | succ n ih =>
    intro t j K hn ht hK hKh hr
    match K, hK, hKh, hr with
    | [], _, _, hr =>
      refine ⟨t, j, Nat.le_refl _, ht, hr, ?_⟩
      intro s g L hs
      right; exact run_two _ _ s g L (by simpa using hs)
    | [k1], hK, hKh, hr =>
      have htT : t < T' := by omega
      have hk1S : head k1 = S := head_of_continue L1 t T' k1 _ _ _ hr htT _ hT
      have hstep : step ([k1] ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) =
          some (args k1 ++ chainE U V (j + 1) :: chainE U V (j + 2) :: Yt :: R) := by
        simp [step, hk1S, chainE]
      have hr' := run_succ_of L1 t _ _ hr hstep
      obtain ⟨t', j', h1, h2, h3, h4⟩ := ih (t + 1) (j + 1) (args k1) (by omega) (by omega)
        (fun k hk => by have := rk_args_le k1 k hk; rw [hK k1 (by simp)] at this; omega)
        (fun k hk => occN_args h k1 (hKh k1 (by simp)) k hk) hr'
      refine ⟨t', j', by omega, h2, h3, ?_⟩
      intro s g L hs
      cases s with
      | zero =>
        left; simp [run] at hs; obtain ⟨rfl, -⟩ := hs; exact hKh _ (by simp)
      | succ s =>
        have e : run (s + 1) ([k1] ++ [chainE U0 V0 j, chainE U0 V0 (j + 1)]) =
            run s (args k1 ++ [chainE U0 V0 (j + 1), chainE U0 V0 (j + 1 + 1)]) := by
          simp [run, step, hk1S, chainE]
        rw [e] at hs
        exact h4 s g L hs
    | [k1, k2], hK, _, hr =>
      exfalso
      have htT : t < T' := by omega
      have hk1S : head k1 = S := head_of_continue L1 t T' k1 _ _ _ hr htT _ hT
      have hstep : step ([k1, k2] ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) =
          some (args k1 ++ chainE U V j :: app k2 (chainE U V j) :: chainE U V (j + 1) :: Yt :: R) := by
        simp [step, hk1S]
      have hr' := run_succ_of L1 t _ _ hr hstep
      have hb := hbound (t + 1) _ (by omega) hr'
      have hk20 : rk k2 = 0 := hK k2 (by simp)
      have hk1a : Preg (args k1) = [] := Preg_args_closed k1 (hK k1 (by simp))
      have hj := chainE_rk U V hU hV j
      have hj1 := chainE_rk U V hU hV (j + 1)
      have hk2j : rk (app k2 (chainE U V j)) = 1 := by rw [rk_app, hk20, hj]; rfl
      rw [Preg_append, hk1a] at hb
      simp only [Preg_cons, hj, hk2j, hj1, if_true, List.nil_append, List.length_cons] at hb
      omega
    | k1 :: k2 :: k3 :: K', hK, hKh, hr =>
      have htT : t < T' := by omega
      have hk1S : head k1 = S := head_of_continue L1 t T' k1 _ _ _ hr htT _ hT
      have hstep : step ((k1 :: k2 :: k3 :: K') ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) =
          some ((args k1 ++ k3 :: app k2 k3 :: K') ++ chainE U V j :: chainE U V (j + 1) :: Yt :: R) := by
        simp [step, hk1S]
      have hr' := run_succ_of L1 t _ _ hr hstep
      have hk0 : ∀ k ∈ args k1 ++ k3 :: app k2 k3 :: K', rk k = 0 := by
        intro k hk
        simp at hk
        rcases hk with hk | hk | hk | hk
        · have := rk_args_le k1 k hk; rw [hK k1 (by simp)] at this; omega
        · rw [hk]; exact hK k3 (by simp)
        · rw [hk, rk_app, hK k2 (by simp), hK k3 (by simp)]; rfl
        · exact hK k (by simp [hk])
      have hkh : ∀ k ∈ args k1 ++ k3 :: app k2 k3 :: K', occN h k = 0 := by
        intro k hk
        simp at hk
        rcases hk with hk | hk | hk | hk
        · exact occN_args h k1 (hKh k1 (by simp)) k hk
        · rw [hk]; exact hKh k3 (by simp)
        · rw [hk]; simp only [occN]; rw [hKh k2 (by simp), hKh k3 (by simp)]
        · exact hKh k (by simp [hk])
      obtain ⟨t', j', h1, h2, h3, h4⟩ := ih (t + 1) j _ (by omega) (by omega) hk0 hkh hr'
      refine ⟨t', j', by omega, h2, h3, ?_⟩
      intro s g L hs
      cases s with
      | zero =>
        left; simp [run] at hs; obtain ⟨rfl, -⟩ := hs; exact hKh _ (by simp)
      | succ s =>
        have e : run (s + 1) ((k1 :: k2 :: k3 :: K') ++ [chainE U0 V0 j, chainE U0 V0 (j + 1)]) =
            run s ((args k1 ++ k3 :: app k2 k3 :: K') ++ [chainE U0 V0 j, chainE U0 V0 (j + 1)]) := by
          simp [run, step, hk1S]
        rw [e] at hs
        exact h4 s g L hs

/-- the B-form of an h1-front of a two-hole run: h1.(X.h1) followed by h2, as its next argument or at position 3 -/
def BFfront (X : T) (h1 h2 : Nat) (G : T) (L : List T) : Prop :=
  head G = var h1 ∧ ((args G = [app X (var h1)] ∧ ∃ b' L', L = b' :: var h2 :: L') ∨
    ∃ A, args G = app X (var h1) :: var h2 :: A)

theorem img_args (c e1 e2 : T) (h1 h2 : Nat) (h12 : h1 ≠ h2) (hf1 : occN h1 c = 0) (hf2 : occN h2 c = 0)
    (B : List T) :
    (args c ++ [var h1, var h2]).map (asub (sg2 h1 h2 e1 e2)) ++ B = args c ++ e1 :: e2 :: B := by
  have hs1 : sg2 h1 h2 e1 e2 h1 = e1 := by simp [sg2]
  have hs2 : sg2 h1 h2 e1 e2 h2 = e2 := by simp [sg2, Ne.symm h12]
  have hargs : (args c).map (asub (sg2 h1 h2 e1 e2)) = args c := by
    have : (args c).map (asub (sg2 h1 h2 e1 e2)) = (args c).map id := by
      apply List.map_congr_left
      intro e he'
      exact asub_sg2_id h1 h2 _ _ e (occN_args h1 c hf1 e he') (occN_args h2 c hf2 e he')
    simpa using this
  simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs1, hs2]
  simp

/-- opening the image of a B-form front (hole h1 -> e1, S-headed) lays out args(e1) ++ [X.e1, e2, ...] -/
theorem bf_step (X : T) (h1 h2 : Nat) (h12 : h1 ≠ h2) (hX1 : occN h1 X = 0) (hX2 : occN h2 X = 0)
    (e1 e2 : T) (he1 : head e1 = S) (G : T) (L B L'' : List T) (hG : BFfront X h1 h2 G L)
    (hs : step ((G :: L).map (asub (sg2 h1 h2 e1 e2)) ++ B) = some L'') :
    ∃ R', L'' = args e1 ++ app X e1 :: e2 :: R' := by
  obtain ⟨hGh, hGf⟩ := hG
  have hs1 : sg2 h1 h2 e1 e2 h1 = e1 := by simp [sg2]
  have hs2 : sg2 h1 h2 e1 e2 h2 = e2 := by simp [sg2, Ne.symm h12]
  have hXid : asub (sg2 h1 h2 e1 e2) X = X := asub_sg2_id h1 h2 e1 e2 X hX1 hX2
  have hargs : args (asub (sg2 h1 h2 e1 e2) G) = args e1 ++ (args G).map (asub (sg2 h1 h2 e1 e2)) := by
    rw [asub_args_var (sg2 h1 h2 e1 e2) h1 (by rw [hs1]; exact he1) G hGh, hs1]
  obtain ⟨a, b, c, R0, hL, _, hL''⟩ := step_some _ _ hs
  simp only [List.map_cons, List.cons_append] at hL
  injection hL with ha hrest
  rcases hGf with ⟨hA, b', L', hL'⟩ | ⟨A, hA⟩
  · subst hL'
    simp only [List.map_cons, List.cons_append] at hrest
    injection hrest with hb hrest2
    injection hrest2 with hc hR0
    have hc' : c = e2 := by rw [← hc]; simp [asub, hs2]
    refine ⟨app b c :: R0, ?_⟩
    rw [hL'', ← ha, hargs, hA, hc']
    simp [asub, hs1, hXid]
  · refine ⟨(A.map (asub (sg2 h1 h2 e1 e2))) ++ c :: app b c :: R0, ?_⟩
    rw [hL'', ← ha, hargs, hA]
    simp [asub, hs1, hs2, hXid]

theorem Preg_len_ge3 (A : List T) (e1 e2 : T) (B : List T) (hA : 1 ≤ (Preg A).length) (h1 : rk e1 = 1)
    (h2 : rk e2 = 1) : 3 ≤ (Preg (A ++ e1 :: e2 :: B)).length := by
  rw [Preg_append]
  simp only [Preg_cons, h1, h2, if_true, List.length_append, List.length_cons]
  omega

/-- **THEOREM BF-NK1.**  Let a run from L1 reach a p-front list with a rank-2 third element at T' (|P| <= 2 up to
    T').  If at a time t <= T' the list is args(b0) ++ [c0, X.w, y | R] (w = b0.c0, c0 and X S-headed P-terms, b0 of
    rank <= 1, holes h1, h2 fresh) and c0's two-hole run reaches a B-form front h1.(X.h1) followed by h2, then b0's
    two-hole run never reaches a first-hole front (NK1(b0)).  Proof: YT on the pair (c0, X.w) and its abstract side
    (yt_abs): b0's only possible hole front is E_j' (j' <= 3); j' = 0 makes c0 run on (y, ...) - its h1-front is a
    y-front; j' = 2 makes c0 run on (X.w, y) - opening its B-form front leaves 3 P-elements; so j' is odd. -/
theorem bform_nk1 (L1 : List T) (T' : Nat) (f b d : T) (RT : List T)
    (hT : run T' L1 = some (f :: b :: d :: RT)) (hd : rk d = 2) (hf : head f = var 0)
    (hbound : ∀ s Ls, s ≤ T' → run s L1 = some Ls → (Preg Ls).length ≤ 2)
    (b0 c0 X : T) (h1 h2 : Nat) (h12 : h1 ≠ h2)
    (hb0r : rk b0 ≤ 1) (hb0h1 : occN h1 b0 = 0) (hc0h1 : occN h1 c0 = 0) (hc0h2 : occN h2 c0 = 0)
    (hX1 : occN h1 X = 0) (hX2 : occN h2 X = 0)
    (hc0S : head c0 = S) (hc0r : rk c0 = 1) (hXS : head X = S) (hXr : rk X = 1)
    (t : Nat) (ht : t ≤ T') (R : List T)
    (hr : run t L1 = some (args b0 ++ c0 :: app X (app b0 c0) :: var 2 :: R))
    (m0 : Nat) (G : T) (LG : List T) (hm0 : run m0 (args c0 ++ [var h1, var h2]) = some (G :: LG))
    (hBF : BFfront X h1 h2 G LG) :
    ∀ (m : Nat) (g : T) (L : List T), run m (args b0 ++ [var h1, var h2]) = some (g :: L) → head g ≠ var h1 := by
  intro m g L hm hg
  have hwr : rk (app b0 c0) = 1 := by rw [rk_app, hc0r, Nat.max_eq_right hb0r]
  have hVr : rk (app X (app b0 c0)) = 1 := by rw [rk_app, hXr, hwr]; rfl
  have hVS : head (app X (app b0 c0)) = S := by simp [head, hXS]
  have hXVr : rk (app X (app X (app b0 c0))) = 1 := by rw [rk_app, hXr, hVr]; rfl
  -- b0's arguments are closed (|P| <= 2 at time t)
  have hK0 : ∀ k ∈ args b0, rk k = 0 := by
    intro k hk
    have hle := rk_args_le b0 k hk
    rcases Nat.lt_or_ge (rk k) 1 with h0 | h1'
    · omega
    · exfalso
      have hk1 : rk k = 1 := by omega
      have hb := hbound t _ ht hr
      rw [Preg_append] at hb
      simp only [Preg_cons, hc0r, hVr, if_true, List.length_append, List.length_cons] at hb
      have : 1 ≤ (Preg (args b0)).length := by
        unfold Preg; apply List.length_pos_iff_exists_mem.2; exact ⟨k, by simp [hk, hk1]⟩
      omega
  have hc0P : 1 ≤ (Preg (args c0)).length := by
    obtain ⟨s, hs, hs1⟩ := P_has_P_arg c0 hc0S hc0r
    unfold Preg; apply List.length_pos_iff_exists_mem.2; exact ⟨s, by simp [hs, hs1]⟩
  have hVP : 1 ≤ (Preg (args (app X (app b0 c0)))).length := by
    obtain ⟨s, hs, hs1⟩ := P_has_P_arg _ hVS hVr
    unfold Preg; apply List.length_pos_iff_exists_mem.2; exact ⟨s, by simp [hs, hs1]⟩
  have hXP : 1 ≤ (Preg (args X)).length := by
    obtain ⟨s, hs, hs1⟩ := P_has_P_arg X hXS hXr
    unfold Preg; apply List.length_pos_iff_exists_mem.2; exact ⟨s, by simp [hs, hs1]⟩
  obtain ⟨t', j', htt', ht'T, hrt', habs⟩ := yt_abs L1 T' f b d RT hT hd hbound c0 (app X (app b0 c0)) (var 2) R
    hc0r hVr (var h1) (var h2) h1 (T' - t) t 0 (args b0) rfl ht hK0 (occN_args h1 b0 hb0h1)
    (by simpa [chainE] using hr)
  rcases habs m g L (by simpa [chainE] using hm) with hocc | hgE
  · exact occN_head h1 g hg hocc
  · have hES : ∀ n, head (chainE c0 (app X (app b0 c0)) n) = S := chainE_headS _ _ hc0S hVS
    have ht'lt : t' < T' := by
      rcases Nat.lt_or_ge t' T' with h | h
      · exact h
      · exfalso
        have he : t' = T' := by omega
        rw [he, hT] at hrt'
        injection hrt' with hrt'
        injection hrt' with hf' _
        rw [hf', hES] at hf; simp at hf
    have hstep' : step (chainE c0 (app X (app b0 c0)) j' :: chainE c0 (app X (app b0 c0)) (j' + 1) :: var 2 :: R) =
        some (args (chainE c0 (app X (app b0 c0)) j') ++ var 2 ::
          app (chainE c0 (app X (app b0 c0)) (j' + 1)) (var 2) :: R) := by
      simp [step, hES]
    have hr1 := run_succ_of L1 t' _ _ hrt' hstep'
    have hj3 : j' ≤ 3 := by
      have hlen := Preg_args_chainE_len c0 _ hc0r hVr hc0P hVP j'
      have hb := hbound (t' + 1) _ (by omega) hr1
      rw [Preg_append] at hb
      simp only [List.length_append] at hb
      omega
    subst hgE
    rcases (by omega : j' = 0 ∨ j' = 1 ∨ j' = 2 ∨ j' = 3) with hj | hj | hj | hj <;> subst hj
    · -- j' = 0: c0 runs on (y, (X.w).y); its h1-front is a y-front
      have hr1' : run (t' + 1) L1 = some ((args c0 ++ [var h1, var h2]).map
          (asub (sg2 h1 h2 (var 2) (app (app X (app b0 c0)) (var 2)))) ++ R) := by
        rw [img_args c0 _ _ h1 h2 h12 hc0h1 hc0h2 R]; simpa [chainE] using hr1
      obtain ⟨hstuck, _⟩ := image_stuck _ _ R L1 (t' + 1) T' (by omega) hr1' f b d RT hT hf m0 (G :: LG) hm0
      have hy : head (asub (sg2 h1 h2 (var 2) (app (app X (app b0 c0)) (var 2))) G) = var 2 := by
        rw [asub_headvar _ h1 G hBF.1]; simp [sg2, head]
      have hne : head (asub (sg2 h1 h2 (var 2) (app (app X (app b0 c0)) (var 2))) G) ≠ S := by
        rw [hy]; simp
      have p2 : run (t' + 1 + m0) L1 = some ((G :: LG).map
          (asub (sg2 h1 h2 (var 2) (app (app X (app b0 c0)) (var 2)))) ++ R) := by
        rw [run_add (t' + 1) m0, hr1', Option.bind_some]
        exact run_append m0 _ _ R (asub_run _ m0 _ _ hm0)
      have hnone : run (t' + 1 + m0 + 1) L1 = none := by
        rw [run_add (t' + 1 + m0) 1, p2, Option.bind_some]
        simp only [List.map_cons, List.cons_append]
        simp [run, step_head_ne _ _ hne]
      obtain ⟨hfe, _⟩ := hstuck hnone
      simp only [List.map_cons, List.cons_append] at hfe
      injection hfe with hfe _
      rw [← hfe, hy] at hf; simp at hf
    · simp [chainE, head] at hg; exact h12 hg.symm
    · -- j' = 2: c0 runs on (X.w, y); opening its B-form front leaves 3 P-elements
      have hr1' : run (t' + 1) L1 = some ((args c0 ++ [var h1, var h2]).map
          (asub (sg2 h1 h2 (app X (app b0 c0)) (var 2))) ++
            (app (chainE c0 (app X (app b0 c0)) 3) (var 2) :: R)) := by
        rw [img_args c0 _ _ h1 h2 h12 hc0h1 hc0h2]; simpa [chainE, args] using hr1
      obtain ⟨_, hearly⟩ := image_stuck _ _ _ L1 (t' + 1) T' (by omega) hr1' f b d RT hT hf m0 (G :: LG) hm0
      have hge : t' + 1 + m0 ≤ T' := Nat.le_of_not_lt hearly
      have p2 : run (t' + 1 + m0) L1 = some ((G :: LG).map
          (asub (sg2 h1 h2 (app X (app b0 c0)) (var 2))) ++
            (app (chainE c0 (app X (app b0 c0)) 3) (var 2) :: R)) := by
        rw [run_add (t' + 1) m0, hr1', Option.bind_some]
        exact run_append m0 _ _ _ (asub_run _ m0 _ _ hm0)
      have hGS : head (asub (sg2 h1 h2 (app X (app b0 c0)) (var 2)) G) = S := by
        rw [asub_headvar _ h1 G hBF.1]; simp [sg2]; exact hVS
      have hlt : t' + 1 + m0 < T' := by
        rcases Nat.lt_or_ge (t' + 1 + m0) T' with h | h
        · exact h
        · exfalso
          have he : t' + 1 + m0 = T' := by omega
          rw [he, hT] at p2
          injection p2 with p2
          simp only [List.map_cons, List.cons_append] at p2
          injection p2 with p2 _
          rw [p2, hGS] at hf; simp at hf
      obtain ⟨L'', hL'', _⟩ := run_prefix T' (t' + 1 + m0 + 1) L1 _ hT (by omega)
      obtain ⟨Lm, hLm, hsLm⟩ := run_succ_split L1 (t' + 1 + m0) L'' hL''
      rw [p2] at hLm; injection hLm with hLm; subst hLm
      obtain ⟨R', hR'⟩ := bf_step X h1 h2 h12 hX1 hX2 (app X (app b0 c0)) (var 2) hVS G LG _ L'' hBF hsLm
      have hb := hbound _ _ (by omega) hL''
      have hL3 : L'' = args X ++ app b0 c0 :: app X (app X (app b0 c0)) :: var 2 :: R' := by
        rw [hR']; simp [args]
      rw [hL3] at hb
      have := Preg_len_ge3 (args X) (app b0 c0) (app X (app X (app b0 c0))) (var 2 :: R') hXP hwr hXVr
      omega
    · simp [chainE, head] at hg; exact h12 hg.symm

#print axioms yt_abs
#print axioms bform_nk1

/-- the residual condition BF(c0): c0's two-hole run reaches a B-form front h1.(X.h1) followed by h2, X an S-headed
    hole-free P-term -/
def BFc (c0 : T) (h1 h2 : Nat) : Prop :=
  ∃ X m0 G LG, head X = S ∧ rk X = 1 ∧ occN h1 X = 0 ∧ occN h2 X = 0 ∧
    run m0 (args c0 ++ [var h1, var h2]) = some (G :: LG) ∧ BFfront X h1 h2 G LG

/-- a code whose two-hole run has a B-form front contains p -/
theorem bf_c0_rank (c0 X : T) (h1 h2 : Nat) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) (hc1 : occN 1 c0 = 0)
    (hc2 : occN 2 c0 = 0) (hc3 : occN 3 c0 = 0) (hXr : rk X = 1) (m0 : Nat) (G : T) (LG : List T)
    (hm0 : run m0 (args c0 ++ [var h1, var h2]) = some (G :: LG)) (hBF : BFfront X h1 h2 G LG) : rk c0 = 1 := by
  have hp : occN 0 c0 ≠ 0 := by
    intro h0
    have hz := occ_run_zero 0 m0 _ _ (by
      intro e he
      simp at he
      rcases he with he | he | he
      · exact occN_args 0 c0 h0 e he
      · subst he; simp [occN]; omega
      · subst he; simp [occN]; omega) hm0 G (by simp)
    have hXG : app X (var h1) ∈ args G := by
      rcases hBF.2 with ⟨hA, _⟩ | ⟨A, hA⟩ <;> simp [hA]
    have hz2 := occN_args 0 G hz _ hXG
    simp only [occN] at hz2
    rcases rk_spec X with h | h | h <;> omega
  rcases rk_spec c0 with h | h | h <;> omega

/-- **THEOREM R3-SINGLE-3.**  r3_single2 with the residual condition widened: the next phase of a single-wrapper
    handler (b0.c0).y (b0, c0 S-headed) of an ordered single-occurrence datum never makes a proper transfer provided
    H1ok(c0), or b0 never calls its first hole, or c0's two-hole run has a B-form front h1.(X.h1) followed by h2
    (BFc).  In the last case NK1(b0) is DERIVED (bform_nk1) in pattern beta; patterns alpha and closed need no
    condition. -/
theorem r3_single3 (D b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : 4 ≤ h1) (hh2 : 4 ≤ h2)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H)
    (hDS : head D = S) (hDo : ordT D) (hD1 : occN 1 D = 0) (hD2 : occN 2 D = 0) (hD3 : occN 3 D = 0)
    (hDp : occN 0 D ≤ 1) (hDh1 : occN h1 D = 0) (hDh2 : occN h2 D = 0)
    (hb0S : head b0 = S) (hc0S : head c0 = S) (hw1 : occN 1 (app b0 c0) = 0) (hw2 : occN 2 (app b0 c0) = 0)
    (hw3 : occN 3 (app b0 c0) = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (T' : Nat) (f b : T) (R : List T)
    (hT : run T' [D, var 1, var 2, var 3] = some (f :: b :: app (app b0 c0) (var 2) :: R)) (hf : head f = var 0)
    (hcond : (∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R')) ∨
      (∀ (m : Nat) (g : T) (L : List T), run m (args b0 ++ [var h1, var h2]) = some (g :: L) → head g ≠ var h1) ∨
      BFc c0 h1 h2) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  rcases hcond with hH1 | hNK1 | hBF
  · exact r3_single2 D b0 c0 c h1 h2 H hc hc2 hh1 hh2 h12 hH hDS hDo hD1 hD2 hD3 hDp hDh1 hDh2 hb0S hc0S hw1 hw2
      hw3 hV T' f b R hT hf (Or.inl hH1)
  · exact r3_single2 D b0 c0 c h1 h2 H hc hc2 hh1 hh2 h12 hH hDS hDo hD1 hD2 hD3 hDp hDh1 hDh2 hb0S hc0S hw1 hw2
      hw3 hV T' f b R hT hf (Or.inr hNK1)
  have hh1' : h1 ≠ 0 := by omega
  have hh2' : h2 ≠ 0 := by omega
  have hw2' : occN 2 b0 = 0 ∧ occN 2 c0 = 0 := by simp only [occN] at hw2; omega
  have hy0 : occ2 b0 = 0 := by rw [occ2_eq]; exact hw2'.1
  have hy1 : occ2 c0 = 0 := by rw [occ2_eq]; exact hw2'.2
  have hz : ∀ hh, 4 ≤ hh → occN hh D = 0 → ∀ (k : Nat) (L : List T), run k [D, var 1, var 2, var 3] = some L →
      ∀ e ∈ L, occN hh e = 0 := by
    intro hh h4 hD k L hk
    apply occ_run_zero hh k _ L _ hk
    intro e he
    simp at he
    rcases he with he | he | he | he <;> subst he
    · exact hD
    · simp [occN]; omega
    · simp [occN]; omega
    · simp [occN]; omega
  have hTm : app (app b0 c0) (var 2) ∈ f :: b :: app (app b0 c0) (var 2) :: R := by simp
  have hw0 := hz h1 hh1 hDh1 T' _ hT _ hTm
  have hw0' := hz h2 hh2 hDh2 T' _ hT _ hTm
  simp only [occN] at hw0 hw0'
  have hc0f1 : occN h1 c0 = 0 := by omega
  have hc0f2 : occN h2 c0 = 0 := by omega
  have hb0f1 : occN h1 b0 = 0 := by omega
  have hb0f2 : occN h2 b0 = 0 := by omega
  -- the glue that created the handler node w.y
  obtain ⟨tg, htg, a1, R0, hg⟩ := creation (app b0 c0) (var 2) T' _ _ hT
    ⟨_, hTm, sub_refl _⟩ (by
      intro e he hs
      simp at he
      rcases he with he | he | he | he <;> subst he
      · have := occN_sub_le 2 _ _ hs; simp [occN] at this; omega
      · simp [sub] at hs
      · simp [sub] at hs
      · simp [sub] at hs)
  have ha1S : head a1 = S := head_of_continue _ tg T' a1 _ _ R0 hg htg _ hT
  have htg1 : 1 ≤ tg := by
    rcases Nat.eq_zero_or_pos tg with h0 | h0
    · subst h0; simp [run] at hg
    · exact h0
  obtain ⟨hSeg, hocc⟩ := phase2_start D hDS hDo hD1 hD2 hD3
  have hg1 : run (tg - 1) (args D ++ [var 2, app (var 1) (var 2), var 3]) = some (a1 :: app b0 c0 :: var 2 :: R0) := by
    rw [← phase2_shift D hDS (tg - 1), show tg - 1 + 1 = tg by omega]; exact hg
  have hT1 : run (T' - 1) (args D ++ [var 2, app (var 1) (var 2), var 3]) = some (f :: b :: app (app b0 c0) (var 2) :: R) := by
    rw [← phase2_shift D hDS (T' - 1), show T' - 1 + 1 = T' by omega]; exact hT
  have hSg := seg_run _ _ _ hSeg hg1
  have hrank : rk a1 ≤ rk (app b0 c0) := srt_tail_ge a1 _ hSg.1 _ (by simp)
  have hwr : rk (app b0 c0) ≤ 1 := rk_le1_of _ hw1 hw2 hw3
  have ha1f1 : occN h1 a1 = 0 := hz h1 hh1 hDh1 tg _ hg a1 (by simp)
  have ha1f2 : occN h2 a1 = 0 := hz h2 hh2 hDh2 tg _ hg a1 (by simp)
  by_cases hac : a1 = c0
  · -- pattern alpha
    subst hac
    exact alpha_main b0 a1 c h1 h2 H hc hc2 hh1' hh2' h12 hH hb0S hc0S hy0 hy1 hc0f1 hc0f2 hV _ tg T' R0 hg htg
      f b _ R hT hf
  · rcases rk_cases a1 with ha0 | ha1 | ha2
    · -- closed glue front
      have ha10 : occN 0 a1 = 0 := ((rk_eq0 a1).1 ha0).2
      have hno := closedglue_main a1 (app b0 c0) c h1 h2 H hc hh1' hh2' h12 hH ha1S ha10 (by simp [head, hb0S])
        ha1f1 ha1f2 hV _ tg T' R0 hg htg f b _ R hT hf
      have hD3' : asub (sg3 c) (app (app b0 c0) (var 2)) = app (app (sb c b0) (sb c c0)) (var 0) := by
        simp [asub, asub_sg3_sb c b0 hy0, asub_sg3_sb c c0 hy1, sg3]
      intro m f' b' d' R' hm hf'
      rw [← hD3'] at hm
      exact absurd hf' (hno m f' _ hm)
    · -- P-front different from c0: THEOREM S1, then the B-form front, BF-NK1 and PAXB
      have hw1r : rk (app b0 c0) = 1 := by omega
      obtain ⟨s, hs, B, hsB⟩ := s1_core _ (app b0 c0) b0 c0 rfl hw1r hSeg (by rw [hocc]; exact hDp)
        (T' - 1) f b _ R hT1 (by rw [rk_app, rk_var2]; omega) (tg - 1) (by omega) a1 R0 hg1 ha1 hac
      obtain ⟨X, m0, G, LG, hXS, hXr, hX1, hX2, hm0, hBFf⟩ := hBF
      have hb0r : rk b0 ≤ 1 := by have := rk_app_left b0 c0; omega
      have hc0r : rk c0 = 1 := by
        simp only [occN] at hw1 hw2 hw3
        exact bf_c0_rank c0 X h1 h2 hh1' hh2' (by omega) (by omega) (by omega) hXr m0 G LG hm0 hBFf
      have hd2 : rk (app (app b0 c0) (var 2)) = 2 := by rw [rk_app, rk_var2]; omega
      have hbound := fun s Ls hs hr => ab3_bound _ hSeg (T' - 1) f b _ R hT1 hd2 s Ls hs hr
      have hwS : head (app b0 c0) = S := by simp [head, hb0S]
      have hr0 : run s (args D ++ [var 2, app (var 1) (var 2), var 3]) = some ((args c0 ++ [var h1, var h2]).map
          (asub (sg2 h1 h2 (app b0 c0) (var 2))) ++ B) := by
        rw [img_args c0 _ _ h1 h2 h12 hc0f1 hc0f2 B]; exact hsB
      obtain ⟨_, hearly⟩ := image_stuck _ _ B _ s (T' - 1) (by omega) hr0 f b _ R hT1 hf m0 (G :: LG) hm0
      have hge : s + m0 ≤ T' - 1 := Nat.le_of_not_lt hearly
      have p2 : run (s + m0) (args D ++ [var 2, app (var 1) (var 2), var 3]) = some ((G :: LG).map
          (asub (sg2 h1 h2 (app b0 c0) (var 2))) ++ B) := by
        rw [run_add s m0, hr0, Option.bind_some]
        exact run_append m0 _ _ B (asub_run _ m0 _ _ hm0)
      have hGS : head (asub (sg2 h1 h2 (app b0 c0) (var 2)) G) = S := by
        rw [asub_headvar _ h1 G hBFf.1]; simp [sg2]; exact hb0S
      have hlt : s + m0 < T' - 1 := by
        rcases Nat.lt_or_ge (s + m0) (T' - 1) with h | h
        · exact h
        · exfalso
          have he : s + m0 = T' - 1 := by omega
          rw [he, hT1] at p2
          injection p2 with p2
          simp only [List.map_cons, List.cons_append] at p2
          injection p2 with p2 _
          rw [p2, hGS] at hf; simp at hf
      obtain ⟨L'', hL'', _⟩ := run_prefix (T' - 1) (s + m0 + 1) _ _ hT1 (by omega)
      obtain ⟨Lm, hLm, hsLm⟩ := run_succ_split _ (s + m0) L'' hL''
      rw [p2] at hLm; injection hLm with hLm; subst hLm
      obtain ⟨R', hR'⟩ := bf_step X h1 h2 h12 hX1 hX2 (app b0 c0) (var 2) hwS G LG B L'' hBFf hsLm
      have hL3 : L'' = args b0 ++ c0 :: app X (app b0 c0) :: var 2 :: R' := by
        rw [hR']; simp [args]
      have hNK1 := bform_nk1 _ (T' - 1) f b _ R hT1 hd2 hf hbound b0 c0 X h1 h2 h12 hb0r hb0f1 hc0f1 hc0f2
        hX1 hX2 hc0S hc0r hXS hXr (s + m0 + 1) (by omega) R' (by rw [← hL3]; exact hL'') m0 G LG hm0 hBFf
      exact paxb_main b0 c0 c h1 h2 hc hc2 hh1 hh2 h12 hb0S hc0S hy0 hy1 hb0f1 hb0f2 hNK1
    · omega

#print axioms bf_c0_rank
#print axioms r3_single3
