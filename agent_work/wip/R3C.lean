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
#print axioms beta_main
#print axioms pbt_main
