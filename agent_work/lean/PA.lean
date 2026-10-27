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
  innermost level vn[p:=c].p' is opened, then the generalised core `pa_core_g` from args(b0') ++ [c0', p'] ++ B).
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

#print axioms pa_main
#print axioms pb_main
#print axioms pam_main
#print axioms reexec_replays_transfer
