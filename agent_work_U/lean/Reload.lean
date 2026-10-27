/-
  agent_work_U/lean/Reload.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.

  RELOAD LEMMA for fuel-S tail calls of the leftmost Böhm path.
  A node q.S whose head normal form is S p q' continues as q'.S after a single pushed multiplier exactly when
  p = S S or H(p) = S S y (a 'fuel-S tail call').  `TC.reload_lemma`: if q = Q.z has >= 3 arguments and z /= S, such
  a step is either an R-step on the prefix (H(Q) = S S y, q' = y.z, same last argument) or produces the RELOAD SHAPE
  q' = w.(S S w).  Since R-steps strictly shrink the prefix (no_R_chain), an infinite fuel-S tail-call chain whose last
  arguments avoid S returns infinitely often to reload shape — the structure of the reload cycle
  N_i N_k S -> N_(i-1) N_k S -> ... -> B N_k S -> N_k (S S N_k) S.
  `RC.restart_detail`: if moreover z /= S S, a restart can only happen at the prefix Q = B = S(SS)(SS), and then
  q' = z.(S S z) (a single wrap; computed head normal forms are never B, and multiple wraps need z = S or S S).
  `RC.reload_classification`: an infinite chain of fuel-S tail calls whose terms never have last argument S is
  EVENTUALLY THE RELOAD CYCLE: from some index on every multiplier is N i . N m with i < m (N 0 = B,
  N (k+1) = S S (N k)).  (Ingredients: `TC.restarts`, `RC.next_restart` (between two restarts the prefix counts down
  from a counter N d to B), `RC.closure` (the reload set is closed under tail calls), `RC.reach_det` (determinism).)
  `FZ.tail_call_fuel` / `FZ.no_tail_calls_fuel`: over a closed fuel Z /= S a tail call q.Z -> q'.Z forces
  H(q) = S (S S) q' (an R2-step), so there is NO infinite tail-call walk over a fuel other than S (Conjecture F,
  tail-call case).
  `FZ.tail_call_S` + `FZ.walk_reload`: walk-level form — an infinite leftmost walk through nodes q_j.S whose every
  child is the next node q_(j+1).S (q_j with >= 2 arguments, last argument /= S) is eventually the reload cycle.
  `RC2.reload_classification_full` / `walk_reload_full`: the same WITHOUT any hypothesis on last arguments (tail calls
  through last argument S or S S die or reach the invariant 'last argument = S S W', after which the restricted
  classification applies).  So: every infinite leftmost walk that eventually consists of tail calls over a fixed
  bottom has bottom S and is eventually the reload cycle N_i N_m S (with FZ.no_tail_calls_fuel for bottoms /= S).
  Namespace C = lean/Strip.lean verbatim.
-/

namespace C


inductive T where
  | S : T
  | app : T → T → T
deriving DecidableEq, Repr

open T

def args : T → List T
  | S => []
  | app f x => args f ++ [x]

def size : T → Nat
  | S => 1
  | app f x => size f + size x

def lchild : T → T
  | S => S
  | app f _ => f

def step : List T → Option (List T)
  | a :: b :: c :: R => some (args a ++ c :: app b c :: R)
  | _ => none

inductive Reach (L0 : List T) : List T → Prop
  | refl : Reach L0 L0
  | tail {L L' : List T} : Reach L0 L → step L = some L' → Reach L0 L'

theorem size_pos : ∀ t : T, 0 < size t
  | S => by simp [size]
  | app f x => by have := size_pos f; simp [size]; omega

theorem args_nil (t : T) (h : args t = []) : t = S := by
  cases t with
  | S => rfl
  | app f x => simp [args] at h

theorem size_args : ∀ (t y : T), y ∈ args t → size y < size t
  | S, y, h => by simp [args] at h
  | app f x, y, h => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · have := size_args f y h; simp [size]; omega
    · have := size_pos f; simp [size]; omega

theorem step_len (L L' : List T) (h : step L = some L') : 2 ≤ L'.length := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step, Option.some.injEq] at h; subst h; simp; omega

theorem step_exists (L : List T) (h : 3 ≤ L.length) : ∃ L', step L = some L' := by
  match L, h with
  | a :: b :: c :: R, _ => exact ⟨_, rfl⟩

theorem step_append (L L' M : List T) (h3 : 3 ≤ L.length) (h : step L = some L') :
    step (L ++ M) = some (L' ++ M) := by
  match L, h3, h with
  | a :: b :: c :: R, _, h =>
    simp only [step, Option.some.injEq] at h; subst h
    simp [step]

theorem step_short (A : List T) (hA : A.length ≤ 2) : step A = none := by
  match A, hA with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _, hA => simp at hA

theorem reach_stuck (A B : List T) (hA : A.length ≤ 2) (h : Reach A B) : B = A := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    rw [ih, step_short A hA] at hs
    exact absurd hs (by simp)

/-! ## the bottom-size invariant -/

/-- the last element is strictly larger than z -/
def BigBot (z : T) (L : List T) : Prop := ∃ M w, L = M ++ [w] ∧ size z < size w

theorem bigbot_step (z : T) (L L' : List T) (hB : BigBot z L) (hs : step L = some L') : BigBot z L' := by
  obtain ⟨M, w, rfl, hw⟩ := hB
  match M, hs with
  | [], hs => simp [step] at hs
  | [_], hs => simp [step] at hs
  | [a, b], hs =>
    simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
    subst hs
    refine ⟨args a ++ [w], app b w, by simp, ?_⟩
    simp [size]; omega
  | a :: b :: c :: M', hs =>
    simp only [List.cons_append, step, Option.some.injEq] at hs
    subst hs
    exact ⟨args a ++ c :: app b c :: M', w, by simp, hw⟩

theorem bigbot_reach (z : T) (A B : List T) (hA : BigBot z A) (h : Reach A B) : BigBot z B := by
  induction h with
  | refl => exact hA
  | tail _ hs ih => exact bigbot_step z _ _ ih hs

/-- a 2-list reached by at least one step from a BigBot list has a first element larger than z -/
theorem bigbot_final (z : T) (A : List T) (c d : T) (hA : BigBot z A) (h : Reach A [c, d])
    (hne : A ≠ [c, d]) : size z < size c := by
  cases h with
  | refl => exact absurd rfl hne
  | tail h1 hs =>
    rename_i L1
    have hB := bigbot_reach z A L1 hA h1
    obtain ⟨M, w, hL1, hw⟩ := hB
    match L1, hs, hL1 with
    | a :: b :: c' :: R, hs, hL1 =>
      simp only [step, Option.some.injEq] at hs
      have hlen := congrArg List.length hs
      simp at hlen
      have ha : args a = [] := by
        cases h' : args a with
        | nil => rfl
        | cons _ _ => rw [h'] at hlen; simp at hlen; omega
      have hR : R = [] := by
        cases R with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hR
      rw [ha] at hs
      simp only [List.nil_append, List.cons.injEq] at hs
      have hw' : w = c' := by
        have := congrArg List.getLast? hL1
        simp at this; exact this.symm
      rw [← hs.1, ← hw']; exact hw

/-! ## the stripping invariant -/

def SInv (L : List T) (z : T) (L2 : List T) : Prop :=
  (∃ L1, Reach L L1 ∧ 2 ≤ L1.length ∧ L2 = L1 ++ [z]) ∨
  (∃ y, Reach L [S, y] ∧ L2 = [z, app y z]) ∨
  (∃ x y, x ≠ S ∧ Reach L [x, y] ∧ Reach (args x ++ [z, app y z]) L2)

theorem inv_step (L : List T) (z : T) (L2 L3 : List T) (hI : SInv L z L2) (hs : step L2 = some L3) :
    SInv L z L3 := by
  rcases hI with ⟨L1, hr, hlen, rfl⟩ | ⟨y, _, rfl⟩ | ⟨x, y, hx, hr, hr2⟩
  · by_cases h3 : 3 ≤ L1.length
    · obtain ⟨L1', h1'⟩ := step_exists L1 h3
      have := step_append L1 L1' [z] h3 h1'
      rw [this] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inl ⟨L1', Reach.tail hr h1', step_len _ _ h1', rfl⟩
    · have h2 : L1.length = 2 := by omega
      match L1, h2, hr, hs with
      | [x, y], _, hr, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hx : x = S
        · subst hx
          exact Or.inr (Or.inl ⟨y, hr, by simp [args]⟩)
        · exact Or.inr (Or.inr ⟨x, y, hx, hr, Reach.refl⟩)
  · simp [step] at hs
  · exact Or.inr (Or.inr ⟨x, y, hx, hr, Reach.tail hr2 hs⟩)

theorem inv_reach (L : List T) (z : T) (hL : 2 ≤ L.length) (L2 : List T) (h : Reach (L ++ [z]) L2) :
    SInv L z L2 := by
  induction h with
  | refl => exact Or.inl ⟨L, Reach.refl, hL, rfl⟩
  | tail _ hs ih => exact inv_step L z _ _ ih hs

/-- **Final shape.**  A head normal form [c, d] of L ++ [z] (L with >= 2 elements) either keeps the bottom z as its
    first component — and then L itself reaches [S, y] and d = y.z — or has a first component larger than z. -/
theorem final_shape (L : List T) (z c d : T) (hL : 2 ≤ L.length) (h : Reach (L ++ [z]) [c, d]) :
    (c = z ∧ ∃ y, Reach L [S, y] ∧ d = app y z) ∨ size z < size c := by
  rcases inv_reach L z hL _ h with ⟨L1, _, hlen, hEq⟩ | ⟨y, hr, hEq⟩ | ⟨x, y, hx, _, hr2⟩
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq] at hEq
    exact Or.inl ⟨hEq.1, y, hr, hEq.2.1⟩
  · right
    refine bigbot_final z _ c d ⟨args x ++ [z], app y z, by simp, ?_⟩ hr2 ?_
    · simp [size]; have := size_pos y; omega
    · intro hEq
      have := congrArg List.length hEq
      simp at this
      have : args x = [] := by
        cases h' : args x with
        | nil => rfl
        | cons _ _ => rw [h'] at this; simp at this
      exact hx (args_nil x this)

/-! ## chains -/

/-- H(P) = S S P' -/
def R (P P' : T) : Prop := Reach (args P) [S, P']

/-- H(W) = S (S S) W' -/
def R2 (W W' : T) : Prop := Reach (args W) [app S S, W']

theorem args_app (f x : T) : args (app f x) = args f ++ [x] := rfl

theorem R_short (P P' : T) (h : (args P).length ≤ 2) (hR : R P P') : args P = [S, P'] :=
  (reach_stuck _ _ h hR).symm

theorem R_S (P' : T) : ¬ R S P' := by
  intro h
  have := R_short S P' (by simp [args]) h
  simp [args] at this

/-- if P = Q.z with Q having >= 2 arguments and H(P) = S S P', then z = S and H(Q) = S S y with P' = y.S -/
theorem R_strip (Q z P' : T) (hQ : 2 ≤ (args Q).length) (h : R (app Q z) P') :
    z = S ∧ ∃ y, R Q y ∧ P' = app y S := by
  unfold R at h
  rw [args_app] at h
  rcases final_shape (args Q) z S P' hQ h with ⟨hz, y, hy, hP⟩ | hbig
  · subst hz; exact ⟨rfl, y, hy, hP⟩
  · have := size_pos z; simp [size] at hbig; omega

theorem R2_strip (Q P' : T) (hQ : 2 ≤ (args Q).length) (h : R2 (app Q (app S S)) P') :
    ∃ y, R Q y ∧ P' = app y (app S S) := by
  unfold R2 at h
  rw [args_app] at h
  rcases final_shape (args Q) (app S S) (app S S) P' hQ h with ⟨_, y, hy, hP⟩ | hbig
  · exact ⟨y, hy, hP⟩
  · simp [size] at hbig

/-- a term y.S where y has at most one argument cannot start an R-chain of length 2 -/
theorem R_dies (y P1 P2 : T) (hy : (args y).length ≤ 1) (h1 : R (app y S) P1) (h2 : R P1 P2) : False := by
  have hlen : (args (app y S)).length ≤ 2 := by rw [args_app]; simp; omega
  have e := R_short _ _ hlen h1
  rw [args_app] at e
  match hy' : args y, e with
  | [w], e =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    rw [← e.2.1] at h2
    exact R_S P2 h2
  | [], e => simp at e
  | _ :: _ :: _, _ => rw [hy'] at hy; simp at hy

theorem no_R_chain_aux : ∀ (n : Nat) (f : Nat → T), size (f 0) ≤ n → (∀ j, R (f j) (f (j + 1))) → False := by
  intro n
  induction n with
  | zero => intro f h _; have := size_pos (f 0); omega
  | succ n ih =>
    intro f hsize hR
    by_cases hshort : (args (f 0)).length ≤ 2
    · have e := R_short _ _ hshort (hR 0)
      have hmem : f 1 ∈ args (f 0) := by rw [e]; simp
      have := size_args _ _ hmem
      exact ih (fun j => f (j + 1)) (by simp; omega) (fun j => hR (j + 1))
    · match hf0 : f 0 with
      | S => rw [hf0] at hshort; simp [args] at hshort
      | app Q z =>
        have hQ : 2 ≤ (args Q).length := by
          rw [hf0, args_app] at hshort; simp at hshort; omega
        have key : ∀ j, f j = app (lchild (f j)) S ∧ 2 ≤ (args (lchild (f j))).length := by
          intro j
          induction j with
          | zero =>
            have h0 := hR 0
            rw [hf0] at h0
            obtain ⟨hz, _⟩ := R_strip Q z (f 1) hQ h0
            subst hz
            rw [hf0]; exact ⟨rfl, hQ⟩
          | succ j ihj =>
            obtain ⟨hfj, hlen⟩ := ihj
            have hj := hR j
            rw [hfj] at hj
            obtain ⟨_, y, _, hP⟩ := R_strip _ S _ hlen hj
            have hy : 2 ≤ (args y).length := by
              by_cases hy1 : (args y).length ≤ 1
              · exfalso
                have h1 := hR (j + 1)
                rw [hP] at h1
                exact R_dies y _ _ hy1 h1 (hR (j + 2))
              · omega
            rw [hP]; exact ⟨rfl, hy⟩
        have chain : ∀ j, R (lchild (f j)) (lchild (f (j + 1))) := by
          intro j
          obtain ⟨hfj, hlen⟩ := key j
          have hj := hR j
          rw [hfj] at hj
          obtain ⟨_, y, hy, hP⟩ := R_strip _ S _ hlen hj
          rw [hP]; exact hy
        have hsz : size (lchild (f 0)) ≤ n := by
          rw [hf0] at hsize ⊢; simp [lchild, size] at hsize ⊢; have := size_pos z; omega
        exact ih (fun j => lchild (f j)) hsz chain

/-- **No infinite R-chain:** there is no sequence P0, P1, ... of closed S-terms with H(P_j) = S S P_(j+1). -/
theorem no_R_chain (f : Nat → T) (hR : ∀ j, R (f j) (f (j + 1))) : False :=
  no_R_chain_aux (size (f 0)) f (Nat.le_refl _) hR


/-! ## R2-chains (the opaque-fuel step) -/

/-- a 2-list reached from a list of length >= 3 has the shape [c, b.c] -/
theorem final_app (A : List T) (c d : T) (hA : 3 ≤ A.length) (h : Reach A [c, d]) : ∃ b, d = app b c := by
  cases h with
  | refl => simp at hA
  | tail h1 hs =>
    rename_i L1
    match L1, hs with
    | a :: b :: c' :: R, hs =>
      simp only [step, Option.some.injEq] at hs
      have hlen := congrArg List.length hs
      simp at hlen
      have ha : args a = [] := by
        cases h' : args a with
        | nil => rfl
        | cons _ _ => rw [h'] at hlen; simp at hlen; omega
      have hR : R = [] := by
        cases R with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hR
      rw [ha] at hs
      simp only [List.nil_append, List.cons.injEq] at hs
      exact ⟨b, by rw [← hs.2.1, hs.1]⟩

theorem R2_short (W W' : T) (h : (args W).length ≤ 2) (hR : R2 W W') : args W = [app S S, W'] :=
  (reach_stuck _ _ h hR).symm

theorem R2_SS (W' : T) : ¬ R2 (app S S) W' := by
  intro h
  have := R2_short (app S S) W' (by simp [args]) h
  simp [args] at this

theorem R2_dies (y W1 W2 : T) (hy : (args y).length ≤ 1) (h1 : R2 (app y (app S S)) W1)
    (h2 : R2 W1 W2) : False := by
  have hlen : (args (app y (app S S))).length ≤ 2 := by rw [args_app]; simp; omega
  have e := R2_short _ _ hlen h1
  rw [args_app] at e
  match hy' : args y, e with
  | [w], e =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    rw [← e.2.1] at h2
    exact R2_SS W2 h2
  | [], e => simp at e
  | _ :: _ :: _, _ => rw [hy'] at hy; simp at hy

theorem no_R2_chain_aux : ∀ (n : Nat) (f : Nat → T), size (f 0) ≤ n → (∀ j, R2 (f j) (f (j + 1))) → False := by
  intro n
  induction n with
  | zero => intro f h _; have := size_pos (f 0); omega
  | succ n ih =>
    intro f hsize hR
    by_cases hshort : (args (f 0)).length ≤ 2
    · have e := R2_short _ _ hshort (hR 0)
      have hmem : f 1 ∈ args (f 0) := by rw [e]; simp
      have := size_args _ _ hmem
      exact ih (fun j => f (j + 1)) (by simp; omega) (fun j => hR (j + 1))
    · obtain ⟨b, hb⟩ := final_app _ _ _ (by omega) (hR 0)
      -- from f 1 on, every term is y.(S S) with y having >= 2 arguments
      have key : ∀ j, f (j + 1) = app (lchild (f (j + 1))) (app S S) ∧
          2 ≤ (args (lchild (f (j + 1)))).length := by
        intro j
        induction j with
        | zero =>
          have hb2 : 2 ≤ (args b).length := by
            by_cases hb1 : (args b).length ≤ 1
            · exfalso
              have h1 := hR 1
              rw [hb] at h1
              exact R2_dies b _ _ hb1 h1 (hR 2)
            · omega
          rw [hb]; exact ⟨rfl, hb2⟩
        | succ j ihj =>
          obtain ⟨hfj, hlen⟩ := ihj
          have hj := hR (j + 1)
          rw [hfj] at hj
          obtain ⟨y, _, hP⟩ := R2_strip _ _ hlen hj
          have hy : 2 ≤ (args y).length := by
            by_cases hy1 : (args y).length ≤ 1
            · exfalso
              have h1 := hR (j + 2)
              rw [hP] at h1
              exact R2_dies y _ _ hy1 h1 (hR (j + 3))
            · omega
          rw [hP]; exact ⟨rfl, hy⟩
      have chain : ∀ j, R (lchild (f (j + 1))) (lchild (f (j + 1 + 1))) := by
        intro j
        obtain ⟨hfj, hlen⟩ := key j
        have hj := hR (j + 1)
        rw [hfj] at hj
        obtain ⟨y, hy, hP⟩ := R2_strip _ _ hlen hj
        rw [hP]; exact hy
      exact no_R_chain (fun j => lchild (f (j + 1))) chain

/-- **No infinite R2-chain:** there is no sequence W0, W1, ... of closed S-terms with H(W_j) = S (S S) W_(j+1). -/
theorem no_R2_chain (f : Nat → T) (hR : ∀ j, R2 (f j) (f (j + 1))) : False :=
  no_R2_chain_aux (size (f 0)) f (Nat.le_refl _) hR

end C

/-! ## Fuel-S tail calls and the reload shape (namespace TC, closed terms of namespace C) -/

namespace TC

open C
open C.T

theorem args_one' (q p : T) (h : args q = [p]) : q = app S p := by
  cases q with
  | S => simp [args] at h
  | app f x =>
    simp only [args] at h
    have hl := congrArg List.length h
    simp at hl
    have hf : args f = [] := by
      cases h' : args f with
      | nil => rfl
      | cons _ _ => rw [h'] at hl; simp at hl
    rw [hf] at h
    simp at h
    rw [args_nil f hf, h]

/-- runs from args Q ++ [z]: before any wrap (A), after the last wrap [x, c, w] -> args x ++ [w, c.w] (B), finished
    after a wrap (C), finished without a wrap (D) -/
def TCInv (Q z : T) (L : List T) : Prop :=
  (∃ L1, Reach (args Q) L1 ∧ 2 ≤ L1.length ∧ L = L1 ++ [z]) ∨
  (∃ x c w P, w ≠ S ∧ x ≠ S ∧ Reach (args x ++ [w]) P ∧ 2 ≤ P.length ∧ L = P ++ [app c w]) ∨
  (∃ x c w b, w ≠ S ∧ x ≠ S ∧ Reach (args x ++ [w]) [S, b] ∧ L = [app c w, app b (app c w)]) ∨
  (∃ y, Reach (args Q) [S, y] ∧ L = [z, app y z])

theorem args_ne_nil (x : T) (hx : x ≠ S) : 1 ≤ (args x).length := by
  cases h : args x with
  | nil => exact absurd (args_nil x h) hx
  | cons _ _ => simp

theorem tc_step (Q z : T) (hz : z ≠ S) (L L' : List T) (hI : TCInv Q z L) (hs : step L = some L') :
    TCInv Q z L' := by
  rcases hI with ⟨L1, hr, hlen, rfl⟩ | ⟨x, c, w, P, hw, hx, hP, hlen, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ |
      ⟨_, _, rfl⟩
  · by_cases h3 : 3 ≤ L1.length
    · obtain ⟨L1', h1'⟩ := step_exists L1 h3
      rw [step_append L1 L1' [z] h3 h1'] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inl ⟨L1', Reach.tail hr h1', step_len _ _ h1', rfl⟩
    · have h2 : L1.length = 2 := by omega
      match L1, h2, hr, hs with
      | [x, c], _, hr, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hxS : x = S
        · subst hxS
          exact Or.inr (Or.inr (Or.inr ⟨c, hr, by simp [args]⟩))
        · refine Or.inr (Or.inl ⟨x, c, z, args x ++ [z], hz, hxS, Reach.refl, ?_, by simp⟩)
          have := args_ne_nil x hxS; simp; omega
  · by_cases h3 : 3 ≤ P.length
    · obtain ⟨P', h1'⟩ := step_exists P h3
      rw [step_append P P' [app c w] h3 h1'] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inr (Or.inl ⟨x, c, w, P', hw, hx, Reach.tail hP h1', step_len _ _ h1', rfl⟩)
    · have h2 : P.length = 2 := by omega
      match P, h2, hP, hs with
      | [x', c'], _, hP, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hxS : x' = S
        · subst hxS
          exact Or.inr (Or.inr (Or.inl ⟨x, c, w, c', hw, hx, hP, by simp [args]⟩))
        · refine Or.inr (Or.inl ⟨x', c', app c w, args x' ++ [app c w], by simp, hxS, Reach.refl, ?_, by simp⟩)
          have := args_ne_nil x' hxS; simp; omega
  · simp [step] at hs
  · simp [step] at hs

theorem tc_reach (Q z : T) (hQ : 2 ≤ (args Q).length) (hz : z ≠ S) (L : List T)
    (h : Reach (args Q ++ [z]) L) : TCInv Q z L := by
  induction h with
  | refl => exact Or.inl ⟨args Q, Reach.refl, hQ, rfl⟩
  | tail _ hs ih => exact tc_step Q z hz _ _ ih hs

/-- **Reload lemma.**  Let q = Q.z have >= 3 arguments, with last argument z /= S, and let the head normal form of q be
    S p q' where p is a fuel-S tail-call head (p = S S, or H(p) = S S y).  Then either the step is an R-step on the
    prefix (H(Q) = S S y and q' = y.z, same last argument) or q' has the RELOAD SHAPE  w.(S S w). -/
theorem reload_lemma (Q z p q' : T) (hQ : 2 ≤ (args Q).length) (hz : z ≠ S)
    (h : Reach (args (app Q z)) [p, q']) (hfuel : p = app S S ∨ ∃ y, R p y) :
    (∃ y, R Q y ∧ q' = app y z) ∨ (∃ w, q' = app w (app (app S S) w)) := by
  rw [args_app] at h
  rcases tc_reach Q z hQ hz _ h with ⟨L1, _, hlen, hEq⟩ | ⟨x, c, w, P, _, _, _, hlen, hEq⟩ |
      ⟨x, c, w, b, hw, hx, hP, hEq⟩ | ⟨y, hy, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · right
    simp only [List.cons.injEq] at hEq
    obtain ⟨hp, hq, _⟩ := hEq
    -- b = w: the prefix args x ++ [w] reached [S, b]
    have hbw : b = w := by
      by_cases hx2 : 2 ≤ (args x).length
      · rcases final_shape (args x) w S b hx2 hP with ⟨hwS, _⟩ | hbig
        · exact absurd hwS.symm hw
        · simp [size] at hbig; have := size_pos w; omega
      · have hl : (args x ++ [w]).length ≤ 2 := by simp; omega
        have e := reach_stuck _ _ hl hP
        match hax : args x, e with
        | [x0], e =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
          exact e.2.1
        | [], e => simp at e
        | _ :: _ :: _, _ => rw [hax] at hx2; simp at hx2
    -- c = S S by the fuel condition on p = c.w
    have hc : c = app S S := by
      rcases hfuel with hSS | ⟨y, hy⟩
      · rw [hp] at hSS
        simp only [app.injEq] at hSS
        exact absurd hSS.2 hw
      · rw [hp] at hy
        by_cases hc2 : 2 ≤ (args c).length
        · exact absurd (R_strip c w y hc2 hy).1 hw
        · have hl : (args (app c w)).length ≤ 2 := by rw [args_app]; simp; omega
          have e := R_short _ _ hl hy
          rw [args_app] at e
          match hac : args c, e with
          | [c0], e =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
            rw [args_one' c c0 hac, e.1]
          | [], e => simp at e
          | _ :: _ :: _, _ => rw [hac] at hc2; simp at hc2
    exact ⟨w, by rw [hq, hbw, hc]⟩
  · left
    simp only [List.cons.injEq] at hEq
    exact ⟨y, hy, hEq.2.1⟩

end TC

#print axioms TC.reload_lemma

namespace TC
open C
open C.T

/-- R-steps strictly shrink: H(Q) = S S y implies |y| < |Q| -/
theorem R_shrinks : ∀ (n : Nat) (Q y : T), size Q ≤ n → R Q y → size y < size Q := by
  intro n
  induction n with
  | zero => intro Q y h _; have := size_pos Q; omega
  | succ n ih =>
    intro Q y hs hR
    by_cases h2 : (args Q).length ≤ 2
    · have e := R_short Q y h2 hR
      have hmem : y ∈ args Q := by rw [e]; simp
      exact size_args Q y hmem
    · match Q, h2, hR, hs with
      | S, h2, _, _ => simp [args] at h2
      | app Q' z, h2, hR, hs =>
        have hQ' : 2 ≤ (args Q').length := by rw [args_app] at h2; simp at h2; omega
        obtain ⟨hz, y', hy', hyy⟩ := R_strip Q' z y hQ' hR
        subst hz; subst hyy
        have := ih Q' y' (by simp [size] at hs; omega) hy'
        simp [size]; omega

/-- a fuel-S tail call q.S -> q'.S: the head normal form of q is S p q' with p = S S or H(p) = S S y -/
def TCStep (q q' : T) : Prop := ∃ p, Reach (args q) [p, q'] ∧ (p = app S S ∨ ∃ y, R p y)

/-- the last spine argument -/
def lastArg : T → T
  | S => S
  | app _ z => z

/-- **Restart theorem.**  In an infinite chain of fuel-S tail calls whose terms never have last argument S, the
    reload shape w.(S S w) recurs infinitely often. -/
theorem restarts (f : Nat → T) (hstep : ∀ j, TCStep (f j) (f (j + 1))) (hlast : ∀ j, lastArg (f j) ≠ S) :
    ∀ N, ∃ j, N ≤ j ∧ ∃ w, f j = app w (app (app S S) w) := by
  intro N
  refine Classical.byContradiction (fun hno => ?_)
  have hno' : ∀ j, N ≤ j → ∀ w, f j ≠ app w (app (app S S) w) := by
    intro j hj w hw
    exact hno ⟨j, hj, w, hw⟩
  -- sizes strictly decrease from N on
  have hdec : ∀ j, N ≤ j → size (f (j + 1)) < size (f j) := by
    intro j hj
    obtain ⟨p, hr, hfuel⟩ := hstep j
    by_cases h2 : (args (f j)).length ≤ 2
    · have e := (reach_stuck _ _ h2 hr).symm
      have hmem : f (j + 1) ∈ args (f j) := by rw [e]; simp
      exact size_args _ _ hmem
    · match hfj : f j, h2, hr with
      | S, h2, _ => simp [args] at h2
      | app Q z, h2, hr =>
        have hQ : 2 ≤ (args Q).length := by rw [args_app] at h2; simp at h2; omega
        have hz : z ≠ S := by have := hlast j; rw [hfj] at this; exact this
        rcases reload_lemma Q z p (f (j + 1)) hQ hz hr hfuel with ⟨y, hy, hq⟩ | ⟨w, hw⟩
        · rw [hq]
          have := R_shrinks (size Q) Q y (Nat.le_refl _) hy
          simp [size]; omega
        · exact absurd hw (hno' (j + 1) (by omega) w)
  -- an infinite strictly decreasing sequence of naturals
  have hbound : ∀ k, size (f (N + k)) + k ≤ size (f N) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hdec (N + k) (by omega)
      rw [show N + (k + 1) = N + k + 1 by omega]
      omega
  have := hbound (size (f N) + 1)
  omega

end TC

#print axioms TC.R_shrinks
#print axioms TC.restarts

/-! ## Classification: infinite fuel-S tail-call chains are the reload cycle -/

namespace RC

open C
open C.T
open TC

def SS : T := app S S
/-- B = S(SS)(SS) -/
def B : T := app (app S SS) SS
/-- N 0 = B, N (k+1) = S S (N k) -/
def N : Nat → T
  | 0 => B
  | k + 1 => app SS (N k)

/-- bottoms after wraps: z, c.z, c'.(c.z), ... -/
inductive Wrapped (z : T) : T → Prop
  | base : Wrapped z z
  | wrap (c w : T) : Wrapped z w → Wrapped z (app c w)

theorem wrapped_ne_S (z w : T) (hz : z ≠ S) (h : Wrapped z w) : w ≠ S := by
  cases h with
  | base => exact hz
  | wrap c w' _ => intro h; cases h

/-- a 2-list [S S, S S] is never the result of a step, so it is reached only in zero steps -/
theorem reach_SSSS (A : List T) (h : Reach A [SS, SS]) : A = [SS, SS] := by
  cases h with
  | refl => rfl
  | tail h1 hs =>
    rename_i L1
    match L1, hs with
    | a :: b :: c :: R, hs =>
      simp only [step, Option.some.injEq] at hs
      have hlen := congrArg List.length hs
      simp at hlen
      have ha : args a = [] := by
        cases h' : args a with
        | nil => rfl
        | cons _ _ => rw [h'] at hlen; simp at hlen; omega
      have hR : R = [] := by
        cases R with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hR
      rw [ha] at hs
      simp only [List.nil_append, List.cons.injEq, SS] at hs
      obtain ⟨h1, h2, _⟩ := hs
      rw [h1] at h2
      simp at h2

theorem args_two (q a b : T) (h : args q = [a, b]) : q = app (app S a) b := by
  cases q with
  | S => simp [args] at h
  | app f x =>
    simp only [args] at h
    have hl := congrArg List.length h
    simp at hl
    match hf : args f, h with
    | [a'], h =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      rw [args_one' f a' hf, h.1, h.2.1]
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h

/-- history of the last wrap [x, c, w] -/
def Hist (Q z x c w : T) : Prop :=
  (w = z ∧ Reach (args Q) [x, c]) ∨
  (∃ x0 c0 w0, w = app c0 w0 ∧ Wrapped z w0 ∧ Reach (args x0 ++ [w0]) [x, c])

theorem hist_wrapped (Q z x c w : T) (h : Hist Q z x c w) : Wrapped z w := by
  rcases h with ⟨rfl, _⟩ | ⟨x0, c0, w0, rfl, hw0, _⟩
  · exact Wrapped.base
  · exact Wrapped.wrap c0 w0 hw0

def CInv (Q z : T) (L : List T) : Prop :=
  (∃ L1, Reach (args Q) L1 ∧ 2 ≤ L1.length ∧ L = L1 ++ [z]) ∨
  (∃ x c w P, x ≠ S ∧ Hist Q z x c w ∧ Reach (args x ++ [w]) P ∧ 2 ≤ P.length ∧ L = P ++ [app c w]) ∨
  (∃ x c w b, x ≠ S ∧ Hist Q z x c w ∧ Reach (args x ++ [w]) [S, b] ∧ L = [app c w, app b (app c w)]) ∨
  (∃ y, Reach (args Q) [S, y] ∧ L = [z, app y z])

theorem cinv_step (Q z : T) (L L' : List T) (hI : CInv Q z L) (hs : step L = some L') : CInv Q z L' := by
  rcases hI with ⟨L1, hr, hlen, rfl⟩ | ⟨x, c, w, P, hx, hH, hP, hlen, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ |
      ⟨_, _, rfl⟩
  · by_cases h3 : 3 ≤ L1.length
    · obtain ⟨L1', h1'⟩ := step_exists L1 h3
      rw [step_append L1 L1' [z] h3 h1'] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inl ⟨L1', Reach.tail hr h1', step_len _ _ h1', rfl⟩
    · have h2 : L1.length = 2 := by omega
      match L1, h2, hr, hs with
      | [x, c], _, hr, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hxS : x = S
        · subst hxS
          exact Or.inr (Or.inr (Or.inr ⟨c, hr, by simp [args]⟩))
        · refine Or.inr (Or.inl ⟨x, c, z, args x ++ [z], hxS, Or.inl ⟨rfl, hr⟩, Reach.refl, ?_, by simp⟩)
          have := args_ne_nil x hxS; simp; omega
  · by_cases h3 : 3 ≤ P.length
    · obtain ⟨P', h1'⟩ := step_exists P h3
      rw [step_append P P' [app c w] h3 h1'] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inr (Or.inl ⟨x, c, w, P', hx, hH, Reach.tail hP h1', step_len _ _ h1', rfl⟩)
    · have h2 : P.length = 2 := by omega
      match P, h2, hP, hs with
      | [x', c'], _, hP, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hxS : x' = S
        · subst hxS
          exact Or.inr (Or.inr (Or.inl ⟨x, c, w, c', hx, hH, hP, by simp [args]⟩))
        · refine Or.inr (Or.inl ⟨x', c', app c w, args x' ++ [app c w], hxS,
            Or.inr ⟨x, c, w, rfl, hist_wrapped Q z x c w hH, hP⟩, Reach.refl, ?_, by simp⟩)
          have := args_ne_nil x' hxS; simp; omega
  · simp [step] at hs
  · simp [step] at hs

theorem cinv_reach (Q z : T) (hQ : 2 ≤ (args Q).length) (L : List T)
    (h : Reach (args Q ++ [z]) L) : CInv Q z L := by
  induction h with
  | refl => exact Or.inl ⟨args Q, Reach.refl, hQ, rfl⟩
  | tail _ hs ih => exact cinv_step Q z _ _ ih hs

/-- **Restart detail.**  If q = Q.z (>= 3 arguments) with z /= S, z /= S S makes a fuel-S tail call, then it is an
    R-step on the prefix, or Q = B and the next multiplier is z.(S S z). -/
theorem restart_detail (Q z p q' : T) (hQ : 2 ≤ (args Q).length) (hz : z ≠ S) (hzSS : z ≠ SS)
    (h : Reach (args (app Q z)) [p, q']) (hfuel : p = SS ∨ ∃ y, R p y) :
    (∃ y, R Q y ∧ q' = app y z) ∨ (Q = B ∧ q' = app z (app SS z)) := by
  rw [args_app] at h
  rcases cinv_reach Q z hQ _ h with ⟨L1, _, hlen, hEq⟩ | ⟨x, c, w, P, _, _, _, hlen, hEq⟩ |
      ⟨x, c, w, b, hx, hH, hP, hEq⟩ | ⟨y, hy, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · right
    simp only [List.cons.injEq] at hEq
    obtain ⟨hp, hq, _⟩ := hEq
    have hw : w ≠ S := wrapped_ne_S z w hz (hist_wrapped Q z x c w hH)
    -- the prefix args x ++ [w] reached [S, b]: |args x| = 1, x = S S, b = w
    have hx1 : (args x).length = 1 := by
      by_cases hx2 : 2 ≤ (args x).length
      · rcases final_shape (args x) w S b hx2 hP with ⟨hwS, _⟩ | hbig
        · exact absurd hwS.symm hw
        · simp [size] at hbig; have := size_pos w; omega
      · have := args_ne_nil x hx; omega
    have hl : (args x ++ [w]).length ≤ 2 := by simp; omega
    have e := reach_stuck _ _ hl hP
    obtain ⟨hxSS, hbw⟩ : x = SS ∧ b = w := by
      match hax : args x, e with
      | [x0], e =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
        refine ⟨?_, e.2.1⟩
        rw [args_one' x x0 hax, ← e.1]; rfl
      | [], e => simp at e
      | _ :: _ :: _, _ => rw [hax] at hx1; simp at hx1
    -- c = S S by the fuel condition
    have hc : c = SS := by
      rcases hfuel with hSS | ⟨y, hy⟩
      · rw [hp] at hSS
        simp only [SS, app.injEq] at hSS
        exact absurd hSS.2 hw
      · rw [hp] at hy
        by_cases hc2 : 2 ≤ (args c).length
        · exact absurd (R_strip c w y hc2 hy).1 hw
        · have hl2 : (args (app c w)).length ≤ 2 := by rw [args_app]; simp; omega
          have e2 := R_short _ _ hl2 hy
          rw [args_app] at e2
          match hac : args c, e2 with
          | [c0], e2 =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at e2
            rw [args_one' c c0 hac, e2.1]; rfl
          | [], e2 => simp at e2
          | _ :: _ :: _, _ => rw [hac] at hc2; simp at hc2
    subst hxSS; subst hc
    -- the last wrap was [S S, S S, w]: it is the first wrap (Q = B, w = z)
    rcases hH with ⟨hwz, hrQ⟩ | ⟨x0, c0, w0, hw0eq, hw0, hr0⟩
    · have := reach_SSSS _ hrQ
      refine ⟨args_two Q SS SS this, ?_⟩
      rw [hq, hbw, hwz]
    · exfalso
      have e0 := reach_SSSS _ hr0
      have hw0SS : w0 = SS := by
        have := congrArg List.getLast? e0; simp at this; exact this
      cases hw0 with
      | base => exact hzSS hw0SS
      | wrap c1 w1 hw1 =>
        simp only [SS, app.injEq] at hw0SS
        exact wrapped_ne_S z w1 hz hw1 hw0SS.2
  · left
    simp only [List.cons.injEq] at hEq
    exact ⟨y, hy, hEq.2.1⟩

/-- R-steps into a term whose last argument is not S are syntactic -/
theorem R_into (y v : T) (hv : lastArg v ≠ S) (h : R y v) : y = app SS v := by
  by_cases h2 : (args y).length ≤ 2
  · have e := R_short y v h2 h
    have := args_two y S v e
    rw [this]; rfl
  · match y, h2, h with
    | S, h2, _ => simp [args] at h2
    | app Q z, h2, h =>
      have hQ : 2 ≤ (args Q).length := by rw [args_app] at h2; simp at h2; omega
      obtain ⟨_, y', _, hv'⟩ := R_strip Q z v hQ h
      rw [hv'] at hv; simp [lastArg] at hv

theorem N_ne_S (k : Nat) : N k ≠ S := by
  cases k <;> simp [N, B]

theorem lastArg_N (k : Nat) : lastArg (N k) ≠ S := by
  cases k with
  | zero => simp [N, B, SS, lastArg]
  | succ k => simp only [N, lastArg]; exact N_ne_S k

/-- an R-chain of length t ending at B starts at N t -/
theorem Rchain_to_B : ∀ (t : Nat) (y : Nat → T), y t = B → (∀ s, s < t → R (y s) (y (s + 1))) → y 0 = N t := by
  intro t
  induction t with
  | zero => intro y h _; simpa [N] using h
  | succ t ih =>
    intro y ht hR
    -- shift: y' s = y (s + 1)
    have h1 := ih (fun s => y (s + 1)) ht (fun s hs => hR (s + 1) (by omega))
    have h0 := R_into (y 0) (y 1) (by simp at h1; rw [h1]; exact lastArg_N t) (hR 0 (by omega))
    simp at h1
    rw [h0, h1]; rfl

end RC

#print axioms RC.restart_detail
#print axioms RC.Rchain_to_B

namespace RC

open C
open C.T
open TC

/-! ### determinism of head runs -/

theorem reach_head (X Y : List T) (h : Reach X Y) : Y = X ∨ ∃ X', step X = some X' ∧ Reach X' Y := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
    rcases ih with rfl | ⟨X', hX', hr⟩
    · exact Or.inr ⟨_, hs, Reach.refl⟩
    · exact Or.inr ⟨X', hX', Reach.tail hr hs⟩

theorem reach_trans (A B C : List T) (h1 : Reach A B) (h2 : Reach B C) : Reach A C := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact Reach.tail ih hs

theorem reach_linear (A B C : List T) (hB : Reach A B) (hC : Reach A C) : Reach B C ∨ Reach C B := by
  induction hC with
  | refl => exact Or.inr hB
  | tail hC' hs ih =>
    rename_i C' C2
    rcases ih with h | h
    · exact Or.inl (Reach.tail h hs)
    · rcases reach_head _ _ h with rfl | ⟨X', hX', hr⟩
      · exact Or.inl (Reach.tail Reach.refl hs)
      · rw [hs] at hX'
        simp only [Option.some.injEq] at hX'
        subst hX'
        exact Or.inr hr

theorem reach_det (A B1 B2 : List T) (h1 : Reach A B1) (h2 : Reach A B2) (l1 : B1.length ≤ 2)
    (l2 : B2.length ≤ 2) : B1 = B2 := by
  rcases reach_linear A B1 B2 h1 h2 with h | h
  · exact (reach_stuck _ _ l1 h).symm
  · exact reach_stuck _ _ l2 h

/-! ### the reload set is closed under tail calls -/

theorem args_N_succ (i : Nat) : args (N (i + 1)) = [S, N i] := rfl

theorem args_B : args B = [SS, SS] := rfl

theorem closure (i m : Nat) (q' : T) (him : i < m) (h : TCStep (app (N i) (N m)) q') :
    ∃ i' m', i' < m' ∧ q' = app (N i') (N m') := by
  obtain ⟨p, hr, _⟩ := h
  cases i with
  | succ i =>
    have hr1 : Reach (args (app (N (i + 1)) (N m))) [N m, app (N i) (N m)] := by
      apply Reach.tail Reach.refl
      rw [args_app, args_N_succ]
      rfl
    have := reach_det _ _ _ hr hr1 (by simp) (by simp)
    simp only [List.cons.injEq] at this
    exact ⟨i, m, by omega, this.2.1⟩
  | zero =>
    have s1 : step (args (app (N 0) (N m))) = some [S, N m, app SS (N m)] := rfl
    have s2 : step [S, N m, app SS (N m)] = some [N (m + 1), app (N m) (N (m + 1))] := rfl
    have hr1 : Reach (args (app (N 0) (N m))) [N (m + 1), app (N m) (N (m + 1))] :=
      Reach.tail (Reach.tail Reach.refl s1) s2
    have := reach_det _ _ _ hr hr1 (by simp) (by simp)
    simp only [List.cons.injEq] at this
    exact ⟨m, m + 1, by omega, this.2.1⟩

/-! ### between two restarts the prefix is a counter -/

def Restart (q : T) : Prop := ∃ w, q = app w (app SS w)

theorem SSw_ne_S (w : T) : app SS w ≠ S := by intro h; cases h

theorem SSw_ne_SS (w : T) : app SS w ≠ SS := by
  intro h; simp only [SS, app.injEq] at h; exact absurd h.1 (by intro h'; cases h')

/-- a node whose multiplier is y.Z with y having <= 1 argument cannot make two tail calls in a row -/
theorem short_dies (y Z q1 q2 : T) (hy : (args y).length ≤ 1) (hZ : Z = app SS (lchild Z) ∨ True)
    (h1 : TCStep (app y Z) q1) (h2 : TCStep q1 q2) (hZS : ∃ w, Z = app SS w) : False := by
  obtain ⟨w, rfl⟩ := hZS
  obtain ⟨p1, hr1, _⟩ := h1
  have hl : (args (app y (app SS w))).length ≤ 2 := by rw [args_app]; simp; omega
  have e := (reach_stuck _ _ hl hr1)
  rw [args_app] at e
  have hq1 : q1 = app SS w := by
    have := congrArg List.getLast? e; simp at this; exact this
  subst hq1
  obtain ⟨p2, hr2, hf2⟩ := h2
  have e2 := (reach_stuck _ _ (by rw [args_app]; simp [SS, args]) hr2)
  -- args (S S w) = [S, w], so p2 = S, which is not a fuel head
  have hp2 : p2 = S := by
    have : args (app SS w) = [S, w] := rfl
    rw [this] at e2
    simp only [List.cons.injEq] at e2
    exact e2.1
  subst hp2
  rcases hf2 with h | ⟨y', hy'⟩
  · cases h
  · exact R_S y' hy'

theorem next_restart : ∀ (d j : Nat) (f : Nat → T), (∀ i, TCStep (f i) (f (i + 1))) →
    Restart (f j) → Restart (f (j + d + 1)) → ∃ k, f j = app (N k) (N (k + 1)) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro j f hstep hj hjd
    by_cases hmid : ∃ d', d' < d ∧ Restart (f (j + d' + 1))
    · obtain ⟨d', hd', hr⟩ := hmid
      exact ih d' hd' j f hstep hj hr
    · have hno : ∀ s, 1 ≤ s → s ≤ d → ¬ Restart (f (j + s)) := by
        intro s hs1 hsd hr
        exact hmid ⟨s - 1, by omega, by rw [show j + (s - 1) + 1 = j + s by omega]; exact hr⟩
      obtain ⟨w, hw⟩ := hj
      -- prefixes y s := lchild (f (j + s)); invariant for s <= d
      have inv : ∀ s, s ≤ d → f (j + s) = app (lchild (f (j + s))) (app SS w) ∧
          2 ≤ (args (lchild (f (j + s)))).length ∧
          (∀ s', s' < s → R (lchild (f (j + s'))) (lchild (f (j + s' + 1)))) ∧
          (0 < s → size (lchild (f (j + s))) < size w) := by
        intro s
        induction s with
        | zero =>
          intro _
          refine ⟨by simp [hw, lchild], ?_, fun s' hs' => absurd hs' (by omega), fun h => absurd h (by omega)⟩
          by_cases h1 : (args w).length ≤ 1
          · exfalso
            have h1' := hstep j
            rw [hw] at h1'
            exact short_dies w (app SS w) _ _ h1 (Or.inr trivial) h1' (hstep (j + 1)) ⟨w, rfl⟩
          · simp [hw, lchild]; omega
        | succ s ihs =>
          intro hsd
          obtain ⟨hfs, hlen, hR, hsz⟩ := ihs (by omega)
          have hst := hstep (j + s)
          rw [hfs] at hst
          obtain ⟨p, hr, hfuel⟩ := hst
          rcases restart_detail _ _ p _ hlen (SSw_ne_S w) (SSw_ne_SS w) hr hfuel with ⟨y, hy, hq⟩ | ⟨_, hq⟩
          · have hq' : f (j + (s + 1)) = app y (app SS w) := by rw [show j + (s + 1) = j + s + 1 by omega, hq]
            have hyl : lchild (f (j + (s + 1))) = y := by rw [hq']; rfl
            refine ⟨by rw [hq']; rfl, ?_, ?_, ?_⟩
            · rw [hyl]
              by_cases h1 : (args y).length ≤ 1
              · exfalso
                have h1' := hstep (j + (s + 1))
                rw [hq'] at h1'
                exact short_dies y (app SS w) _ _ h1 (Or.inr trivial) h1' (hstep (j + (s + 1) + 1)) ⟨w, rfl⟩
              · omega
            · intro s' hs'
              by_cases hss : s' < s
              · exact hR s' hss
              · have : s' = s := by omega
                subst this
                rw [show j + s' + 1 = j + (s' + 1) by omega, hyl]; exact hy
            · intro _
              have h1 := R_shrinks _ _ _ (Nat.le_refl _) hy
              rw [hyl]
              by_cases hs0 : s = 0
              · subst hs0
                have : lchild (f (j + 0)) = w := by simp [hw, lchild]
                rw [this] at h1; exact h1
              · have := hsz (by omega); omega
          · exfalso
            exact hno (s + 1) (by omega) hsd ⟨app SS w, by rw [show j + (s + 1) = j + s + 1 by omega, hq]⟩
      -- the step from f (j + d) into the restart f (j + d + 1)
      obtain ⟨hfd, hlen, hR, hsz⟩ := inv d (Nat.le_refl d)
      have hst := hstep (j + d)
      rw [hfd] at hst
      obtain ⟨p, hr, hfuel⟩ := hst
      rcases restart_detail _ _ p _ hlen (SSw_ne_S w) (SSw_ne_SS w) hr hfuel with ⟨y, hy, hq⟩ | ⟨hB, _⟩
      · -- an R-step cannot produce the restart shape: it would make the prefix w again, but prefixes shrink
        exfalso
        obtain ⟨w', hw'⟩ := hjd
        rw [hq] at hw'
        simp only [app.injEq] at hw'
        obtain ⟨hyw, hZ⟩ := hw'
        have hww : w = w' := by
          first
            | exact hZ
            | exact hZ.2
            | (simp only [SS, app.injEq] at hZ; exact hZ.2)
        have h1 := R_shrinks _ _ _ (Nat.le_refl _) hy
        rw [hyw, ← hww] at h1
        by_cases hd0 : d = 0
        · subst hd0
          have : lchild (f (j + 0)) = w := by simp [hw, lchild]
          rw [this] at h1; omega
        · have := hsz (by omega); omega
      · -- the prefix chain w = y 0 -> ... -> y d = B: w = N d
        have hchain := Rchain_to_B d (fun s => lchild (f (j + s))) hB (fun s hs => hR s hs)
        simp only [Nat.add_zero] at hchain
        have hwl : lchild (f j) = w := by simp [hw, lchild]
        rw [hwl] at hchain
        exact ⟨d, by rw [hw, hchain]; rfl⟩

/-- **Reload classification.**  An infinite chain of fuel-S tail calls q_j.S -> q_(j+1).S of the leftmost path, whose
    terms never have last argument S, is eventually the reload cycle: from some index on every q_j is N i . N m with
    i < m (N 0 = S(SS)(SS), N (k+1) = S S (N k)). -/
theorem reload_classification (f : Nat → T) (hstep : ∀ j, TCStep (f j) (f (j + 1)))
    (hlast : ∀ j, lastArg (f j) ≠ S) : ∃ J, ∀ j, J ≤ j → ∃ i m, i < m ∧ f j = app (N i) (N m) := by
  obtain ⟨j1, _, w1, hw1⟩ := restarts f hstep hlast 0
  obtain ⟨j2, hj2, w2, hw2⟩ := restarts f hstep hlast (j1 + 1)
  have hd : j2 = j1 + (j2 - j1 - 1) + 1 := by omega
  obtain ⟨k, hk⟩ := next_restart (j2 - j1 - 1) j1 f hstep ⟨w1, hw1⟩ (by rw [← hd]; exact ⟨w2, hw2⟩)
  refine ⟨j1, ?_⟩
  have all : ∀ t, ∃ i m, i < m ∧ f (j1 + t) = app (N i) (N m) := by
    intro t
    induction t with
    | zero => exact ⟨k, k + 1, by omega, by simpa using hk⟩
    | succ t iht =>
      obtain ⟨i, m, him, hf⟩ := iht
      have hs := hstep (j1 + t)
      rw [hf] at hs
      obtain ⟨i', m', him', hq⟩ := closure i m _ him hs
      exact ⟨i', m', him', by rw [show j1 + (t + 1) = j1 + t + 1 by omega]; exact hq⟩
  intro j hj
  have := all (j - j1)
  rw [show j1 + (j - j1) = j by omega] at this
  exact this

end RC

#print axioms RC.reload_classification

/-! ## Tail calls over a closed fuel Z /= S (Conjecture F, tail-call case) -/

namespace FZ

open C
open C.T

/-- the last element is a.w with w larger than Z -/
def RBig (Z : T) (L : List T) : Prop := ∃ M a w, L = M ++ [app a w] ∧ size Z < size w

theorem rbig_step (Z : T) (L L' : List T) (hB : RBig Z L) (hs : step L = some L') : RBig Z L' := by
  obtain ⟨M, a0, w0, rfl, hw⟩ := hB
  match M, hs with
  | [], hs => simp [step] at hs
  | [_], hs => simp [step] at hs
  | [a, b], hs =>
    simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
    subst hs
    refine ⟨args a ++ [app a0 w0], b, app a0 w0, by simp, ?_⟩
    simp [size]; omega
  | a :: b :: c :: M', hs =>
    simp only [List.cons_append, step, Option.some.injEq] at hs
    subst hs
    exact ⟨args a ++ c :: app b c :: M', a0, w0, by simp, hw⟩

theorem rbig_reach (Z : T) (A B : List T) (hA : RBig Z A) (h : Reach A B) : RBig Z B := by
  induction h with
  | refl => exact hA
  | tail _ hs ih => exact rbig_step Z _ _ ih hs

theorem rbig_final (Z : T) (A : List T) (x y : T) (hA : RBig Z A) (h : Reach A [x, y]) (hne : A ≠ [x, y]) :
    ∃ a w, x = app a w ∧ size Z < size w := by
  cases h with
  | refl => exact absurd rfl hne
  | tail h1 hs =>
    rename_i L1
    match L1, hs with
    | a0 :: b0 :: c0 :: R0, hs =>
      simp only [step, Option.some.injEq] at hs
      have hlen := congrArg List.length hs
      simp at hlen
      have ha : args a0 = [] := by
        cases h' : args a0 with
        | nil => rfl
        | cons _ _ => rw [h'] at hlen; simp at hlen; omega
      have hR : R0 = [] := by
        cases R0 with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hR
      rw [ha] at hs
      simp only [List.nil_append, List.cons.injEq] at hs
      obtain ⟨M, a1, w1, hM, hw1⟩ := rbig_reach Z _ _ hA h1
      have hlast : app a1 w1 = c0 := by
        have := congrArg List.getLast? hM; simp at this; exact this.symm
      exact ⟨a1, w1, by rw [← hs.1, ← hlast], hw1⟩

def FInvZ (Lq : List T) (Z : T) (L2 : List T) : Prop :=
  (∃ L1, Reach Lq L1 ∧ 2 ≤ L1.length ∧ L2 = L1 ++ [Z]) ∨
  (∃ p c P2, Reach Lq [p, c] ∧ Reach (args p ++ [Z]) P2 ∧ 2 ≤ P2.length ∧ L2 = P2 ++ [app c Z]) ∨
  (∃ p c d', Reach Lq [p, c] ∧ Reach (args p ++ [Z]) [S, d'] ∧ L2 = [app c Z, app d' (app c Z)]) ∨
  (∃ p c c' d', Reach Lq [p, c] ∧ Reach (args p ++ [Z]) [c', d'] ∧ c' ≠ S ∧
      Reach (args c' ++ [app c Z, app d' (app c Z)]) L2) ∨
  (∃ c, Reach Lq [S, c] ∧ L2 = [Z, app c Z])

theorem finvz_step (Lq : List T) (Z : T) (L2 L3 : List T) (hI : FInvZ Lq Z L2) (hs : step L2 = some L3) :
    FInvZ Lq Z L3 := by
  rcases hI with ⟨L1, hr, hlen, rfl⟩ | ⟨p, c, P2, hr, hP, hlen, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ |
      ⟨p, c, c', d', hr, hP, hc', hr2⟩ | ⟨_, _, rfl⟩
  · by_cases h3 : 3 ≤ L1.length
    · obtain ⟨L1', h1'⟩ := step_exists L1 h3
      rw [step_append L1 L1' [Z] h3 h1'] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inl ⟨L1', Reach.tail hr h1', step_len _ _ h1', rfl⟩
    · have h2 : L1.length = 2 := by omega
      match L1, h2, hr, hs with
      | [p, c], _, hr, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hpS : p = S
        · subst hpS
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, hr, by simp [args]⟩)))
        · refine Or.inr (Or.inl ⟨p, c, args p ++ [Z], hr, Reach.refl, ?_, by simp⟩)
          have := TC.args_ne_nil p hpS; simp; omega
  · by_cases h3 : 3 ≤ P2.length
    · obtain ⟨P2', h1'⟩ := step_exists P2 h3
      rw [step_append P2 P2' [app c Z] h3 h1'] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inr (Or.inl ⟨p, c, P2', hr, Reach.tail hP h1', step_len _ _ h1', rfl⟩)
    · have h2 : P2.length = 2 := by omega
      match P2, h2, hP, hs with
      | [c', d'], _, hP, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hcS : c' = S
        · subst hcS
          exact Or.inr (Or.inr (Or.inl ⟨p, c, d', hr, hP, by simp [args]⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, c, c', d', hr, hP, hcS, Reach.refl⟩)))
  · simp [step] at hs
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, c, c', d', hr, hP, hc', Reach.tail hr2 hs⟩)))
  · simp [step] at hs

theorem finvz_reach (Lq : List T) (Z : T) (hL : 2 ≤ Lq.length) (L2 : List T) (h : Reach (Lq ++ [Z]) L2) :
    FInvZ Lq Z L2 := by
  induction h with
  | refl => exact Or.inl ⟨Lq, Reach.refl, hL, rfl⟩
  | tail _ hs ih => exact finvz_step Lq Z _ _ ih hs

/-- **Tail call over a closed fuel.**  If q has >= 2 arguments, Z /= S, and the leftmost child of the node q.Z is
    q'.Z (a single pushed multiplier), then H(q) = S (S S) q'. -/
theorem tail_call_fuel (q q' Z d : T) (hq : 2 ≤ (args q).length) (hZ : Z ≠ S)
    (h : Reach (args (app q Z)) [app q' Z, d]) : R2 q q' := by
  rw [args_app] at h
  rcases finvz_reach (args q) Z hq _ h with ⟨L1, _, hlen, hEq⟩ | ⟨p, c, P2, _, _, hlen, hEq⟩ |
      ⟨p, c, d', hr, hP, hEq⟩ | ⟨p, c, c', d', _, _, hc', hr2⟩ | ⟨c, _, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq, app.injEq] at hEq
    obtain ⟨⟨hcq, _⟩, _⟩ := hEq
    -- args p ++ [Z] reaches [S, d'] only in zero steps, so p = S S
    have hp : p = app S S := by
      by_cases hp2 : 2 ≤ (args p).length
      · rcases final_shape (args p) Z S d' hp2 hP with ⟨hS, _⟩ | hbig
        · exact absurd hS.symm hZ
        · simp [size] at hbig; have := size_pos Z; omega
      · have hl : (args p ++ [Z]).length ≤ 2 := by simp; omega
        have e := reach_stuck _ _ hl hP
        match hap : args p, e with
        | [p0], e =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
          rw [TC.args_one' p p0 hap, ← e.1]
        | [], e => simp at e
        | _ :: _ :: _, _ => rw [hap] at hp2; simp at hp2
    unfold R2
    rw [hp, ← hcq] at hr
    exact hr
  · exfalso
    have hB : RBig Z (args c' ++ [app c Z, app d' (app c Z)]) :=
      ⟨args c' ++ [app c Z], d', app c Z, by simp, by simp [size]; have := size_pos c; omega⟩
    by_cases hne : args c' ++ [app c Z, app d' (app c Z)] = [app q' Z, d]
    · have hl := congrArg List.length hne
      simp at hl
      have : args c' = [] := by
        cases h' : args c' with
        | nil => rfl
        | cons _ _ => rw [h'] at hl; simp at hl
      exact hc' (args_nil c' this)
    · obtain ⟨a, w, hx, hw⟩ := rbig_final Z _ _ _ hB hr2 hne
      simp only [app.injEq] at hx
      rw [← hx.2] at hw
      omega
  · simp only [List.cons.injEq] at hEq
    obtain ⟨h0, _⟩ := hEq
    have := congrArg size h0
    simp [size] at this; have := size_pos q'; omega

/-- **No infinite tail-call walk over a closed fuel Z /= S**: there is no infinite sequence of multipliers q_j (each
    with >= 2 arguments) such that the leftmost child of q_j.Z is q_(j+1).Z. -/
theorem no_tail_calls_fuel (Z : T) (hZ : Z ≠ S) (f : Nat → T)
    (h : ∀ j, 2 ≤ (args (f j)).length ∧ ∃ d, Reach (args (app (f j) Z)) [app (f (j + 1)) Z, d]) : False := by
  apply no_R2_chain f
  intro j
  obtain ⟨hl, d, hr⟩ := h j
  exact tail_call_fuel (f j) (f (j + 1)) Z d hl hZ hr

end FZ

#print axioms FZ.tail_call_fuel
#print axioms FZ.no_tail_calls_fuel

namespace FZ
open C
open C.T

/-- **Tail call over the fuel S.**  If q has >= 2 arguments and the leftmost child of the node q.S is q'.S, then the
    step is a fuel-S tail call of the multipliers (TC.TCStep q q'). -/
theorem tail_call_S (q q' d : T) (hq : 2 ≤ (args q).length) (h : Reach (args (app q S)) [app q' S, d]) :
    TC.TCStep q q' := by
  rw [args_app] at h
  rcases finvz_reach (args q) S hq _ h with ⟨L1, _, hlen, hEq⟩ | ⟨p, c, P2, _, _, hlen, hEq⟩ |
      ⟨p, c, d', hr, hP, hEq⟩ | ⟨p, c, c', d', _, _, hc', hr2⟩ | ⟨c, _, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq, app.injEq] at hEq
    obtain ⟨⟨hcq, _⟩, _⟩ := hEq
    refine ⟨p, by rw [hcq]; exact hr, ?_⟩
    by_cases hp2 : 2 ≤ (args p).length
    · rcases final_shape (args p) S S d' hp2 hP with ⟨_, y, hy, _⟩ | hbig
      · exact Or.inr ⟨y, hy⟩
      · simp [size] at hbig
    · left
      have hl : (args p ++ [S]).length ≤ 2 := by simp; omega
      have e := reach_stuck _ _ hl hP
      match hap : args p, e with
      | [p0], e =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
        rw [TC.args_one' p p0 hap, ← e.1]
      | [], e => simp at e
      | _ :: _ :: _, _ => rw [hap] at hp2; simp at hp2
  · exfalso
    have hB : RBig S (args c' ++ [app c S, app d' (app c S)]) :=
      ⟨args c' ++ [app c S], d', app c S, by simp, by simp [size]; have := size_pos c; omega⟩
    by_cases hne : args c' ++ [app c S, app d' (app c S)] = [app q' S, d]
    · have hl := congrArg List.length hne
      simp at hl
      have : args c' = [] := by
        cases h' : args c' with
        | nil => rfl
        | cons _ _ => rw [h'] at hl; simp at hl
      exact hc' (args_nil c' this)
    · obtain ⟨a, w, hx, hw⟩ := rbig_final S _ _ _ hB hr2 hne
      simp only [app.injEq] at hx
      rw [← hx.2] at hw
      simp [size] at hw
  · simp only [List.cons.injEq] at hEq
    obtain ⟨h0, _⟩ := hEq
    cases h0

/-- **Walk-level reload classification.**  An infinite leftmost walk through nodes q_j.S in which every child is the
    next node q_(j+1).S (pure tail calls over the fuel S; every q_j with >= 2 arguments and last argument /= S) is
    eventually the reload cycle N_i N_m S (i < m). -/
theorem walk_reload (f : Nat → T) (d : Nat → T)
    (h : ∀ j, 2 ≤ (args (f j)).length ∧ Reach (args (app (f j) S)) [app (f (j + 1)) S, d j])
    (hlast : ∀ j, TC.lastArg (f j) ≠ S) :
    ∃ J, ∀ j, J ≤ j → ∃ i m, i < m ∧ f j = app (RC.N i) (RC.N m) :=
  RC.reload_classification f (fun j => tail_call_S (f j) (f (j + 1)) (d j) (h j).1 (h j).2) hlast

end FZ

#print axioms FZ.tail_call_S
#print axioms FZ.walk_reload

/-! ## Full classification: every infinite chain of fuel-S tail calls is eventually the reload cycle -/

namespace RC2

open C
open C.T
open TC
open RC

/-- all outcomes of a fuel-S tail call from q = Q.z (Q with >= 2 arguments), for an arbitrary last argument z -/
theorem tc_detail (Q z p q' : T) (hQ : 2 ≤ (args Q).length)
    (h : Reach (args (app Q z)) [p, q']) (hfuel : p = SS ∨ ∃ y, R p y) :
    (∃ y, R Q y ∧ q' = app y z) ∨ (∃ w, q' = app w (app SS w)) ∨
    (z = S ∧ ∃ x c, (x = SS ∧ q' = app S (app c S)) ∨ (∃ y, R x y ∧ q' = app (app y S) (app c S))) := by
  rw [args_app] at h
  rcases cinv_reach Q z hQ _ h with ⟨L1, _, hlen, hEq⟩ | ⟨x, c, w, P, _, _, _, hlen, hEq⟩ |
      ⟨x, c, w, b, hx, hH, hP, hEq⟩ | ⟨y, hy, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq] at hEq
    obtain ⟨hp, hq, _⟩ := hEq
    by_cases hw : w = S
    · -- the last wrap was the first one, with bottom z = S
      subst hw
      right; right
      have hz : z = S := by
        rcases hH with ⟨hwz, _⟩ | ⟨_, _, _, hw0, _, _⟩
        · exact hwz.symm
        · cases hw0
      refine ⟨hz, x, c, ?_⟩
      by_cases hx2 : 2 ≤ (args x).length
      · rcases final_shape (args x) S S b hx2 hP with ⟨_, y, hy, hb⟩ | hbig
        · right; exact ⟨y, hy, by rw [hq, hb]⟩
        · simp [size] at hbig
      · left
        have hl : (args x ++ [S]).length ≤ 2 := by simp; omega
        have e := reach_stuck _ _ hl hP
        match hax : args x, e with
        | [x0], e =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
          refine ⟨by rw [args_one' x x0 hax, ← e.1]; rfl, by rw [hq, e.2.1]⟩
        | [], e => simp at e
        | _ :: _ :: _, _ => rw [hax] at hx2; simp at hx2
    · -- w /= S: x = S S, b = w, c = S S: a restart
      right; left
      have hx1 : (args x).length = 1 := by
        by_cases hx2 : 2 ≤ (args x).length
        · rcases final_shape (args x) w S b hx2 hP with ⟨hwS, _⟩ | hbig
          · exact absurd hwS.symm hw
          · simp [size] at hbig; have := size_pos w; omega
        · have := args_ne_nil x hx; omega
      have hl : (args x ++ [w]).length ≤ 2 := by simp; omega
      have e := reach_stuck _ _ hl hP
      have hbw : b = w := by
        match hax : args x, e with
        | [x0], e =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
          exact e.2.1
        | [], e => simp at e
        | _ :: _ :: _, _ => rw [hax] at hx1; simp at hx1
      have hc : c = SS := by
        rcases hfuel with hSS | ⟨y, hy⟩
        · rw [hp] at hSS
          simp only [SS, app.injEq] at hSS
          exact absurd hSS.2 hw
        · rw [hp] at hy
          by_cases hc2 : 2 ≤ (args c).length
          · exact absurd (R_strip c w y hc2 hy).1 hw
          · have hl2 : (args (app c w)).length ≤ 2 := by rw [args_app]; simp; omega
            have e2 := R_short _ _ hl2 hy
            rw [args_app] at e2
            match hac : args c, e2 with
            | [c0], e2 =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at e2
              rw [args_one' c c0 hac, e2.1]; rfl
            | [], e2 => simp at e2
            | _ :: _ :: _, _ => rw [hac] at hc2; simp at hc2
      exact ⟨w, by rw [hq, hbw, hc]⟩
  · left
    simp only [List.cons.injEq] at hEq
    exact ⟨y, hy, hEq.2.1⟩

/-- multipliers with at most one argument, and S S X, make no tail call -/
theorem no_tc_small (q q' : T) (h : (args q).length ≤ 1) : ¬ TCStep q q' := by
  intro ⟨p, hr, _⟩
  have := reach_stuck _ _ (by omega) hr
  have hl := congrArg List.length this
  simp at hl; omega

theorem no_tc_SS (X q' : T) : ¬ TCStep (app SS X) q' := by
  intro ⟨p, hr, hf⟩
  have e := reach_stuck _ _ (by rw [args_app]; simp [SS, args]) hr
  have hp : p = S := by
    have : args (app SS X) = [S, X] := rfl
    rw [this] at e
    simp only [List.cons.injEq] at e
    exact e.1
  subst hp
  rcases hf with h | ⟨y, hy⟩
  · cases h
  · exact R_S y hy

/-- a 2-argument multiplier S p z makes the tail call to z -/
theorem tc_two (q q' : T) (h : (args q).length = 2) (ht : TCStep q q') : ∃ p, q = app (app S p) q' := by
  obtain ⟨p, hr, _⟩ := ht
  have e := (reach_stuck _ _ (by omega) hr).symm
  exact ⟨p, args_two q p q' e⟩

/-- I: the multiplier has a last argument of the form S S W -/
def I (q : T) : Prop := ∃ P W, q = app P (app SS W)

theorem I_step (q q1 q2 : T) (hI : I q) (h1 : TCStep q q1) (h2 : TCStep q1 q2) : I q1 := by
  obtain ⟨P, W, rfl⟩ := hI
  by_cases hP : 2 ≤ (args P).length
  · obtain ⟨p, hr, hf⟩ := h1
    rcases tc_detail P (app SS W) p q1 hP hr hf with ⟨y, _, hq⟩ | ⟨w, hq⟩ | ⟨hz, _⟩
    · exact ⟨y, W, hq⟩
    · exact ⟨w, w, hq⟩
    · cases hz
  · exfalso
    by_cases hP1 : (args P).length = 1
    · have h2' : (args (app P (app SS W))).length = 2 := by rw [args_app]; simp; omega
      obtain ⟨p, hq⟩ := tc_two _ _ h2' h1
      -- q1 is the last argument S S W
      have : q1 = app SS W := by
        simp only [app.injEq] at hq; exact hq.2.symm
      rw [this] at h2
      exact no_tc_SS W q2 h2
    · exact no_tc_small _ q1 (by rw [args_app, List.length_append]; simp only [List.length_singleton]; omega) h1

theorem I_forever (f : Nat → T) (hstep : ∀ j, TCStep (f j) (f (j + 1))) (j0 : Nat) (h0 : I (f j0)) :
    ∀ t, I (f (j0 + t)) := by
  intro t
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    exact I_step _ _ _ ih (hstep (j0 + t)) (hstep (j0 + t + 1))

theorem I_lastArg (q : T) (h : I q) : lastArg q ≠ S := by
  obtain ⟨P, W, rfl⟩ := h
  exact SSw_ne_S W

/-- PS: the prefix has last argument S and the last argument is not S -/
def PS (q : T) : Prop := ∃ P z, q = app P z ∧ lastArg P = S ∧ z ≠ S

theorem PS_step (q q1 q2 : T) (hPS : PS q) (hnI : ¬ I q1) (h1 : TCStep q q1) (_h2 : TCStep q1 q2) :
    PS q1 ∧ size q1 < size q := by
  obtain ⟨P, z, rfl, hP, hz⟩ := hPS
  by_cases hP2 : 2 ≤ (args P).length
  · obtain ⟨p, hr, hf⟩ := h1
    rcases tc_detail P z p q1 hP2 hr hf with ⟨y, hy, hq⟩ | ⟨w, hq⟩ | ⟨hzS, _⟩
    · -- an R-step keeps the prefix's last argument S and shrinks the prefix
      match P, hP2, hP, hy with
      | S, hP2, _, _ => simp [args] at hP2
      | app P' S, hP2, _, hy =>
        have hsz := R_shrinks _ _ _ (Nat.le_refl _) hy
        have hly : lastArg y = S := by
          by_cases hP'2 : 2 ≤ (args P').length
          · obtain ⟨_, y', _, hyy⟩ := R_strip P' S y hP'2 hy
            rw [hyy]; rfl
          · have hl2 : (args (app P' S)).length ≤ 2 := by
              rw [args_app, List.length_append]; simp only [List.length_singleton]; omega
            have e := R_short _ _ hl2 hy
            rw [args_app] at e
            have : y = S := by
              have := congrArg List.getLast? e; simp at this; exact this.symm
            rw [this]; rfl
        refine ⟨⟨y, z, hq, hly, hz⟩, ?_⟩
        rw [hq]; simp [size] at hsz ⊢; omega
      | app P' (app _ _), _, hP, _ => simp [lastArg] at hP
    · exact absurd ⟨w, w, hq⟩ hnI
    · exact absurd hzS hz
  · exfalso
    by_cases hP1 : (args P).length = 1
    · -- P = S S
      match P, hP1, hP with
      | app P0 S, hP1, _ =>
        have : args P0 = [] := by
          have := congrArg List.length (show args (app P0 S) = args P0 ++ [S] from rfl)
          rw [hP1] at this; simp at this
          cases h' : args P0 with
          | nil => rfl
          | cons _ _ => rw [h'] at this; simp at this
        have hP0 := args_nil P0 this
        subst hP0
        exact no_tc_SS z q1 h1
      | S, hP1, _ => simp [args] at hP1
      | app _ (app _ _), _, hP => simp [lastArg] at hP
    · exact no_tc_small _ q1 (by rw [args_app, List.length_append]; simp only [List.length_singleton]; omega) h1

/-- in a chain without the invariant I, the steps before a wrap shrink the multiplier -/
theorem shrink_or_wrap (q q1 q2 : T) (hnI : ¬ I q1) (h1 : TCStep q q1) (h2 : TCStep q1 q2) :
    size q1 < size q ∨ PS q1 := by
  by_cases hq : (args q).length ≤ 2
  · left
    by_cases hq1 : (args q).length ≤ 1
    · exact absurd h1 (no_tc_small q q1 hq1)
    · obtain ⟨p, hp⟩ := tc_two q q1 (by omega) h1
      rw [hp]; simp [size]; have := size_pos p; omega
  · match q, hq, h1 with
    | S, hq, _ => simp [args] at hq
    | app Q z, hq, h1 =>
      have hQ : 2 ≤ (args Q).length := by rw [args_app] at hq; simp at hq; omega
      obtain ⟨p, hr, hf⟩ := h1
      rcases tc_detail Q z p q1 hQ hr hf with ⟨y, hy, hq1⟩ | ⟨w, hq1⟩ | ⟨_, x, c, ⟨_, hq1⟩ | ⟨y, _, hq1⟩⟩
      · left
        have := R_shrinks _ _ _ (Nat.le_refl _) hy
        rw [hq1]; simp [size]; omega
      · exact absurd ⟨w, w, hq1⟩ hnI
      · exfalso; rw [hq1] at h2; exact no_tc_small _ q2 (by simp [args]) h2
      · right; exact ⟨app y S, app c S, hq1, rfl, by intro h; cases h⟩

/-- **Every infinite chain of fuel-S tail calls is eventually the reload cycle.** -/
theorem reload_classification_full (f : Nat → T) (hstep : ∀ j, TCStep (f j) (f (j + 1))) :
    ∃ J, ∀ j, J ≤ j → ∃ i m, i < m ∧ f j = app (N i) (N m) := by
  -- step 1: the invariant I holds at some index
  have hI : ∃ j0, I (f j0) := by
    refine Classical.byContradiction (fun hno => ?_)
    have hnI : ∀ j, ¬ I (f j) := fun j h => hno ⟨j, h⟩
    -- either the multipliers shrink forever (impossible) or some step reaches PS, after which they shrink forever
    have hPS : ∃ j, PS (f j) := by
      refine Classical.byContradiction (fun hno2 => ?_)
      have hdec : ∀ j, size (f (j + 1)) < size (f j) := by
        intro j
        rcases shrink_or_wrap _ _ _ (hnI (j + 1)) (hstep j) (hstep (j + 1)) with h | h
        · exact h
        · exact absurd ⟨j + 1, h⟩ hno2
      have : ∀ k, size (f k) + k ≤ size (f 0) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => have := hdec k; omega
      have := this (size (f 0) + 1); omega
    obtain ⟨j1, hj1⟩ := hPS
    have hPSall : ∀ t, PS (f (j1 + t)) ∧ size (f (j1 + t)) + t ≤ size (f j1) := by
      intro t
      induction t with
      | zero => exact ⟨by simpa using hj1, by simp⟩
      | succ t ih =>
        obtain ⟨hps, hsz⟩ := ih
        obtain ⟨hps', hlt⟩ := PS_step _ _ _ hps (hnI (j1 + t + 1)) (hstep (j1 + t)) (hstep (j1 + t + 1))
        rw [show j1 + (t + 1) = j1 + t + 1 by omega]
        exact ⟨hps', by omega⟩
    have := (hPSall (size (f j1) + 1)).2; omega
  -- step 2: from there on the last arguments are not S; apply the classification
  obtain ⟨j0, h0⟩ := hI
  have hall := I_forever f hstep j0 h0
  obtain ⟨J, hJ⟩ := reload_classification (fun t => f (j0 + t))
    (fun t => by rw [show j0 + (t + 1) = j0 + t + 1 by omega]; exact hstep (j0 + t))
    (fun t => I_lastArg _ (hall t))
  refine ⟨j0 + J, fun j hj => ?_⟩
  have := hJ (j - j0) (by omega)
  rw [show j0 + (j - j0) = j by omega] at this
  exact this

end RC2

#print axioms RC2.reload_classification_full

/-- **Walk-level, unconditional.**  An infinite leftmost walk through nodes q_j.S in which every child is the next node
    q_(j+1).S (pure tail calls over the fuel S, every q_j with >= 2 arguments) is eventually the reload cycle. -/
theorem walk_reload_full (f : Nat → C.T) (d : Nat → C.T)
    (h : ∀ j, 2 ≤ (C.args (f j)).length ∧ C.Reach (C.args (C.T.app (f j) C.T.S)) [C.T.app (f (j + 1)) C.T.S, d j]) :
    ∃ J, ∀ j, J ≤ j → ∃ i m, i < m ∧ f j = C.T.app (RC.N i) (RC.N m) :=
  RC2.reload_classification_full f (fun j => FZ.tail_call_S (f j) (f (j + 1)) (d j) (h j).1 (h j).2)

#print axioms walk_reload_full
