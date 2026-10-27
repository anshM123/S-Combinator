/-
  Core of the unique-redex analysis, formalised (main agent, 2026-10-26). Plain Lean 4 core, no Mathlib.

  S-terms, their argument lists (the head of every S-term is S), the head machine on lists
      [a, b, c] ++ R  ⇒  args a ++ [c, b·c] ++ R,
  normal forms, and the "unique-redex" condition on a list (all elements normal, second element with at most one
  argument). Proved here:
    * `step_nf`        a good list steps to a list of normal forms;
    * `end_lemma`      if the first element is S, the step can only stay good when the second element is S;
    * `dying_lemma`    (Theorem UR-R, step (2)) from [c, S c, S z c] ++ P with normal forms, the run is not
                       unique-redex for ever.
-/

inductive Tm where
  | S : Tm
  | app : Tm → Tm → Tm
deriving DecidableEq, Repr

namespace Tm

/-- the argument list of a term (every S-term has head S) -/
def args : Tm → List Tm
  | S => []
  | app f x => args f ++ [x]

/-- normal form: no node has three or more arguments -/
def nf : Tm → Prop
  | S => True
  | app f x => (args f).length + 1 ≤ 2 ∧ nf f ∧ nf x

@[simp] theorem args_S : args S = [] := rfl
@[simp] theorem args_app (f x : Tm) : args (app f x) = args f ++ [x] := rfl

theorem args_length_app (f x : Tm) : (args (app f x)).length = (args f).length + 1 := by
  simp [args]

/-- every argument of a normal form is a normal form, and there are at most two -/
theorem nf_args : ∀ t : Tm, nf t → (args t).length ≤ 2 ∧ ∀ a ∈ args t, nf a
  | S, _ => by simp
  | app f x, h => by
    obtain ⟨hl, hf, hx⟩ := h
    have ih := nf_args f hf
    refine ⟨by simp [args]; omega, ?_⟩
    intro a ha
    simp [args] at ha
    rcases ha with ha | ha
    · exact ih.2 a ha
    · subst ha; exact hx

end Tm

open Tm

/-- one head-machine step -/
def step : List Tm → Option (List Tm)
  | a :: b :: c :: R => some (args a ++ c :: app b c :: R)
  | _ => none

/-- the unique-redex condition on a list: at least three elements, all normal forms, the second one with at most one
    argument (then the head redex is the only redex) -/
def good (L : List Tm) : Prop :=
  match L with
  | _ :: b :: _ :: _ => (∀ e ∈ L, nf e) ∧ (args b).length ≤ 1
  | _ => False

/-- iterate the machine -/
def run : Nat → List Tm → Option (List Tm)
  | 0, L => some L
  | n + 1, L => match step L with
    | some L' => run n L'
    | none => none

/-- the run from L keeps a unique redex for ever -/
def urForever (L : List Tm) : Prop := ∀ n, ∃ L', run n L = some L' ∧ good L'

/-- a product b·c with b of at most one argument is a normal form when b and c are -/
theorem nf_app_of_small (b c : Tm) (hb : nf b) (hc : nf c) (hlen : (args b).length ≤ 1) : nf (app b c) := by
  exact ⟨by omega, hb, hc⟩

/-- a good list steps to a list of normal forms -/
theorem step_nf (a b c : Tm) (R : List Tm) (h : good (a :: b :: c :: R)) :
    ∀ e ∈ args a ++ c :: app b c :: R, nf e := by
  obtain ⟨hall, hb⟩ := h
  have ha : nf a := hall a (by simp)
  have hbn : nf b := hall b (by simp)
  have hcn : nf c := hall c (by simp)
  intro e he
  simp at he
  rcases he with he | he | he | he
  · exact (nf_args a ha).2 e he
  · subst he; exact hcn
  · subst he; exact nf_app_of_small b c hbn hcn hb
  · exact hall e (by simp [he])

/-- End lemma: if the first element is S, the next list can only be good when the second element is S. -/
theorem end_lemma (b c : Tm) (R : List Tm) (h : good (args S ++ c :: app b c :: R)) : b = S := by
  simp [good] at h
  cases R with
  | nil => simp [good] at h
  | cons d R' =>
    simp [good] at h
    obtain ⟨_, hlen⟩ := h
    cases b with
    | S => rfl
    | app f x => simp [args] at hlen

/-- run (n + 1) unfolds through step -/
theorem run_succ (n : Nat) (L L' : List Tm) (h : step L = some L') : run (n + 1) L = run n L' := by
  simp [run, h]

/-- refuting `urForever` by one bad step count -/
theorem not_ur_of (L : List Tm) (n : Nat) (h : ∀ L', run n L = some L' → ¬ good L') : ¬ urForever L := by
  intro hu
  obtain ⟨L', h1, h2⟩ := hu n
  exact h L' h1 h2

/-- urForever passes to the next list -/
theorem ur_step (L L' : List Tm) (hs : step L = some L') (hu : urForever L) : urForever L' := by
  intro n
  obtain ⟨L'', h1, h2⟩ := hu (n + 1)
  exact ⟨L'', by rw [← run_succ n L L' hs]; exact h1, h2⟩

/-- a list whose second element has two or more arguments is not good -/
theorem not_good_of_second (a b : Tm) (R : List Tm) (hb : 2 ≤ (args b).length) : ¬ good (a :: b :: R) := by
  intro h
  cases R with
  | nil => simp [good] at h
  | cons c R' =>
    simp only [good] at h
    omega

/-- a list containing a term with three or more arguments is not good -/
theorem not_good_of_wide (L : List Tm) (e : Tm) (he : e ∈ L) (hw : 3 ≤ (args e).length) : ¬ good L := by
  intro h
  match L, h with
  | _ :: _ :: _ :: _, ⟨hall, _⟩ =>
    have := (nf_args e (hall e he)).1
    omega

theorem args_SS (z c : Tm) : args (app (app S z) c) = [z, c] := by simp [args]

/-- the inner induction of the dying lemma: during the round the third element stays w = S z c, where c has two
    arguments; the run cannot keep a unique redex -/
theorem dying_aux (z x' t' : Tm) :
    ∀ (x u : Tm) (Q : List Tm),
      ¬ urForever (x :: u :: app (app S z) (app (app S x') t') :: Q)
  | S, u, Q => by
    intro hu
    have hs : step (S :: u :: app (app S z) (app (app S x') t') :: Q)
        = some (app (app S z) (app (app S x') t') :: app u (app (app S z) (app (app S x') t')) :: Q) := by
      simp [step]
    have hu1 := ur_step _ _ hs hu
    cases u with
    | app f y =>
      apply not_ur_of _ 0 _ hu1
      intro L' h1
      simp [run] at h1; subst h1
      apply not_good_of_second
      simp [args]
    | S =>
      cases Q with
      | nil =>
        apply not_ur_of _ 0 _ hu1
        intro L' h1; simp [run] at h1; subst h1; simp [good]
      | cons q Q' =>
        have hs2 : step (app (app S z) (app (app S x') t') :: app S (app (app S z) (app (app S x') t')) :: q :: Q')
            = some (z :: app (app S x') t' :: q :: app (app S (app (app S z) (app (app S x') t'))) q :: Q') := by
          simp [step, args]
        have hu2 := ur_step _ _ hs2 hu1
        apply not_ur_of _ 0 _ hu2
        intro L' h1; simp [run] at h1; subst h1
        apply not_good_of_second
        simp [args]
  | app S x1, u, Q => by
    intro hu
    have hs : step (app S x1 :: u :: app (app S z) (app (app S x') t') :: Q)
        = some (x1 :: app (app S z) (app (app S x') t') :: app u (app (app S z) (app (app S x') t')) :: Q) := by
      simp [step, args]
    have hu1 := ur_step _ _ hs hu
    apply not_ur_of _ 0 _ hu1
    intro L' h1; simp [run] at h1; subst h1
    apply not_good_of_second
    simp [args]
  | app (app S x1) t1, u, Q => by
    intro hu
    have hs : step (app (app S x1) t1 :: u :: app (app S z) (app (app S x') t') :: Q)
        = some (x1 :: t1 :: app (app S z) (app (app S x') t') :: app u (app (app S z) (app (app S x') t')) :: Q) := by
      simp [step, args]
    exact dying_aux z x' t' x1 t1 _ (ur_step _ _ hs hu)
  | app (app (app g a) b) d, u, Q => by
    intro hu
    apply not_ur_of _ 0 _ hu
    intro L' h1; simp [run] at h1; subst h1
    apply not_good_of_wide _ (app (app (app g a) b) d) (by simp)
    simp [args]

/-- Dying lemma (Theorem UR-R, step (2)): a round start [c, S c, S z c] ++ P never keeps a unique redex for ever. -/
theorem dying_lemma (c z : Tm) (P : List Tm) : ¬ urForever (c :: app S c :: app (app S z) c :: P) := by
  match c with
  | S =>
    intro hu
    have hs : step (S :: app S S :: app (app S z) S :: P) = some (app (app S z) S :: app (app S S) (app (app S z) S) :: P) := by
      simp [step]
    have hu1 := ur_step _ _ hs hu
    apply not_ur_of _ 0 _ hu1
    intro L' h1; simp [run] at h1; subst h1
    apply not_good_of_second
    simp [args]
  | app S x1 =>
    intro hu
    have hs : step (app S x1 :: app S (app S x1) :: app (app S z) (app S x1) :: P)
        = some (x1 :: app (app S z) (app S x1) :: app (app S (app S x1)) (app (app S z) (app S x1)) :: P) := by
      simp [step, args]
    have hu1 := ur_step _ _ hs hu
    apply not_ur_of _ 0 _ hu1
    intro L' h1; simp [run] at h1; subst h1
    apply not_good_of_second
    simp [args]
  | app (app S x1) t1 =>
    intro hu
    have hs : step (app (app S x1) t1 :: app S (app (app S x1) t1) :: app (app S z) (app (app S x1) t1) :: P)
        = some (x1 :: t1 :: app (app S z) (app (app S x1) t1)
                 :: app (app S (app (app S x1) t1)) (app (app S z) (app (app S x1) t1)) :: P) := by
      simp [step, args]
    exact dying_aux z x1 t1 x1 t1 _ (ur_step _ _ hs hu)
  | app (app (app g a) b) d =>
    intro hu
    apply not_ur_of _ 0 _ hu
    intro L' h1; simp [run] at h1; subst h1
    apply not_good_of_wide _ (app (app (app g a) b) d) (by simp)
    simp [args]


/-- A = S S S, the last layer of a round that ends with a type-2 step whose argument is S -/
def A : Tm := app (app S S) S

/-- Φ-successor (Theorem UR-R, step (3)): if the run from [A, u, v] ++ P keeps a unique redex for ever, then u = S.
    Then the next round starts at [v, S v, S v] ++ P, a Φ-round. -/
theorem phi_successor (u v : Tm) (P : List Tm) (hu : urForever (A :: u :: v :: P)) : u = S := by
  have hs1 : step (A :: u :: v :: P) = some (S :: S :: v :: app u v :: P) := by simp [step, A, args]
  have h1 := ur_step _ _ hs1 hu
  have hs2 : step (S :: S :: v :: app u v :: P) = some (v :: app S v :: app u v :: P) := by simp [step]
  have h2 := ur_step _ _ hs2 h1
  match u, h2, hu with
  | S, _, _ => rfl
  | app S z, h2, _ => exact absurd h2 (dying_lemma v z P)
  | app (app f a) b, _, hu =>
    exfalso
    obtain ⟨L', hrun, hgood⟩ := hu 0
    simp [run] at hrun; subst hrun
    exact not_good_of_second _ _ _ (by simp [args]) hgood

/-- the list two steps later is the Φ-state [v, S v, S v] ++ P -/
theorem phi_successor_state (u v : Tm) (P : List Tm) (hu : urForever (A :: u :: v :: P)) :
    run 2 (A :: u :: v :: P) = some (v :: app S v :: app S v :: P) := by
  have hS := phi_successor u v P hu
  subst hS
  simp [run, step, A, args]


/-- run composes -/
theorem run_add : ∀ (m n : Nat) (L L' : List Tm), run m L = some L' → run (m + n) L = run n L'
  | 0, n, L, L', h => by simp [run] at h; subst h; simp
  | m + 1, n, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      have := run_add m n L1 L' h
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [run, hs]; exact this

/-- urForever passes along the run -/
theorem ur_run : ∀ (n : Nat) (L L' : List Tm), run n L = some L' → urForever L → urForever L'
  | 0, L, L', h, hu => by simp [run] at h; subst h; exact hu
  | n + 1, L, L', h, hu => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 => rw [hs] at h; exact ur_run n L1 L' h (ur_step L L1 hs hu)

/-- from [S, b, c] ++ R a run that keeps a unique redex for ever has b = S -/
theorem end_of_ur (b c : Tm) (R : List Tm) (hu : urForever (S :: b :: c :: R)) : b = S := by
  obtain ⟨L', h1, h2⟩ := hu 1
  simp [run, step] at h1; subst h1
  exact end_lemma b c R (by simpa using h2)

/-- Walk lemma: inside a round of a run with a unique redex for ever, starting from a good list [x, u, v] ++ Q with
    x ≠ S and v ≠ S, the run reaches a list whose first element is A = S S S. -/
theorem walk_to_A : ∀ (x u v : Tm) (Q : List Tm), x ≠ S → v ≠ S → urForever (x :: u :: v :: Q) →
    ∃ n u' v' Q', run n (x :: u :: v :: Q) = some (A :: u' :: v' :: Q')
  | S, _, _, _, hx, _, _ => absurd rfl hx
  | app S x1, u, v, Q, _, hv, hu => by
    have hs : step (app S x1 :: u :: v :: Q) = some (x1 :: v :: app u v :: Q) := by simp [step, args]
    have hu1 := ur_step _ _ hs hu
    by_cases hx1 : x1 = S
    · subst hx1
      exact absurd (end_of_ur v (app u v) Q hu1) hv
    · obtain ⟨n, u', v', Q', h⟩ := walk_to_A x1 v (app u v) Q hx1 (by simp) hu1
      exact ⟨n + 1, u', v', Q', by rw [run_succ n _ _ hs]; exact h⟩
  | app (app S x1) t, u, v, Q, _, hv, hu => by
    by_cases hx1 : x1 = S
    · subst hx1
      have hs : step (app (app S S) t :: u :: v :: Q) = some (S :: t :: v :: app u v :: Q) := by simp [step, args]
      have ht := end_of_ur t v (app u v :: Q) (ur_step _ _ hs hu)
      subst ht
      exact ⟨0, u, v, Q, by simp [run, A]⟩
    · have hs : step (app (app S x1) t :: u :: v :: Q) = some (x1 :: t :: v :: app u v :: Q) := by simp [step, args]
      obtain ⟨n, u', v', Q', h⟩ := walk_to_A x1 t v (app u v :: Q) hx1 hv (ur_step _ _ hs hu)
      exact ⟨n + 1, u', v', Q', by rw [run_succ n _ _ hs]; exact h⟩
  | app (app (app g a) b) d, u, v, Q, _, _, hu => by
    exfalso
    obtain ⟨L', h1, h2⟩ := hu 0
    simp [run] at h1; subst h1
    exact not_good_of_wide _ (app (app (app g a) b) d) (by simp) (by simp [args]) h2

/-- Theorem UR-R, Φ-rounds follow Φ-rounds: from a Φ-state [c, S c, S c] ++ P of a run with a unique redex for ever,
    the run reaches another Φ-state [c', S c', S c'] ++ P' after n ≥ 1 steps. -/
theorem phi_next (c : Tm) (P : List Tm) (hu : urForever (c :: app S c :: app S c :: P)) :
    ∃ n c' P', 0 < n ∧ run n (c :: app S c :: app S c :: P) = some (c' :: app S c' :: app S c' :: P') := by
  by_cases hc : c = S
  · subst hc
    exfalso
    obtain ⟨L', h1, h2⟩ := hu 1
    simp [run, step] at h1; subst h1
    exact not_good_of_second _ _ _ (by simp [args]) h2
  · obtain ⟨n, u', v', Q', h⟩ := walk_to_A c (app S c) (app S c) P hc (by simp) hu
    have hA := ur_run n _ _ h hu
    have h2 := phi_successor_state u' v' Q' hA
    exact ⟨n + 2, v', Q', by omega, by rw [run_add n 2 _ _ h]; exact h2⟩

/-- Consequently a run with a unique redex for ever that reaches a Φ-state passes through Φ-states for ever. -/
theorem phi_forever (c : Tm) (P : List Tm) (hu : urForever (c :: app S c :: app S c :: P)) :
    ∀ k, ∃ n c' P', k ≤ n ∧ run n (c :: app S c :: app S c :: P) = some (c' :: app S c' :: app S c' :: P') := by
  intro k
  induction k with
  | zero => exact ⟨0, c, P, by omega, by simp [run]⟩
  | succ k ih =>
    obtain ⟨n, c1, P1, hk, h1⟩ := ih
    obtain ⟨m, c2, P2, hm, h2⟩ := phi_next c1 P1 (ur_run n _ _ h1 hu)
    exact ⟨n + m, c2, P2, by omega, by rw [run_add n m _ _ h1]; exact h2⟩

/-- Lemma R (unique-redex form): from any list [x, u, v] ++ Q of a run with a unique redex for ever, the run reaches a
    round start [c, S c, d] ++ Q'. -/
theorem reach_round : ∀ (x u v : Tm) (Q : List Tm), urForever (x :: u :: v :: Q) →
    ∃ n c d Q', 0 < n ∧ run n (x :: u :: v :: Q) = some (c :: app S c :: d :: Q')
  | S, u, v, Q, hu => by
    have hS := end_of_ur u v Q hu
    subst hS
    cases Q with
    | nil =>
      exfalso
      obtain ⟨L', h1, h2⟩ := hu 1
      simp [run, step] at h1; subst h1; simp [good] at h2
    | cons q Q' => exact ⟨1, v, q, Q', by omega, by simp [run, step]⟩
  | app S x1, u, v, Q, hu => by
    have hs : step (app S x1 :: u :: v :: Q) = some (x1 :: v :: app u v :: Q) := by simp [step, args]
    obtain ⟨n, c, d, Q', _, h⟩ := reach_round x1 v (app u v) Q (ur_step _ _ hs hu)
    exact ⟨n + 1, c, d, Q', by omega, by rw [run_succ n _ _ hs]; exact h⟩
  | app (app S x1) t, u, v, Q, hu => by
    have hs : step (app (app S x1) t :: u :: v :: Q) = some (x1 :: t :: v :: app u v :: Q) := by simp [step, args]
    obtain ⟨n, c, d, Q', _, h⟩ := reach_round x1 t v (app u v :: Q) (ur_step _ _ hs hu)
    exact ⟨n + 1, c, d, Q', by omega, by rw [run_succ n _ _ hs]; exact h⟩
  | app (app (app g a) b) e, u, v, Q, hu => by
    exfalso
    obtain ⟨L', h1, h2⟩ := hu 0
    simp [run] at h1; subst h1
    exact not_good_of_wide _ (app (app (app g a) b) e) (by simp) (by simp [args]) h2

/-- a round start whose third element is not S leads to a Φ-state -/
theorem phi_of_round (c d : Tm) (Q : List Tm) (hd : d ≠ S) (hu : urForever (c :: app S c :: d :: Q)) :
    ∃ n c' P', run n (c :: app S c :: d :: Q) = some (c' :: app S c' :: app S c' :: P') := by
  by_cases hc : c = S
  · subst hc
    exfalso
    have := end_of_ur (app S S) d Q hu
    simp at this
  · obtain ⟨n, u', v', Q', h⟩ := walk_to_A c (app S c) d Q hc hd hu
    have h2 := phi_successor_state u' v' Q' (ur_run n _ _ h hu)
    exact ⟨n + 2, v', Q', by rw [run_add n 2 _ _ h]; exact h2⟩

/-- Generalised walk (the third element may be S): the round either reaches A, or reaches a type-1 layer S S while the
    third element is S; in the second case either nothing was pushed (n = 0) or the fourth element is an application. -/
theorem walk_gen : ∀ (x u v : Tm) (Q : List Tm), x ≠ S → urForever (x :: u :: v :: Q) →
    (∃ n u' v' Q', run n (x :: u :: v :: Q) = some (A :: u' :: v' :: Q')) ∨
    (∃ n u' Q', run n (x :: u :: v :: Q) = some (app S S :: u' :: S :: Q') ∧
       ((n = 0 ∧ Q' = Q) ∨ ∃ a b Q'', Q' = app a b :: Q''))
  | S, _, _, _, hx, _ => absurd rfl hx
  | app S x1, u, v, Q, _, hu => by
    by_cases hx1 : x1 = S
    · subst hx1
      have hs : step (app S S :: u :: v :: Q) = some (S :: v :: app u v :: Q) := by simp [step, args]
      have hv := end_of_ur v (app u v) Q (ur_step _ _ hs hu)
      subst hv
      exact Or.inr ⟨0, u, Q, by simp [run], Or.inl ⟨rfl, rfl⟩⟩
    · have hs : step (app S x1 :: u :: v :: Q) = some (x1 :: v :: app u v :: Q) := by simp [step, args]
      have hu1 := ur_step _ _ hs hu
      obtain ⟨n, u', v', Q', h⟩ := walk_to_A x1 v (app u v) Q hx1 (by simp) hu1
      exact Or.inl ⟨n + 1, u', v', Q', by rw [run_succ n _ _ hs]; exact h⟩
  | app (app S x1) t, u, v, Q, _, hu => by
    by_cases hx1 : x1 = S
    · subst hx1
      have hs : step (app (app S S) t :: u :: v :: Q) = some (S :: t :: v :: app u v :: Q) := by simp [step, args]
      have ht := end_of_ur t v (app u v :: Q) (ur_step _ _ hs hu)
      subst ht
      exact Or.inl ⟨0, u, v, Q, by simp [run, A]⟩
    · have hs : step (app (app S x1) t :: u :: v :: Q) = some (x1 :: t :: v :: app u v :: Q) := by simp [step, args]
      rcases walk_gen x1 t v (app u v :: Q) hx1 (ur_step _ _ hs hu) with ⟨n, u', v', Q', h⟩ | ⟨n, u', Q', h, hq⟩
      · exact Or.inl ⟨n + 1, u', v', Q', by rw [run_succ n _ _ hs]; exact h⟩
      · refine Or.inr ⟨n + 1, u', Q', by rw [run_succ n _ _ hs]; exact h, Or.inr ?_⟩
        rcases hq with ⟨_, hQ⟩ | hq
        · exact ⟨u, v, Q, hQ⟩
        · exact hq
  | app (app (app g a) b) e, u, v, Q, _, hu => by
    exfalso
    obtain ⟨L', h1, h2⟩ := hu 0
    simp [run] at h1; subst h1
    exact not_good_of_wide _ (app (app (app g a) b) e) (by simp) (by simp [args]) h2

/-- from [S S, u, S] ++ Q' the run reaches the round start [u·S, S (u·S)] ++ Q' two steps later -/
theorem e2_next (u : Tm) (Q' : List Tm) :
    run 2 (app S S :: u :: S :: Q') = some (app u S :: app S (app u S) :: Q') := by
  simp [run, step, args]

/-- Theorem UR-R (a), entry into the Φ-regime: every run with a unique redex for ever reaches a Φ-state. -/
theorem reach_phi (x u v : Tm) (Q : List Tm) (hu : urForever (x :: u :: v :: Q)) :
    ∃ n c P, run n (x :: u :: v :: Q) = some (c :: app S c :: app S c :: P) := by
  obtain ⟨n1, c, d, Q1, _, h1⟩ := reach_round x u v Q hu
  have hu1 := ur_run n1 _ _ h1 hu
  have finish : ∀ (m : Nat) (c d : Tm) (Q1 : List Tm), d ≠ S →
      run m (x :: u :: v :: Q) = some (c :: app S c :: d :: Q1) →
      ∃ n c' P, run n (x :: u :: v :: Q) = some (c' :: app S c' :: app S c' :: P) := by
    intro m c d Q1 hd hm
    obtain ⟨k, c', P', hk⟩ := phi_of_round c d Q1 hd (ur_run m _ _ hm hu)
    exact ⟨m + k, c', P', by rw [run_add m k _ _ hm]; exact hk⟩
  by_cases hd : d = S
  · subst hd
    by_cases hc : c = S
    · subst hc
      exfalso
      have := end_of_ur (app S S) S Q1 hu1
      simp at this
    · rcases walk_gen c (app S c) S Q1 hc hu1 with ⟨n2, u', v', Q', h2⟩ | ⟨n2, u', Q', h2, hq⟩
      · have h3 := phi_successor_state u' v' Q' (ur_run n2 _ _ h2 hu1)
        exact ⟨n1 + (n2 + 2), v', Q', by rw [run_add n1 _ _ _ h1, run_add n2 2 _ _ h2]; exact h3⟩
      · have h3 := e2_next u' Q'
        have hr : run (n1 + (n2 + 2)) (x :: u :: v :: Q) = some (app u' S :: app S (app u' S) :: Q') := by
          rw [run_add n1 _ _ _ h1, run_add n2 2 _ _ h2]; exact h3
        rcases hq with ⟨hn0, hQ⟩ | ⟨a, b, Q'', hQ⟩
        · subst hQ
          cases Q' with
          | nil =>
            exfalso
            obtain ⟨L', hL, hg⟩ := ur_run _ _ _ hr hu 0
            simp [run] at hL; subst hL; simp [good] at hg
          | cons q Q2 =>
            by_cases hq : q = S
            · subst hq
              subst hn0
              simp [run] at h2
              obtain ⟨hc1, hu'⟩ := h2
              subst hc1; subst hu'
              have h4 : run 3 (app (app S (app S S)) S :: app S (app (app S (app S S)) S) :: S :: Q2)
                  = some (app S S :: app S (app S S)
                          :: app (app S (app (app S (app S S)) S)) S :: Q2) := by
                simp [run, step, args]
              have h5 := (run_add _ 3 _ _ hr).trans h4
              exact finish _ _ _ _ (by simp) h5
            · exact finish _ _ _ _ hq hr
        · subst hQ
          exact finish _ _ _ _ (by simp) hr
  · exact finish n1 c d Q1 hd h1

/-! ## Towards Theorem UR-C: the round machine as a function, the Φ-map, round validity -/

/-- the round machine on x's left spine: the registers when the walk reaches S (none on a layer with ≥ 3 args) -/
def rm : Tm → Tm → Tm → Option (Tm × Tm)
  | S, u, v => some (u, v)
  | app S x1, u, v => rm x1 v (app u v)
  | app (app S x1) t, _, v => rm x1 t v
  | app (app (app _ _) _) _, _, _ => none

/-- the final v register of the round machine on x's left spine -/
def fv : Tm → Tm → Tm → Tm
  | S, _, v => v
  | app S x1, u, v => fv x1 v (app u v)
  | app (app S x1) t, _, v => fv x1 t v
  | app (app (app _ _) _) _, _, v => v

/-- the Φ-map: the next Φ-element -/
def psi (c : Tm) : Tm := fv c (app S c) (app S c)

theorem fv_of_rm : ∀ (x u v a b : Tm), rm x u v = some (a, b) → fv x u v = b
  | S, u, v, a, b, h => by
    simp only [rm, Option.some.injEq, Prod.mk.injEq] at h
    simp only [fv]; exact h.2
  | app S x1, u, v, a, b, h => by
    simp only [rm] at h; simp only [fv]; exact fv_of_rm x1 v (app u v) a b h
  | app (app S x1) t, u, v, a, b, h => by
    simp only [rm] at h; simp only [fv]; exact fv_of_rm x1 t v a b h
  | app (app (app _ _) _) _, _, _, _, _, h => by simp [rm] at h

theorem rm_A (u v : Tm) : rm A u v = some (S, v) := by simp [rm, A]

/-- walk lemma with the round machine: the v register at A is the round machine's final v -/
theorem walk_to_A_rm : ∀ (x u v : Tm) (Q : List Tm), x ≠ S → v ≠ S → urForever (x :: u :: v :: Q) →
    ∃ n u' v' Q', run n (x :: u :: v :: Q) = some (A :: u' :: v' :: Q') ∧ rm x u v = some (S, v')
  | S, _, _, _, hx, _, _ => absurd rfl hx
  | app S x1, u, v, Q, _, hv, hu => by
    have hs : step (app S x1 :: u :: v :: Q) = some (x1 :: v :: app u v :: Q) := by simp [step, args]
    have hu1 := ur_step _ _ hs hu
    by_cases hx1 : x1 = S
    · subst hx1
      exact absurd (end_of_ur v (app u v) Q hu1) hv
    · obtain ⟨n, u', v', Q', h, hr⟩ := walk_to_A_rm x1 v (app u v) Q hx1 (by simp) hu1
      exact ⟨n + 1, u', v', Q', by rw [run_succ n _ _ hs]; exact h, by simp [rm]; exact hr⟩
  | app (app S x1) t, u, v, Q, _, hv, hu => by
    by_cases hx1 : x1 = S
    · subst hx1
      have hs : step (app (app S S) t :: u :: v :: Q) = some (S :: t :: v :: app u v :: Q) := by simp [step, args]
      have ht := end_of_ur t v (app u v :: Q) (ur_step _ _ hs hu)
      subst ht
      exact ⟨0, u, v, Q, by simp [run, A], by simp [rm]⟩
    · have hs : step (app (app S x1) t :: u :: v :: Q) = some (x1 :: t :: v :: app u v :: Q) := by simp [step, args]
      obtain ⟨n, u', v', Q', h, hr⟩ := walk_to_A_rm x1 t v (app u v :: Q) hx1 hv (ur_step _ _ hs hu)
      exact ⟨n + 1, u', v', Q', by rw [run_succ n _ _ hs]; exact h, by simp [rm]; exact hr⟩
  | app (app (app g a) b) d, u, v, Q, _, _, hu => by
    exfalso
    obtain ⟨L', h1, h2⟩ := hu 0
    simp [run] at h1; subst h1
    exact not_good_of_wide _ (app (app (app g a) b) d) (by simp) (by simp [args]) h2

/-- from a Φ-state of a lasting run, the run reaches the Φ-state of ψ(c) -/
theorem phi_next_psi (c : Tm) (P : List Tm) (hu : urForever (c :: app S c :: app S c :: P)) :
    ∃ n P', 0 < n ∧ run n (c :: app S c :: app S c :: P) = some (psi c :: app S (psi c) :: app S (psi c) :: P') := by
  by_cases hc : c = S
  · subst hc
    exfalso
    obtain ⟨L', h1, h2⟩ := hu 1
    simp [run, step] at h1; subst h1
    exact not_good_of_second _ _ _ (by simp [args]) h2
  · obtain ⟨n, u', v', Q', h, hr⟩ := walk_to_A_rm c (app S c) (app S c) P hc (by simp) hu
    have h2 := phi_successor_state u' v' Q' (ur_run n _ _ h hu)
    have hp : psi c = v' := fv_of_rm _ _ _ _ _ hr
    rw [hp]
    exact ⟨n + 2, Q', by omega, by rw [run_add n 2 _ _ h]; exact h2⟩

/-- the orbit of the Φ-map -/
def orbit (c : Tm) : Nat → Tm
  | 0 => c
  | k + 1 => psi (orbit c k)

/-- a lasting run from Φ(c) passes through Φ(orbit c k) for every k -/
theorem phi_orbit (c : Tm) (P : List Tm) (hu : urForever (c :: app S c :: app S c :: P)) :
    ∀ k, ∃ n P', run n (c :: app S c :: app S c :: P) = some (orbit c k :: app S (orbit c k) :: app S (orbit c k) :: P') := by
  intro k
  induction k with
  | zero => exact ⟨0, P, by simp [run, orbit]⟩
  | succ k ih =>
    obtain ⟨n, P1, h1⟩ := ih
    obtain ⟨m, P2, _, h2⟩ := phi_next_psi (orbit c k) P1 (ur_run n _ _ h1 hu)
    exact ⟨n + m, P2, by rw [run_add n m _ _ h1]; simp only [orbit]; exact h2⟩

/-- round validity along a walk: every new second element has at most one argument, and the walk ends with u = S -/
def rv : Tm → Tm → Tm → Prop
  | S, u, _ => u = S
  | app S x1, u, v => (args v).length ≤ 1 ∧ rv x1 v (app u v)
  | app (app S x1) t, _, v => (args t).length ≤ 1 ∧ rv x1 t v
  | app (app (app _ _) _) _, _, _ => False

/-- a lasting run makes every round valid -/
theorem rv_of_ur : ∀ (x u v : Tm) (Q : List Tm), urForever (x :: u :: v :: Q) → rv x u v
  | S, u, v, Q, hu => by simp [rv]; exact end_of_ur u v Q hu
  | app S x1, u, v, Q, hu => by
    have hs : step (app S x1 :: u :: v :: Q) = some (x1 :: v :: app u v :: Q) := by simp [step, args]
    have hu1 := ur_step _ _ hs hu
    obtain ⟨L', h1, h2⟩ := hu1 0
    simp [run] at h1; subst h1
    simp only [rv]
    refine ⟨?_, rv_of_ur x1 v (app u v) Q hu1⟩
    simp only [good] at h2; exact h2.2
  | app (app S x1) t, u, v, Q, hu => by
    have hs : step (app (app S x1) t :: u :: v :: Q) = some (x1 :: t :: v :: app u v :: Q) := by simp [step, args]
    have hu1 := ur_step _ _ hs hu
    obtain ⟨L', h1, h2⟩ := hu1 0
    simp [run] at h1; subst h1
    simp only [rv]
    refine ⟨?_, rv_of_ur x1 t v (app u v :: Q) hu1⟩
    simp only [good] at h2; exact h2.2
  | app (app (app g a) b) d, u, v, Q, hu => by
    exfalso
    obtain ⟨L', h1, h2⟩ := hu 0
    simp [run] at h1; subst h1
    exact not_good_of_wide _ (app (app (app g a) b) d) (by simp) (by simp [args]) h2

/-- every round of the orbit is valid -/
theorem rv_orbit (c : Tm) (P : List Tm) (hu : urForever (c :: app S c :: app S c :: P)) :
    ∀ k, rv (orbit c k) (app S (orbit c k)) (app S (orbit c k)) := by
  intro k
  obtain ⟨n, P', h⟩ := phi_orbit c P hu k
  exact rv_of_ur _ _ _ _ (ur_run n _ _ h hu)

/-! ## Theorem UR-C: every lasting orbit of the Φ-map is eventually a linear counter of type A or type II

  Walk shapes (left-spine layers: type 1 = S x, type 2 = S x t):
    * `noOne x`     no type-1 layer;
    * `PredA z x`   type-2 layers, then (2, S z), then one type-1 layer, then no type-1 layer;
    * `PredII x`    type-2 layers, then (2, S), then two type-1 layers, then no type-1 layer.
  `walk_out` classifies the final v register of every valid walk; the pointer z of the "pred" case is a proper
  subterm, which drives the induction in `st_ind`. -/

def tsize : Tm → Nat
  | S => 1
  | app f x => tsize f + tsize x

def noOne : Tm → Prop
  | S => True
  | app S _ => False
  | app (app S x1) _ => noOne x1
  | app (app (app _ _) _) _ => True

def PredA (z : Tm) : Tm → Prop
  | S => False
  | app S _ => False
  | app (app S x1) t => (t = app S z ∧ ∃ x2, x1 = app S x2 ∧ noOne x2) ∨ PredA z x1
  | app (app (app _ _) _) _ => False

def PredII : Tm → Prop
  | S => False
  | app S _ => False
  | app (app S x1) t => (t = S ∧ ∃ x2, x1 = app S (app S x2) ∧ noOne x2) ∨ PredII x1
  | app (app (app _ _) _) _ => False

/-- S^n x -/
def iterS : Nat → Tm → Tm
  | 0, x => x
  | n + 1, x => app S (iterS n x)

theorem iterS_succ' : ∀ (n : Nat) (x : Tm), iterS n (app S x) = iterS (n + 1) x
  | 0, _ => rfl
  | n + 1, x => by
    show app S (iterS n (app S x)) = app S (iterS (n + 1) x)
    rw [iterS_succ' n x]

theorem iterS_succ_S (n : Nat) (y : Tm) : iterS (n + 1) (app S y) = app S (app S (iterS n y)) :=
  iterS_succ' (n + 1) y

theorem fv_noOne : ∀ (x u v : Tm), noOne x → fv x u v = v
  | S, _, _, _ => by simp only [fv]
  | app S _, _, _, h => by simp [noOne] at h
  | app (app S x1) t, _, v, h => by
    simp only [noOne] at h; simp only [fv]; exact fv_noOne x1 t v h
  | app (app (app _ _) _) _, _, _, _ => by simp only [fv]

theorem fv_predA (z : Tm) : ∀ (x u v : Tm), PredA z x → fv x u v = app (app S z) v
  | S, _, _, h => by simp [PredA] at h
  | app S _, _, _, h => by simp [PredA] at h
  | app (app S x1) t, _, v, h => by
    simp only [PredA] at h
    simp only [fv]
    rcases h with ⟨ht, x2, hx1, hn⟩ | h
    · subst ht; subst hx1; simp only [fv]; exact fv_noOne x2 _ _ hn
    · exact fv_predA z x1 t v h
  | app (app (app _ _) _) _, _, _, h => by simp [PredA] at h

theorem fv_predII : ∀ (x u v : Tm), PredII x → fv x u v = app v (app S v)
  | S, _, _, h => by simp [PredII] at h
  | app S _, _, _, h => by simp [PredII] at h
  | app (app S x1) t, _, v, h => by
    simp only [PredII] at h
    simp only [fv]
    rcases h with ⟨ht, x2, hx1, hn⟩ | h
    · subst ht; subst hx1; simp only [fv]; exact fv_noOne x2 _ _ hn
    · exact fv_predII x1 t v h
  | app (app (app _ _) _) _, _, _, h => by simp [PredII] at h

/-- once v has two or more arguments, a valid walk has no further type-1 layer and v is final -/
theorem rv_wide : ∀ (x u v : Tm), 2 ≤ (args v).length → rv x u v → noOne x ∧ fv x u v = v
  | S, _, _, _, _ => by simp only [noOne, fv]; exact ⟨trivial, trivial⟩
  | app S _, _, _, h2, h => by
    simp only [rv] at h
    obtain ⟨h1, _⟩ := h
    omega
  | app (app S x1) t, _, v, h2, h => by
    simp only [rv] at h
    simp only [noOne, fv]
    exact rv_wide x1 t v h2 h.2
  | app (app (app _ _) _) _, _, _, _, h => by simp [rv] at h

/-- death: a walk S (S^n y) entered with an application in u is invalid when y has a type-1 layer -/
theorem death (y U V : Tm) (hy : ¬ noOne y) (hU : 1 ≤ (args U).length) :
    ∀ n, ¬ rv (app S (iterS n y)) U V := by
  intro n h
  simp only [rv] at h
  have h2 : 2 ≤ (args (app U V)).length := by
    simp only [args_app, List.length_append, List.length_singleton]; omega
  have hn := (rv_wide _ _ _ h2 h.2).1
  cases n with
  | zero => exact hy hn
  | succ n => simp [iterS, noOne] at hn

theorem death1 (y w : Tm) (n : Nat) (hy : ¬ noOne y) (hw : w = app S (app S (iterS n y))) :
    ¬ rv w (app S w) (app S w) := by
  subst hw
  exact death y _ _ hy (by simp [args]) (n + 1)

theorem death2 (y w X : Tm) (n : Nat) (hy : ¬ noOne y) (hX : 1 ≤ (args X).length)
    (hw : w = app (app S (app S (iterS n y))) X) : ¬ rv w (app S w) (app S w) := by
  subst hw
  intro h
  simp only [rv] at h
  exact death y X _ hy hX n h.2

/-- the outcome of a walk: (a) no type-1 layer; (b) a single type-1 layer, at position 0; (c) "pred": the last
    type-1 layer follows (2, S z), z a proper subterm; (d) "cons": the last two type-1 layers are consecutive;
    (e) the last type-1 layer follows (2, S) -/
def Out (x U V r : Tm) : Prop :=
  (noOne x ∧ r = V) ∨
  (∃ x1, x = app S x1 ∧ noOne x1 ∧ r = app U V) ∨
  (∃ z j, r = app (app S z) (iterS j V) ∧ tsize z < tsize x ∧ ¬ noOne x ∧ (j = 0 → PredA z x)) ∨
  (∃ j, r = app (iterS j V) (iterS (j + 1) V) ∧ ¬ noOne x ∧
      (j = 0 → (U = S ∧ ∃ x2, x = app S (app S x2) ∧ noOne x2) ∨ PredII x)) ∨
  (∃ j, r = iterS (j + 1) V ∧ ¬ noOne x)

/-- the walk lemma of Theorem UR-C -/
theorem walk_out : ∀ (x U V : Tm), rv x U V → Out x U V (fv x U V)
  | S, U, V, _ => by
    unfold Out
    exact Or.inl ⟨by simp only [noOne], by simp only [fv]⟩
  | app S x1, U, V, h => by
    simp only [rv] at h
    simp only [fv]
    unfold Out
    by_cases hU : U = S
    · subst hU
      have ih := walk_out x1 V (app S V) h.2
      unfold Out at ih
      rcases ih with ⟨hn, hr⟩ | ⟨x2, hx, hn, hr⟩ | ⟨z, j, hr, hs, hn, hp⟩ | ⟨j, hr, hn, hp⟩ | ⟨j, hr, hn⟩
      · exact Or.inr (Or.inl ⟨x1, rfl, hn, hr⟩)
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨0, hr.trans rfl, by simp [noOne], ?_⟩)))
        intro _
        left
        exact ⟨rfl, x2, by rw [hx], hn⟩
      · refine Or.inr (Or.inr (Or.inl ⟨z, j + 1, hr.trans (by rw [iterS_succ' j V]),
          by simp only [tsize]; omega, by simp [noOne], ?_⟩))
        intro hj; exact absurd hj (by omega)
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j + 1,
          hr.trans (by rw [iterS_succ' j V, iterS_succ' (j + 1) V]), by simp [noOne], ?_⟩)))
        intro hj; exact absurd hj (by omega)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j + 1, hr.trans (by rw [iterS_succ' (j + 1) V]),
          by simp [noOne]⟩)))
    · have h2 : 2 ≤ (args (app U V)).length := by
        cases U with
        | S => exact absurd rfl hU
        | app f y => simp only [args_app, List.length_append, List.length_singleton]; omega
      obtain ⟨hn, hr⟩ := rv_wide x1 V (app U V) h2 h.2
      exact Or.inr (Or.inl ⟨x1, rfl, hn, hr⟩)
  | app (app S x1) t, U, V, h => by
    simp only [rv] at h
    have ih := walk_out x1 t V h.2
    simp only [fv]
    unfold Out at ih ⊢
    rcases ih with ⟨hn, hr⟩ | ⟨x2, hx, hn, hr⟩ | ⟨z, j, hr, hs, hn, hp⟩ | ⟨j, hr, hn, hp⟩ | ⟨j, hr, hn⟩
    · exact Or.inl ⟨by simp only [noOne]; exact hn, hr⟩
    · subst hx
      have ht := h.1
      cases t with
      | S =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, hr.trans rfl, by simp [noOne]⟩)))
      | app f z' =>
        cases f with
        | S =>
          refine Or.inr (Or.inr (Or.inl ⟨z', 0, hr.trans rfl, by simp only [tsize]; omega,
            by simp [noOne], ?_⟩))
          intro _
          simp only [PredA]
          left
          exact ⟨trivial, x2, rfl, hn⟩
        | app g w =>
          simp only [args_app, List.length_append, List.length_singleton] at ht
          omega
    · refine Or.inr (Or.inr (Or.inl ⟨z, j, hr, by simp only [tsize]; omega,
        by simp only [noOne]; exact hn, ?_⟩))
      intro hj
      simp only [PredA]
      right
      exact hp hj
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hr, by simp only [noOne]; exact hn, ?_⟩)))
      intro hj
      right
      simp only [PredII]
      exact hp hj
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hr, by simp only [noOne]; exact hn⟩)))
  | app (app (app _ _) _) _, _, _, h => by simp [rv] at h

theorem psi_t1 (c1 x : Tm) (h : c1 = app S x) (hx : noOne x) : psi c1 = app (app S c1) (app S c1) := by
  subst h
  simp only [psi, fv]
  exact fv_noOne x _ _ hx

theorem psi_t2 (c1 z X : Tm) (h : c1 = app (app S z) X) : psi c1 = fv z X (app S c1) := by
  subst h
  simp only [psi, fv]

theorem rv_t2 (c1 z X : Tm) (h : c1 = app (app S z) X) (hv : rv c1 (app S c1) (app S c1)) :
    (args X).length ≤ 1 ∧ rv z X (app S c1) := by
  subst h
  simpa only [rv] using hv

/-- type A persistence: one period of the pointer alternation β, previous element -/
theorem periodA (β γ y : Tm) (hβ : β = app S γ) (hγ : noOne γ) (hA : PredA β y) :
    psi y = app (app S β) (app S y) ∧
    psi (psi y) = app (app S y) (app S (psi y)) ∧ PredA β (psi (psi y)) := by
  have h1 : psi y = app (app S β) (app S y) := by
    simp only [psi]; exact fv_predA β y _ _ hA
  have h2 : psi (psi y) = app (app S y) (app S (psi y)) := by
    rw [h1]
    subst hβ
    simp only [psi, fv]
    exact fv_noOne γ _ _ hγ
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  simp only [PredA]
  right
  exact hA

/-- type II persistence -/
theorem periodII (y : Tm) (h : PredII y) : psi y = app (app S y) (app S (app S y)) ∧ PredII (psi y) := by
  have h1 : psi y = app (app S y) (app S (app S y)) := by
    simp only [psi]; exact fv_predII y _ _ h
  refine ⟨h1, ?_⟩
  rw [h1]
  simp only [PredII]
  right
  exact h

theorem typeA_of (c β γ : Tm) (k0 : Nat) (hβ : β = app S γ) (hγ : noOne γ) (hA : PredA β (orbit c k0)) :
    ∀ j, PredA β (orbit c (k0 + 2 * j)) := by
  intro j
  induction j with
  | zero => simpa using hA
  | succ j ih =>
    have e : k0 + 2 * (j + 1) = k0 + 2 * j + 1 + 1 := by omega
    rw [e]
    exact (periodA β γ _ hβ hγ ih).2.2

theorem typeII_of (c : Tm) (k0 : Nat) (h : PredII (orbit c k0)) : ∀ j, PredII (orbit c (k0 + j)) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih => exact (periodII _ ih).2

/-- the structural form of the conclusion: some orbit element starts type II or type A -/
def Concl (c : Tm) : Prop :=
  ∃ k0, PredII (orbit c k0) ∨ ∃ β γ, β = app S γ ∧ noOne γ ∧ PredA β (orbit c k0)

/-- (T0) a round with no type-1 layer: type A starts two rounds later -/
theorem entry_a (c : Tm) (k : Nat) (hn : noOne (orbit c k)) : Concl c := by
  have e1 : orbit c (k + 1) = app S (orbit c k) := by
    show psi (orbit c k) = _
    simp only [psi]; exact fv_noOne _ _ _ hn
  have e2 : orbit c (k + 1 + 1) = app (app S (orbit c (k + 1))) (app S (orbit c (k + 1))) :=
    psi_t1 _ _ e1 hn
  refine ⟨k + 1 + 1, Or.inr ⟨orbit c (k + 1), orbit c k, e1, hn, ?_⟩⟩
  rw [e2]
  simp only [PredA]
  left
  exact ⟨trivial, orbit c k, e1, hn⟩

/-- "pos0": a single type-1 layer at position 0: type A starts at the next round -/
theorem entry_b (c : Tm) (k : Nat) (x1 : Tm) (hx : orbit c k = app S x1) (hn : noOne x1) : Concl c := by
  have e1 : orbit c (k + 1) = app (app S (orbit c k)) (app S (orbit c k)) := psi_t1 _ _ hx hn
  refine ⟨k + 1, Or.inr ⟨orbit c k, x1, hx, hn, ?_⟩⟩
  rw [e1]
  simp only [PredA]
  left
  exact ⟨trivial, x1, hx, hn⟩

/-- the pointer induction (T1, T2, (S), (II), (A)): from c_{k+1} = S z (S^j (S c_k)) a valid orbit reaches
    type A or type II; consecutive "pred" steps strictly shrink z -/
theorem st_ind (c : Tm) (hv : ∀ k, rv (orbit c k) (app S (orbit c k)) (app S (orbit c k))) :
    ∀ n k z j, tsize z < n → orbit c (k + 1) = app (app S z) (iterS j (app S (orbit c k))) →
      ¬ noOne (orbit c k) → (j = 0 → PredA z (orbit c k)) → Concl c := by
  intro n
  induction n with
  | zero => intro k z j hs; omega
  | succ n ih =>
    intro k z j hs hk hn hp
    have hv1 := rv_t2 _ _ _ hk (hv (k + 1))
    have e2 : orbit c (k + 1 + 1) = fv z (iterS j (app S (orbit c k))) (app S (orbit c (k + 1))) :=
      psi_t2 _ _ _ hk
    have ho := walk_out z _ _ hv1.2
    unfold Out at ho
    rcases ho with ⟨hz, _⟩ | ⟨x1, hx, hx1, hr⟩ | ⟨z', j', hr, hs', hz, hp'⟩ | ⟨j', hr, hz, hp'⟩ | ⟨j', hr, hz⟩
    · exact entry_a c (k + 1) (by rw [hk]; simp only [noOne]; exact hz)
    · cases j with
      | zero => exact ⟨k, Or.inr ⟨z, x1, hx, hx1, hp rfl⟩⟩
      | succ j0 =>
        exfalso
        refine death2 (orbit c k) (orbit c (k + 1 + 1)) (app S (orbit c (k + 1))) j0 hn (by simp [args]) ?_
          (hv (k + 1 + 1))
        rw [e2, hr, iterS_succ_S]
    · refine ih (k + 1) z' j' (by omega) (e2.trans hr) (by rw [hk]; simp only [noOne]; exact hz) ?_
      intro hj
      rw [hk]
      simp only [PredA]
      right
      exact hp' hj
    · cases j' with
      | zero =>
        rcases hp' rfl with ⟨hX, _⟩ | hII
        · exfalso
          cases j <;> simp [iterS] at hX
        · refine ⟨k + 1, Or.inl ?_⟩
          rw [hk]
          simp only [PredII]
          right
          exact hII
      | succ j1 =>
        exfalso
        refine death2 (orbit c (k + 1)) (orbit c (k + 1 + 1)) (iterS (j1 + 1 + 1) (app S (orbit c (k + 1)))) j1
          (by rw [hk]; simp only [noOne]; exact hz) (by simp [iterS, args]) ?_ (hv (k + 1 + 1))
        rw [e2, hr, iterS_succ_S j1]
    · exfalso
      refine death1 (orbit c (k + 1)) (orbit c (k + 1 + 1)) j' (by rw [hk]; simp only [noOne]; exact hz) ?_
        (hv (k + 1 + 1))
      rw [e2, hr, iterS_succ_S]

/-- every valid orbit of the Φ-map reaches type A or type II -/
theorem entry (c : Tm) (hv : ∀ k, rv (orbit c k) (app S (orbit c k)) (app S (orbit c k))) : Concl c := by
  have ho := walk_out (orbit c 0) _ _ (hv 0)
  have e1 : fv (orbit c 0) (app S (orbit c 0)) (app S (orbit c 0)) = orbit c (0 + 1) := rfl
  rw [e1] at ho
  unfold Out at ho
  rcases ho with ⟨hn, _⟩ | ⟨x1, hx, hn, _⟩ | ⟨z, j, hr, _, hn, hp⟩ | ⟨j, hr, hn, hp⟩ | ⟨j, hr, hn⟩
  · exact entry_a c 0 hn
  · exact entry_b c 0 x1 hx hn
  · exact st_ind c hv (tsize z + 1) 0 z j (by omega) hr hn hp
  · cases j with
    | zero =>
      rcases hp rfl with ⟨h, _⟩ | h
      · simp at h
      · exact ⟨0, Or.inl h⟩
    | succ j1 =>
      exfalso
      refine death2 (orbit c 0) (orbit c (0 + 1)) (iterS (j1 + 1 + 1) (app S (orbit c 0))) j1 hn
        (by simp [iterS, args]) ?_ (hv (0 + 1))
      rw [hr, iterS_succ_S j1]
  · exfalso
    refine death1 (orbit c 0) (orbit c (0 + 1)) j hn ?_ (hv (0 + 1))
    rw [hr, iterS_succ_S]

/-- **Theorem UR-C.** If the run from a Φ-state Φ(c) ++ P keeps a unique redex for ever, the Φ-elements
    c_k = orbit c k are, from some round k0 on, a linear counter of type II (c_{k+1} = S c_k (S (S c_k))) or of
    type A (a fixed base β alternating with the previous element). -/
theorem ur_classification (c : Tm) (P : List Tm) (hu : urForever (c :: app S c :: app S c :: P)) :
    ∃ k0, (∀ j, orbit c (k0 + j + 1) = app (app S (orbit c (k0 + j))) (app S (app S (orbit c (k0 + j))))) ∨
      ∃ β, ∀ j, orbit c (k0 + 2 * j + 1) = app (app S β) (app S (orbit c (k0 + 2 * j))) ∧
        orbit c (k0 + 2 * j + 1 + 1) = app (app S (orbit c (k0 + 2 * j))) (app S (orbit c (k0 + 2 * j + 1))) := by
  obtain ⟨k0, hII | ⟨β, γ, hβ, hγ, hA⟩⟩ := entry c (rv_orbit c P hu)
  · exact ⟨k0, Or.inl fun j => (periodII _ (typeII_of c k0 hII j)).1⟩
  · refine ⟨k0, Or.inr ⟨β, fun j => ?_⟩⟩
    obtain ⟨h1, h2, _⟩ := periodA β γ _ hβ hγ (typeA_of c β γ k0 hβ hγ hA j)
    exact ⟨h1, h2⟩

/-- Theorems UR-R and UR-C together: every list that keeps a unique redex for ever reaches a Φ-state from which the
    Φ-elements are eventually a linear counter of type II or type A. -/
theorem ur_counter (x u v : Tm) (Q : List Tm) (hu : urForever (x :: u :: v :: Q)) :
    ∃ n c P, run n (x :: u :: v :: Q) = some (c :: app S c :: app S c :: P) ∧
      (∀ k, ∃ m P', run m (c :: app S c :: app S c :: P) =
        some (orbit c k :: app S (orbit c k) :: app S (orbit c k) :: P')) ∧
      ∃ k0, (∀ j, orbit c (k0 + j + 1) = app (app S (orbit c (k0 + j))) (app S (app S (orbit c (k0 + j))))) ∨
        ∃ β, ∀ j, orbit c (k0 + 2 * j + 1) = app (app S β) (app S (orbit c (k0 + 2 * j))) ∧
          orbit c (k0 + 2 * j + 1 + 1) = app (app S (orbit c (k0 + 2 * j))) (app S (orbit c (k0 + 2 * j + 1))) := by
  obtain ⟨n, c, P, h⟩ := reach_phi x u v Q hu
  have hc := ur_run n _ _ h hu
  exact ⟨n, c, P, h, phi_orbit c P hc, ur_classification c P hc⟩

#print axioms ur_counter
#print axioms ur_classification
#print axioms walk_out
#print axioms st_ind
#print axioms walk_to_A_rm
#print axioms phi_next_psi
#print axioms phi_orbit
#print axioms rv_orbit
#print axioms reach_round
#print axioms walk_gen
#print axioms reach_phi
#print axioms end_lemma
#print axioms step_nf
#print axioms dying_lemma
#print axioms phi_successor
#print axioms phi_successor_state
#print axioms walk_to_A
#print axioms phi_next
#print axioms phi_forever
