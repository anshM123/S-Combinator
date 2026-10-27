import EMA

/-! ## No leftmost walk repeats a node, given Waldmann's no-spiral theorem — JA (agent_work_J, 2026-10-27) -/

namespace JA

open C
open C.T

/-- one-step S-reduction: the compatible closure of S a b c -> a c (b c) -/
inductive Red1 : T → T → Prop
  | root (a b c : T) : Red1 (app (app (app S a) b) c) (app (app a c) (app b c))
  | left (f f' x : T) : Red1 f f' → Red1 (app f x) (app f' x)
  | right (f x x' : T) : Red1 x x' → Red1 (app f x) (app f x')

/-- reflexive-transitive closure of Red1 -/
inductive RedStar : T → T → Prop
  | refl (x : T) : RedStar x x
  | tail (x y z : T) : RedStar x y → Red1 y z → RedStar x z

/-- at least one reduction step -/
def RedPlus (x z : T) : Prop := ∃ y, RedStar x y ∧ Red1 y z

/-- the (reflexive) subterm relation -/
inductive Sub : T → T → Prop
  | refl (x : T) : Sub x x
  | left (x f y : T) : Sub x f → Sub x (app f y)
  | right (x f y : T) : Sub x y → Sub x (app f y)

/-- **Waldmann's no-spiral theorem** (J. Waldmann 2000; BEKW, Dance of the starlings, Theorem 14), stated as a
    proposition and used ONLY as an explicit hypothesis: no S-term M reduces in at least one step to a term
    containing M as a subterm (M ->+ C[M], C possibly trivial). -/
def NoSpiral : Prop := ∀ M N : T, RedPlus M N → ¬ Sub M N

theorem redstar_trans (x y z : T) (h1 : RedStar x y) (h2 : RedStar y z) : RedStar x z := by
  induction h2 with
  | refl => exact h1
  | tail y' z' _ hs ih => exact RedStar.tail _ _ _ ih hs

theorem redplus_star (x z : T) (h : RedPlus x z) : RedStar x z := by
  obtain ⟨y, h1, h2⟩ := h
  exact RedStar.tail _ _ _ h1 h2

theorem redplus_trans (x y z : T) (h1 : RedPlus x y) (h2 : RedPlus y z) : RedPlus x z := by
  obtain ⟨w, hw1, hw2⟩ := h2
  exact ⟨w, redstar_trans _ _ _ (redplus_star _ _ h1) hw1, hw2⟩

theorem sub_trans (a b c : T) (h1 : Sub a b) (h2 : Sub b c) : Sub a c := by
  induction h2 with
  | refl => exact h1
  | left f y _ ih => exact Sub.left _ _ _ ih
  | right f y _ ih => exact Sub.right _ _ _ ih

theorem sub_size (a b : T) (h : Sub a b) : size a ≤ size b := by
  induction h with
  | refl => exact Nat.le_refl _
  | left f y _ ih => simp only [size]; omega
  | right f y _ ih => simp only [size]; omega

theorem args_sub : ∀ (t x : T), x ∈ args t → Sub x t
  | S, x, h => by simp [args] at h
  | app f y, x, h => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact Sub.left _ _ _ (args_sub f x h)
    · exact Sub.right _ _ _ (Sub.refl _)

/-- the term S L1 L2 ... Ln -/
def mk (L : List T) : T := L.foldl app S

theorem mk_args : ∀ t : T, mk (args t) = t
  | S => rfl
  | app f x => by
    have ih := mk_args f
    unfold mk at ih ⊢
    simp only [args, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]

theorem red1_foldl (R : List T) : ∀ x y : T, Red1 x y → Red1 (R.foldl app x) (R.foldl app y) := by
  induction R with
  | nil => intro x y h; exact h
  | cons r R ih =>
    intro x y h
    simp only [List.foldl_cons]
    exact ih _ _ (Red1.left _ _ _ h)

theorem step_red (L L' : List T) (h : step L = some L') : Red1 (mk L) (mk L') := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step, Option.some.injEq] at h
    subst h
    unfold mk
    simp only [List.foldl_cons, List.foldl_append]
    have ha : List.foldl app S (args a) = a := mk_args a
    rw [ha]
    exact red1_foldl R _ _ (Red1.root a b c)

theorem reach_red (L0 L : List T) (h : Reach L0 L) : L = L0 ∨ RedPlus (mk L0) (mk L) := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
    right
    rcases ih with e | hp
    · subst e; exact ⟨_, RedStar.refl _, step_red _ _ hs⟩
    · exact ⟨_, redplus_star _ _ hp, step_red _ _ hs⟩

theorem sub_red1 (X X' : T) (h : Red1 X X') (Y : T) (hs : Sub X Y) : ∃ Y', Red1 Y Y' ∧ Sub X' Y' := by
  induction hs with
  | refl => exact ⟨X', h, Sub.refl _⟩
  | left f y _ ih =>
    obtain ⟨f', h1, h2⟩ := ih
    exact ⟨app f' y, Red1.left _ _ _ h1, Sub.left _ _ _ h2⟩
  | right f y _ ih =>
    obtain ⟨y', h1, h2⟩ := ih
    exact ⟨app f y', Red1.right _ _ _ h1, Sub.right _ _ _ h2⟩

theorem sub_redstar (X X' : T) (h : RedStar X X') : ∀ Y, Sub X Y → ∃ Y', RedStar Y Y' ∧ Sub X' Y' := by
  induction h with
  | refl => intro Y hs; exact ⟨Y, RedStar.refl _, hs⟩
  | tail y z _ hr ih =>
    intro Y hs
    obtain ⟨Y1, h1, h2⟩ := ih Y hs
    obtain ⟨Y2, h3, h4⟩ := sub_red1 _ _ hr Y1 h2
    exact ⟨Y2, RedStar.tail _ _ _ h1 h3, h4⟩

theorem sub_redplus (X X' Y : T) (h : RedPlus X X') (hs : Sub X Y) : ∃ Y', RedPlus Y Y' ∧ Sub X' Y' := by
  obtain ⟨Z, h1, h2⟩ := h
  obtain ⟨Y1, h3, h4⟩ := sub_redstar _ _ h1 Y hs
  obtain ⟨Y2, h5, h6⟩ := sub_red1 _ _ h2 Y1 h4
  exact ⟨Y2, ⟨Y1, h3, h5⟩, h6⟩

/-- one leftmost step: the child is a PROPER subterm of the node itself (pop, jump) or of a proper reduct S u' d -/
theorem lchild_red (u u' : T) (h : FH.LChild u u') :
    (Sub u' u ∧ size u' < size u) ∨ ∃ W, RedPlus u W ∧ Sub u' W ∧ size u' < size W := by
  rcases h with ⟨_, rest, hr⟩ | ⟨h3, d, hr⟩
  · left
    have hm : u' ∈ args u := by rw [hr]; exact List.mem_cons_self
    exact ⟨args_sub u u' hm, C.size_args u u' hm⟩
  · right
    rcases reach_red _ _ hr with e | hp
    · exfalso
      have := congrArg List.length e
      simp at this; omega
    · rw [mk_args] at hp
      refine ⟨app (app S u') d, hp, Sub.left _ _ _ (Sub.right _ _ _ (Sub.refl _)), ?_⟩
      simp only [size]; have := C.size_pos d; omega

/-- the segment invariant: u N reduces (possibly in zero steps) to a term V containing u M as a proper subterm,
    with at least one reduction step unless V = u N -/
theorem segment (u : Nat → T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1))) (N : Nat) :
    ∀ k, ∃ V, (V = u N ∨ RedPlus (u N) V) ∧ Sub (u (N + k + 1)) V ∧ size (u (N + k + 1)) < size V := by
  intro k
  induction k with
  | zero =>
    rcases lchild_red _ _ (hchild N) with ⟨hs, hz⟩ | ⟨W, hW, hs, hz⟩
    · exact ⟨u N, Or.inl rfl, hs, hz⟩
    · exact ⟨W, Or.inr hW, hs, hz⟩
  | succ k ih =>
    obtain ⟨V, hV, hs, hz⟩ := ih
    have hc := hchild (N + k + 1)
    rw [show N + (k + 1) + 1 = N + k + 1 + 1 by omega]
    rcases lchild_red _ _ hc with ⟨hs2, hz2⟩ | ⟨W, hW, hs2, hz2⟩
    · refine ⟨V, hV, sub_trans _ _ _ hs2 hs, ?_⟩
      have := sub_size _ _ hs; omega
    · obtain ⟨V', hV', hs3⟩ := sub_redplus _ _ _ hW hs
      refine ⟨V', ?_, sub_trans _ _ _ hs2 hs3, ?_⟩
      · rcases hV with e | hp
        · right; rw [← e]; exact hV'
        · right; exact redplus_trans _ _ _ hp hV'
      · have := sub_size _ _ hs3; omega

/-- **No repeated node (MACHINE-CHECKED, conditional on Waldmann's no-spiral theorem).**  In a leftmost walk no node
    occurs twice: u N /= u (N + k + 1).  Hence no leftmost walk is eventually periodic. -/
theorem no_repeat (hW : NoSpiral) (u : Nat → T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1))) (N k : Nat) :
    u N ≠ u (N + k + 1) := by
  intro e
  obtain ⟨V, hV, hs, hz⟩ := segment u hchild N k
  rw [← e] at hs hz
  rcases hV with e2 | hp
  · rw [e2] at hz; omega
  · exact hW _ _ hp hs

/-- **No eventually periodic leftmost walk** (conditional on Waldmann's theorem). -/
theorem no_periodic (hW : NoSpiral) (u : Nat → T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1))) :
    ¬ ∃ N P, 0 < P ∧ u (N + P) = u N := by
  rintro ⟨N, P, hP, e⟩
  apply no_repeat hW u hchild N (P - 1)
  rw [show N + (P - 1) + 1 = N + P by omega]; exact e.symm

end JA

#print axioms JA.no_repeat
#print axioms JA.no_periodic
