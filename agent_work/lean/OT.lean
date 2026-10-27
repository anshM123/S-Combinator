/-
  agent_work/lean/OT.lean  (construction agent, 2026-10-26).  Plain Lean 4 core, no Mathlib.

  Theorem OT: ordered data cannot drive a proper transfer.
  Atoms: var 0 = b (datum inside the code), var 1 = x, var 2 = y, var 3 = r (generic inputs / tape).
  A term is *proper pure-y* (`ppy`) if it is d1.(d2.(...(dm.y))) with m >= 1 and every d_i closed.
  `ordered`: every S-headed subterm has spine (closed)* ++ (non-closed)*.
  Statement (`ot_main`): if G is S-headed, ordered, and contains no y, then along the generic run from
  args G ++ [y, x.y, r] (= the list after G's opening in [G, x, y, r]) no list element containing b ever lies above a
  list element that is proper pure-y.
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

def occ (n : Nat) : T → Nat
  | S => 0
  | var m => if m = n then 1 else 0
  | app f x => occ n f + occ n x

def closed : T → Prop
  | S => True
  | var _ => False
  | app f x => closed f ∧ closed x

/-- proper pure-y -/
def ppy : T → Prop
  | app d t => closed d ∧ (t = var 2 ∨ ppy t)
  | _ => False

/-- some spine argument contains b -/
def spineHasB : T → Prop
  | app f x => spineHasB f ∨ occ 0 x ≠ 0
  | _ => False

/-- some subterm has a b-containing spine argument before a proper pure-y spine argument -/
def badT : T → Prop
  | app f x => badT f ∨ badT x ∨ (ppy x ∧ spineHasB f)
  | _ => False

/-- every S-headed subterm has spine (closed)* ++ (non-closed)* -/
def ordered : T → Prop
  | app f x => (head f = S → (closed x → closed f)) ∧ ordered f ∧ ordered x
  | _ => True

end T

open T

/-- some element containing b has a proper pure-y element somewhere below it -/
def badPairL : List T → Prop
  | [] => False
  | e :: L => (occ 0 e ≠ 0 ∧ ∃ v ∈ L, ppy v) ∨ badPairL L

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-! basic facts -/

theorem closed_head (t : T) (h : closed t) : head t = S := by
  induction t with
  | S => rfl
  | var m => simp [closed] at h
  | app f x ihf _ => simp [head]; exact ihf h.1

theorem closed_args : ∀ t : T, closed t → ∀ s ∈ args t, closed s
  | S, _ => by simp [args]
  | var _, h => by simp [closed] at h
  | app f x, h => by
    intro s hs
    simp [args] at hs
    rcases hs with hs | hs
    · exact closed_args f h.1 s hs
    · subst hs; exact h.2

theorem occ_closed (n : Nat) : ∀ t : T, closed t → occ n t = 0
  | S, _ => rfl
  | var _, h => by simp [closed] at h
  | app f x, h => by simp [occ, occ_closed n f h.1, occ_closed n x h.2]

/-- an S-headed term is closed iff all its spine arguments are -/
theorem closed_of_args : ∀ t : T, head t = S → (∀ s ∈ args t, closed s) → closed t
  | S, _, _ => trivial
  | var _, h, _ => by simp [head] at h
  | app f x, h, ha => by
    have hf : head f = S := by simpa [head] using h
    refine ⟨closed_of_args f hf (fun s hs => ha s (by simp [args, hs])), ha x (by simp [args])⟩

theorem occ_args_le (n : Nat) : ∀ t : T, ∀ s ∈ args t, occ n s ≠ 0 → occ n t ≠ 0
  | S, _, hs, _ => by simp [args] at hs
  | var _, _, hs, _ => by simp [args] at hs
  | app f x, s, hs, h => by
    simp [args] at hs
    rcases hs with hs | hs
    · have := occ_args_le n f s hs h; simp [occ]; omega
    · subst hs; simp [occ]; omega

theorem ppy_noB : ∀ t : T, ppy t → occ 0 t = 0
  | app d t, h => by
    rcases h with ⟨hd, ht | ht⟩
    · subst ht; simp [occ, occ_closed 0 d hd]
    · simp [occ, occ_closed 0 d hd, ppy_noB t ht]
  | S, h => by simp [ppy] at h
  | var _, h => by simp [ppy] at h

theorem ppy_hasY : ∀ t : T, ppy t → occ 2 t ≠ 0
  | app d t, h => by
    rcases h with ⟨_, ht | ht⟩
    · subst ht; simp [occ]
    · have := ppy_hasY t ht; simp [occ]; omega
  | S, h => by simp [ppy] at h
  | var _, h => by simp [ppy] at h

theorem spineHasB_hasB : ∀ t : T, spineHasB t → occ 0 t ≠ 0
  | app f x, h => by
    rcases h with h | h
    · have := spineHasB_hasB f h; simp [occ]; omega
    · simp [occ]; omega
  | S, h => by simp [spineHasB] at h
  | var _, h => by simp [spineHasB] at h

theorem spineHasB_of_mem : ∀ t : T, ∀ s ∈ args t, occ 0 s ≠ 0 → spineHasB t
  | S, _, hs, _ => by simp [args] at hs
  | var _, _, hs, _ => by simp [args] at hs
  | app f x, s, hs, h => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact Or.inl (spineHasB_of_mem f s hs h)
    · subst hs; exact Or.inr h

theorem badT_hasY : ∀ t : T, badT t → occ 2 t ≠ 0
  | app f x, h => by
    rcases h with h | h | ⟨h, _⟩
    · have := badT_hasY f h; simp [occ]; omega
    · have := badT_hasY x h; simp [occ]; omega
    · have := ppy_hasY x h; simp [occ]; omega
  | S, h => by simp [badT] at h
  | var _, h => by simp [badT] at h

theorem badT_of_arg : ∀ t : T, ∀ s ∈ args t, badT s → badT t
  | S, _, hs, _ => by simp [args] at hs
  | var _, _, hs, _ => by simp [args] at hs
  | app f x, s, hs, h => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact Or.inl (badT_of_arg f s hs h)
    · subst hs; exact Or.inr (Or.inl h)

theorem badPairL_append : ∀ (A B : List T),
    badPairL (A ++ B) → badPairL A ∨ badPairL B ∨ ((∃ e ∈ A, occ 0 e ≠ 0) ∧ ∃ v ∈ B, ppy v)
  | [], B, h => by simp at h; exact Or.inr (Or.inl h)
  | e :: A, B, h => by
    simp only [List.cons_append, badPairL] at h
    rcases h with ⟨he, v, hv, hp⟩ | h
    · simp at hv
      rcases hv with hv | hv
      · exact Or.inl (Or.inl ⟨he, v, hv, hp⟩)
      · exact Or.inr (Or.inr ⟨⟨e, by simp, he⟩, v, hv, hp⟩)
    · rcases badPairL_append A B h with h | h | ⟨⟨e', he', hb⟩, hv⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨⟨e', by simp [he'], hb⟩, hv⟩)

/-- a bad spine (b before proper pure-y) makes the term bad -/
theorem badT_of_args : ∀ t : T, badPairL (args t) → badT t
  | S, h => by simp [args, badPairL] at h
  | var _, h => by simp [args, badPairL] at h
  | app f x, h => by
    simp only [args] at h
    rcases badPairL_append (args f) [x] h with h | h | ⟨⟨e, he, hb⟩, v, hv, hp⟩
    · exact Or.inl (badT_of_args f h)
    · simp [badPairL] at h
    · simp at hv; subst hv
      exact Or.inr (Or.inr ⟨hp, spineHasB_of_mem f e he hb⟩)

theorem badPairL_ppy : ∀ L : List T, badPairL L → ∃ v ∈ L, ppy v
  | [], h => by simp [badPairL] at h
  | e :: L, h => by
    rcases h with ⟨_, v, hv, hp⟩ | h
    · exact ⟨v, by simp [hv], hp⟩
    · obtain ⟨v, hv, hp⟩ := badPairL_ppy L h; exact ⟨v, by simp [hv], hp⟩

/-! ordering -/

/-- I1: closed elements first, then non-closed ones -/
def I1 (L : List T) : Prop :=
  ∃ C D : List T, L = C ++ D ∧ (∀ c ∈ C, closed c) ∧ (∀ d ∈ D, ¬ closed d)

theorem ordered_args : ∀ t : T, ordered t → ∀ s ∈ args t, ordered s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact ordered_args f h.2.1 s hs
    · subst hs; exact h.2.2

theorem args_split : ∀ t : T, ordered t → head t = S → I1 (args t)
  | S, _, _ => ⟨[], [], by simp [args], by simp, by simp⟩
  | var _, _, h => by simp [head] at h
  | app f x, h, hh => by
    have hf : head f = S := by simpa [head] using hh
    obtain ⟨hcx, hof, _⟩ := h
    by_cases hx : closed x
    · have hcf : closed f := hcx hf hx
      refine ⟨args f ++ [x], [], by simp [args], ?_, by simp⟩
      intro c hc; simp at hc
      rcases hc with hc | hc
      · exact closed_args f hcf c hc
      · subst hc; exact hx
    · obtain ⟨C, D, hCD, hC, hD⟩ := args_split f hof hf
      refine ⟨C, D ++ [x], by simp [args, hCD], hC, ?_⟩
      intro d hd; simp at hd
      rcases hd with hd | hd
      · exact hD d hd
      · subst hd; exact hx

/-- in an I1 list, a closed second element forces a closed first element -/
theorem I1_first_closed (a p : T) (rest : List T) (h : I1 (a :: p :: rest)) (hp : closed p) : closed a := by
  obtain ⟨C, D, hCD, hC, hD⟩ := h
  match C, hCD with
  | [], hCD =>
    simp at hCD
    exact absurd hp (hD p (by rw [← hCD]; simp))
  | c :: C', hCD =>
    simp at hCD
    obtain ⟨rfl, _⟩ := hCD
    exact hC a (by simp)

/-- in an I1 list, if the third element is closed so is the second -/
theorem I1_second_closed (a p q : T) (rest : List T) (h : I1 (a :: p :: q :: rest)) (hq : closed q) :
    closed p := by
  obtain ⟨C, D, hCD, hC, hD⟩ := h
  match C, hCD with
  | [], hCD =>
    simp at hCD
    exact absurd hq (hD q (by rw [← hCD]; simp))
  | [c], hCD =>
    simp at hCD
    obtain ⟨_, hD'⟩ := hCD
    exact absurd hq (hD q (by rw [← hD']; simp))
  | c :: c' :: C', hCD =>
    simp at hCD
    obtain ⟨_, rfl, _⟩ := hCD
    exact hC p (by simp)

theorem I1_step (a p q : T) (R : List T) (ha : head a = S) (hI : I1 (a :: p :: q :: R))
    (ho : ordered a) : I1 (args a ++ q :: app p q :: R) := by
  obtain ⟨C, D, hCD, hC, hD⟩ := hI
  match C, hCD with
  | [], hCD =>
    -- a, p, q, R all non-closed
    simp at hCD
    obtain ⟨C', D', hs, hC', hD'⟩ := args_split a ho ha
    refine ⟨C', D' ++ q :: app p q :: R, by simp [hs], hC', ?_⟩
    intro d hd; simp at hd
    have hq : ¬ closed q := hD q (by rw [← hCD]; simp)
    rcases hd with hd | hd | hd | hd
    · exact hD' d hd
    · subst hd; exact hq
    · subst hd; intro hc; exact hq hc.2
    · exact hD d (by rw [← hCD]; simp [hd])
  | [c], hCD =>
    simp at hCD
    obtain ⟨rfl, hD'⟩ := hCD
    have hca : closed a := hC a (by simp)
    have hq : ¬ closed q := hD q (by rw [← hD']; simp)
    refine ⟨args a, q :: app p q :: R, rfl, closed_args a hca, ?_⟩
    intro d hd; simp at hd
    rcases hd with hd | hd | hd
    · subst hd; exact hq
    · subst hd; intro hc; exact hq hc.2
    · exact hD d (by rw [← hD']; simp [hd])
  | [c, c'], hCD =>
    simp at hCD
    obtain ⟨rfl, rfl, hD'⟩ := hCD
    have hca : closed a := hC a (by simp)
    have hq : ¬ closed q := hD q (by rw [← hD']; simp)
    refine ⟨args a, q :: app p q :: R, rfl, closed_args a hca, ?_⟩
    intro d hd; simp at hd
    rcases hd with hd | hd | hd
    · subst hd; exact hq
    · subst hd; intro hc; exact hq hc.2
    · exact hD d (by rw [← hD']; simp [hd])
  | c :: c' :: c'' :: C', hCD =>
    simp at hCD
    obtain ⟨rfl, rfl, rfl, hR⟩ := hCD
    have hca : closed a := hC a (by simp)
    have hcp : closed p := hC p (by simp)
    have hcq : closed q := hC q (by simp)
    refine ⟨args a ++ q :: app p q :: C', D, by simp [hR], ?_, hD⟩
    intro c hc; simp at hc
    rcases hc with hc | hc | hc | hc
    · exact closed_args a hca c hc
    · subst hc; exact hcq
    · subst hc; exact ⟨hcp, hcq⟩
    · exact hC c (by simp [hc])

theorem I2_step (a p q : T) (R : List T) (hI : I1 (a :: p :: q :: R))
    (hO : ∀ e ∈ a :: p :: q :: R, ordered e) : ∀ e ∈ args a ++ q :: app p q :: R, ordered e := by
  intro e he
  simp at he
  rcases he with he | he | he | he
  · exact ordered_args a (hO a (by simp)) e he
  · rw [he]; exact hO q (by simp)
  · subst he
    refine ⟨fun _ hq => I1_second_closed a p q R hI hq, hO p (by simp), hO q (by simp)⟩
  · exact hO e (by simp [he])

/-! the badness invariant -/

def NB (L : List T) : Prop := ¬ badPairL L ∧ ∀ e ∈ L, ¬ badT e

theorem NB_step (a p q : T) (R : List T) (hI : I1 (a :: p :: q :: R))
    (hN : NB (a :: p :: q :: R)) : NB (args a ++ q :: app p q :: R) := by
  obtain ⟨hbp, hbt⟩ := hN
  -- facts about L
  have hR_bp : ¬ badPairL R := fun h => hbp (Or.inr (Or.inr (Or.inr h)))
  have ha_nbt : ¬ badT a := hbt a (by simp)
  have hp_nbt : ¬ badT p := hbt p (by simp)
  have hq_nbt : ¬ badT q := hbt q (by simp)
  -- an element above R with b and a ppy in R would be a bad pair
  have aboveR : ∀ e, (e = a ∨ e = p ∨ e = q) → occ 0 e ≠ 0 → ∀ v ∈ R, ¬ ppy v := by
    intro e he hb v hv hpv
    apply hbp
    rcases he with rfl | rfl | rfl
    · exact Or.inl ⟨hb, v, by simp [hv], hpv⟩
    · exact Or.inr (Or.inl ⟨hb, v, by simp [hv], hpv⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hb, v, by simp [hv], hpv⟩))
  constructor
  · intro h
    rcases badPairL_append (args a) (q :: app p q :: R) h with h | h | ⟨⟨e, he, hb⟩, v, hv, hpv⟩
    · exact ha_nbt (badT_of_args a h)
    · -- inside q :: app p q :: R
      rcases h with ⟨hb, v, hv, hpv⟩ | ⟨hb, v, hv, hpv⟩ | h
      · simp at hv
        rcases hv with hv | hv
        · subst hv
          rcases hpv with ⟨_, hq | hq⟩
          · subst hq; simp [occ] at hb
          · exact hb (ppy_noB q hq)
        · exact aboveR q (Or.inr (Or.inr rfl)) hb v hv hpv
      · -- app p q has b, v in R
        have : occ 0 p ≠ 0 ∨ occ 0 q ≠ 0 := by simp [occ] at hb; omega
        rcases this with h' | h'
        · exact aboveR p (Or.inr (Or.inl rfl)) h' v hv hpv
        · exact aboveR q (Or.inr (Or.inr rfl)) h' v hv hpv
      · exact hR_bp h
    · -- an arg of a has b; a has b
      have hab : occ 0 a ≠ 0 := occ_args_le 0 a e he hb
      simp at hv
      rcases hv with hv | hv | hv
      · subst hv; exact hbp (Or.inl ⟨hab, v, by simp, hpv⟩)
      · subst hv
        -- v = app p q proper pure-y: p closed, so a closed by I1: contradiction with hab
        have hcp : closed p := hpv.1
        have hca : closed a := I1_first_closed a p (q :: R) hI hcp
        exact hab (occ_closed 0 a hca)
      · exact aboveR a (Or.inl rfl) hab v hv hpv
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact fun h => ha_nbt (badT_of_arg a e he h)
    · subst he; exact hq_nbt
    · subst he
      rintro (h | h | ⟨hq, hs⟩)
      · exact hp_nbt h
      · exact hq_nbt h
      · exact hbp (Or.inr (Or.inl ⟨spineHasB_hasB p hs, q, by simp, hq⟩))
    · exact hbt e (by simp [he])

/-- the full invariant -/
def Good (L : List T) : Prop := I1 L ∧ (∀ e ∈ L, ordered e) ∧ NB L

theorem good_step (L L' : List T) (hG : Good L) (hs : step L = some L') : Good L' := by
  match L, hs with
  | a :: p :: q :: R, hs =>
    simp only [step] at hs
    split at hs
    · rename_i ha
      injection hs with hs; subst hs
      obtain ⟨hI, hO, hN⟩ := hG
      exact ⟨I1_step a p q R ha hI (hO a (by simp)), I2_step a p q R hI hO, NB_step a p q R hI hN⟩
    · exact absurd hs (by simp)

theorem good_run : ∀ (k : Nat) (L L' : List T), Good L → run k L = some L' → Good L'
  | 0, L, L', hG, h => by simp [run] at h; subst h; exact hG
  | k + 1, L, L', hG, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      exact good_run k L1 L' (good_step L L1 hG hs) h
    · exact absurd h (by simp)

theorem occ_args_zero (n : Nat) : ∀ t : T, occ n t = 0 → ∀ s ∈ args t, occ n s = 0 := by
  intro t ht s hs
  have := occ_args_le n t s hs
  by_cases h : occ n s = 0
  · exact h
  · exact absurd ht (this h)

/-- the initial list after G's opening is Good -/
theorem good_init (G : T) (hh : head G = S) (ho : ordered G) (hy : occ 2 G = 0) :
    Good (args G ++ [var 2, app (var 1) (var 2), var 3]) := by
  obtain ⟨C, D, hCD, hC, hD⟩ := args_split G ho hh
  refine ⟨⟨C, D ++ [var 2, app (var 1) (var 2), var 3], by simp [hCD], hC, ?_⟩, ?_, ?_, ?_⟩
  · intro d hd; simp at hd
    rcases hd with hd | hd | hd | hd
    · exact hD d hd
    · subst hd; simp [closed]
    · subst hd; simp [closed]
    · subst hd; simp [closed]
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact ordered_args G ho e he
    · subst he; trivial
    · subst he; exact ⟨fun h => by simp [head] at h, trivial, trivial⟩
    · subst he; trivial
  · intro h
    obtain ⟨v, hv, hpv⟩ := badPairL_ppy _ h
    simp at hv
    rcases hv with hv | hv | hv | hv
    · exact ppy_hasY v hpv (occ_args_zero 2 G hy v hv)
    · subst hv; simp [ppy] at hpv
    · subst hv; simp [ppy, closed] at hpv
    · subst hv; simp [ppy] at hpv
  · intro e he hb
    simp at he
    rcases he with he | he | he | he
    · exact badT_hasY e hb (occ_args_zero 2 G hy e he)
    · subst he; simp [badT] at hb
    · subst he; simp [badT, ppy] at hb
    · subst he; simp [badT] at hb

/-- **Theorem OT** -/
theorem ot_main (G : T) (hh : head G = S) (ho : ordered G) (hy : occ 2 G = 0) (k : Nat) (L : List T)
    (hrun : run k (args G ++ [var 2, app (var 1) (var 2), var 3]) = some L) : ¬ badPairL L :=
  (good_run k _ L (good_init G hh ho hy) hrun).2.2.1

/-- the first step from [G, x, y, r] is G's opening -/
theorem first_step (G : T) (hh : head G = S) :
    step [G, var 1, var 2, var 3] = some (args G ++ [var 2, app (var 1) (var 2), var 3]) := by
  simp [step, hh]

/-- corollary: never stuck at a b-containing front whose second or third element is proper pure-y -/
theorem ot_no_transfer (G : T) (hh : head G = S) (ho : ordered G) (hy : occ 2 G = 0) (k : Nat)
    (f w v : T) (rest : List T) (hf : occ 0 f ≠ 0)
    (hrun : run k (args G ++ [var 2, app (var 1) (var 2), var 3]) = some (f :: w :: v :: rest)) :
    ¬ ppy v ∧ ¬ ppy w := by
  have h := ot_main G hh ho hy k _ hrun
  constructor
  · intro hv; exact h (Or.inl ⟨hf, v, by simp, hv⟩)
  · intro hw; exact h (Or.inl ⟨hf, w, by simp, hw⟩)

/-! ## Lemma RC (right combs): closed code can only write right combs over its v-input -/

/-- the atoms of t lie among x, y, r -/
def onlyXYR (t : T) : Prop := ∀ n, occ n t ≠ 0 → n = 1 ∨ n = 2 ∨ n = 3

/-- property P: a term with exactly one y and no x, r is y itself or a proper pure-y term -/
def RCP (s : T) : Prop := occ 2 s = 1 → occ 1 s = 0 → occ 3 s = 0 → s = var 2 ∨ ppy s

/-- P holds for every subterm -/
def rcGood : T → Prop
  | app f x => rcGood f ∧ rcGood x ∧ RCP (app f x)
  | t => RCP t

theorem rcGood_self : ∀ t : T, rcGood t → RCP t
  | app _ _, h => h.2.2
  | S, h => h
  | var _, h => h

theorem rcGood_args : ∀ t : T, rcGood t → ∀ s ∈ args t, rcGood s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact rcGood_args f h.1 s hs
    · subst hs; exact h.2.1

theorem onlyXYR_closed (t : T) (h : onlyXYR t) (h1 : occ 1 t = 0) (h2 : occ 2 t = 0) (h3 : occ 3 t = 0) :
    closed t := by
  induction t with
  | S => trivial
  | var m =>
    exfalso
    have := h m (by simp [occ])
    rcases this with rfl | rfl | rfl <;> simp [occ] at h1 h2 h3
  | app f x ihf ihx =>
    have hf : onlyXYR f := fun n hn => h n (by simp [occ]; omega)
    have hx : onlyXYR x := fun n hn => h n (by simp [occ]; omega)
    simp [occ] at h1 h2 h3
    exact ⟨ihf hf (by omega) (by omega) (by omega), ihx hx (by omega) (by omega) (by omega)⟩

theorem onlyXYR_args : ∀ t : T, onlyXYR t → ∀ s ∈ args t, onlyXYR s := by
  intro t ht s hs n hn
  exact ht n (occ_args_le n t s hs hn)

/-- RC invariant on lists: I1, every element only has atoms x, y, r, and every element is rcGood -/
def RCInv (L : List T) : Prop := I1 L ∧ (∀ e ∈ L, ordered e) ∧ (∀ e ∈ L, onlyXYR e) ∧ (∀ e ∈ L, rcGood e)

theorem rc_new (p q : T) (rest : List T) (a : T) (hI : I1 (a :: p :: q :: rest))
    (hp : onlyXYR p) (hq : onlyXYR q) (_hrp : rcGood p) (hrq : rcGood q) : RCP (app p q) := by
  intro h2 h1 h3
  simp [occ] at h2 h1 h3
  -- either y is in p (and not in q) or in q (and not in p)
  by_cases hy : occ 2 q = 0
  · -- y in p: then q has no x, y, r, hence closed; so p closed by I1: contradiction
    exfalso
    have hcq : closed q := onlyXYR_closed q hq (by omega) hy (by omega)
    have hcp : closed p := I1_second_closed a p q rest hI hcq
    have : occ 2 p = 0 := occ_closed 2 p hcp
    omega
  · -- y in q (once), p free of x, y, r: p closed, q is y or proper pure-y
    have hcp : closed p := onlyXYR_closed p hp (by omega) (by omega) (by omega)
    have hrq' := rcGood_self q hrq (by omega) (by omega) (by omega)
    right
    exact ⟨hcp, hrq'⟩

theorem rc_step (L L' : List T) (hG : RCInv L) (hs : step L = some L') : RCInv L' := by
  match L, hs with
  | a :: p :: q :: R, hs =>
    simp only [step] at hs
    split at hs
    · rename_i ha
      injection hs with hs; subst hs
      obtain ⟨hI, hO, hX, hR⟩ := hG
      refine ⟨I1_step a p q R ha hI (hO a (by simp)), I2_step a p q R hI hO, ?_, ?_⟩
      · intro e he
        simp at he
        rcases he with he | he | he | he
        · exact onlyXYR_args a (hX a (by simp)) e he
        · rw [he]; exact hX q (by simp)
        · subst he
          intro n hn
          simp [occ] at hn
          by_cases h' : occ n p = 0
          · exact hX q (by simp) n (by omega)
          · exact hX p (by simp) n h'
        · exact hX e (by simp [he])
      · intro e he
        simp at he
        rcases he with he | he | he | he
        · exact rcGood_args a (hR a (by simp)) e he
        · rw [he]; exact hR q (by simp)
        · subst he
          exact ⟨hR p (by simp), hR q (by simp),
            rc_new p q R a hI (hX p (by simp)) (hX q (by simp)) (hR p (by simp)) (hR q (by simp))⟩
        · exact hR e (by simp [he])
    · exact absurd hs (by simp)

theorem rc_run : ∀ (k : Nat) (L L' : List T), RCInv L → run k L = some L' → RCInv L'
  | 0, L, L', hG, h => by simp [run] at h; subst h; exact hG
  | k + 1, L, L', hG, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      exact rc_run k L1 L' (rc_step L L1 hG hs) h
    · exact absurd h (by simp)

theorem rcGood_closed : ∀ t : T, closed t → rcGood t
  | S, _ => fun h => by simp [occ] at h
  | var _, h => by simp [closed] at h
  | app f x, h => ⟨rcGood_closed f h.1, rcGood_closed x h.2, fun h2 => by
      simp [occ, occ_closed 2 f h.1, occ_closed 2 x h.2] at h2⟩

theorem closed_ordered : ∀ t : T, closed t → ordered t
  | S, _ => trivial
  | var _, h => by simp [closed] at h
  | app f x, h => ⟨fun _ _ => h.1, closed_ordered f h.1, closed_ordered x h.2⟩

/-- **Lemma RC**: for closed code G, every list element reachable from args G ++ [y, x.y, r] and every subterm of
    one with exactly one y and no x, r is y itself or a proper pure-y term d1.(...(dm.y)) with closed d's. -/
theorem rc_main (G : T) (hc : closed G) (k : Nat) (L : List T)
    (hrun : run k (args G ++ [var 2, app (var 1) (var 2), var 3]) = some L) :
    ∀ e ∈ L, rcGood e := by
  have hh : head G = S := closed_head G hc
  have h0 : RCInv (args G ++ [var 2, app (var 1) (var 2), var 3]) := by
    obtain ⟨C, D, hCD, hC, hD⟩ := args_split G (closed_ordered G hc) hh
    refine ⟨⟨C, D ++ [var 2, app (var 1) (var 2), var 3], by simp [hCD], hC, ?_⟩, ?_, ?_, ?_⟩
    · intro d hd; simp at hd
      rcases hd with hd | hd | hd | hd
      · exact hD d hd
      · subst hd; simp [closed]
      · subst hd; simp [closed]
      · subst hd; simp [closed]
    · intro e he; simp at he
      rcases he with he | he | he | he
      · exact closed_ordered e (closed_args G hc e he)
      · subst he; trivial
      · subst he; exact ⟨fun h => by simp [head] at h, trivial, trivial⟩
      · subst he; trivial
    · intro e he n hn; simp at he
      rcases he with he | he | he | he
      · exact absurd (occ_closed n e (closed_args G hc e he)) hn
      · subst he; simp [occ] at hn; omega
      · subst he; simp [occ] at hn
        by_cases h1 : 1 = n
        · omega
        · simp [h1] at hn; omega
      · subst he; simp [occ] at hn; omega
    · intro e he; simp at he
      rcases he with he | he | he | he
      · exact rcGood_closed e (closed_args G hc e he)
      · subst he; intro _ _ _; left; rfl
      · subst he
        refine ⟨fun _ h1 _ => by simp [occ] at h1, fun _ _ _ => Or.inl rfl, fun _ h1 _ => by simp [occ] at h1⟩
      · subst he; intro h2; simp [occ] at h2
  exact (rc_run k _ L h0 hrun).2.2.2
