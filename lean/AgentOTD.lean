/-
  agent_work/lean/OTD.lean  (construction agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.
  Theorem OTD = Theorem OT with FROZEN atoms allowed: `closed` now means "free of the atoms 0..3"
  (p = var 0, x = var 1, y = var 2, r = var 3); atoms var n with n >= 4 are frozen old predecessors, which may occur
  anywhere (in the code and in the wrappers).  A frozen-headed front is stuck (the step needs an S-headed front).
  Also Lemma FH: a datum with a frozen-headed level never produces a p-headed element.
  -- (the remaining comment below is inherited from OT.lean; read 'closed' as 'free of 0..3')

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
  | var n => 4 ≤ n
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

theorem closed_args : ∀ t : T, closed t → ∀ s ∈ args t, closed s
  | S, _ => by simp [args]
  | var _, _ => by simp [args]
  | app f x, h => by
    intro s hs
    simp [args] at hs
    rcases hs with hs | hs
    · exact closed_args f h.1 s hs
    · subst hs; exact h.2

theorem occ_closed (n : Nat) (hn : n < 4) : ∀ t : T, closed t → occ n t = 0
  | S, _ => rfl
  | var m, h => by
    simp [closed] at h
    have : m ≠ n := by omega
    simp [occ, this]
  | app f x, h => by simp [occ, occ_closed n hn f h.1, occ_closed n hn x h.2]

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
    · subst ht; simp [occ, occ_closed 0 (by decide) d hd]
    · simp [occ, occ_closed 0 (by decide) d hd, ppy_noB t ht]
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
        exact hab (occ_closed 0 (by decide) a hca)
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


/-! ## Lemma FH: a frozen-headed level blocks the predecessor -/

/-- t is guarded by the level Lv: every occurrence of p (= var 0) in t lies inside an occurrence of Lv -/
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

theorem guarded_args (Lv : T) (hL : head Lv ≠ S) : ∀ t : T, guarded Lv t → head t = S → ∀ s ∈ args t, guarded Lv s
  | S, _, _, s, hs => by simp [args] at hs
  | var _, _, h, _, _ => by simp [head] at h
  | app f x, h, hh, s, hs => by
    rcases h with h | ⟨hf, hx⟩
    · exact absurd (h ▸ hh) hL
    · simp [args] at hs
      rcases hs with hs | hs
      · exact guarded_args Lv hL f hf (by simpa [head] using hh) s hs
      · subst hs; exact hx

theorem guarded_step (Lv : T) (hL : head Lv ≠ S) (L L' : List T) (hG : ∀ e ∈ L, guarded Lv e)
    (hs : step L = some L') : ∀ e ∈ L', guarded Lv e := by
  match L, hs with
  | a :: b :: c :: R, hs =>
    simp only [step] at hs
    split at hs
    · rename_i ha
      injection hs with hs; subst hs
      intro e he
      simp at he
      rcases he with he | he | he | he
      · exact guarded_args Lv hL a (hG a (by simp)) ha e he
      · rw [he]; exact hG c (by simp)
      · rw [he]; exact Or.inr ⟨hG b (by simp), hG c (by simp)⟩
      · exact hG e (by simp [he])
    · exact absurd hs (by simp)

theorem guarded_run (Lv : T) (hL : head Lv ≠ S) :
    ∀ (k : Nat) (L L' : List T), (∀ e ∈ L, guarded Lv e) → run k L = some L' → ∀ e ∈ L', guarded Lv e
  | 0, L, L', hG, h => by simp [run] at h; subst h; exact hG
  | k + 1, L, L', hG, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      exact guarded_run Lv hL k L1 L' (guarded_step Lv hL L L1 hG hs) h
    · exact absurd h (by simp)

/-- **Lemma FH.** If every element of the initial list is guarded by a level Lv whose head is neither S nor p (e.g. a
    frozen atom var c), then no reachable list ever contains a p-headed element: the predecessor can never be
    activated, so no transfer of any kind happens before the run gets stuck at a frozen-headed front. -/
theorem fh_main (Lv : T) (hS : head Lv ≠ S) (hp : head Lv ≠ var 0) (k : Nat) (L0 L : List T)
    (h0 : ∀ e ∈ L0, guarded Lv e) (hrun : run k L0 = some L) : ∀ e ∈ L, head e ≠ var 0 := by
  intro e he
  exact guarded_head Lv hp e (guarded_run Lv hS k L0 L h0 hrun e he)

/-- right combs: rcomb [d1, ..., dk] base = d1.(d2.(...(dk.base))) -/
def rcomb : List T → T → T
  | [], b => b
  | d :: ds, b => app d (rcomb ds b)

theorem guarded_of_nop (Lv : T) : ∀ t : T, occ 0 t = 0 → guarded Lv t
  | S, _ => trivial
  | var n, h => by
    simp [occ] at h
    simp [guarded]; intro hn; exact h hn
  | app f x, h => by
    simp [occ] at h
    exact Or.inr ⟨guarded_of_nop Lv f h.1, guarded_of_nop Lv x h.2⟩

/-- a right comb over p whose wrappers are p-free and one of whose levels is Lv is guarded by Lv -/
theorem guarded_rcomb (ds1 ds2 : List T) (di : T) (h1 : ∀ d ∈ ds1, occ 0 d = 0) :
    guarded (app di (rcomb ds2 (var 0))) (rcomb ds1 (app di (rcomb ds2 (var 0)))) := by
  induction ds1 with
  | nil => simp [rcomb, guarded]
  | cons d ds ih =>
    simp only [rcomb]
    exact Or.inr ⟨guarded_of_nop _ d (h1 d (by simp)), ih (fun d' hd' => h1 d' (by simp [hd']))⟩

/-- **Corollary.** For D = d1.(...(dk.p)) with p-free wrappers, if some wrapper di is headed by a frozen atom var c
    (c != 0), then along the generic run from [D, x, y, r] no list element is ever p-headed. -/
theorem fh_rcomb (ds1 ds2 : List T) (di : T) (c : Nat) (hc : c ≠ 0) (hdi : head di = var c)
    (h1 : ∀ d ∈ ds1, occ 0 d = 0) (k : Nat) (L : List T)
    (hrun : run k [rcomb ds1 (app di (rcomb ds2 (var 0))), var 1, var 2, var 3] = some L) :
    ∀ e ∈ L, head e ≠ var 0 := by
  have hS : head (app di (rcomb ds2 (var 0))) ≠ S := by simp [head, hdi]
  have hp : head (app di (rcomb ds2 (var 0))) ≠ var 0 := by simp [head, hdi, hc]
  apply fh_main _ hS hp k _ L _ hrun
  intro e he
  simp at he
  rcases he with he | he | he | he
  · rw [he]; exact guarded_rcomb ds1 ds2 di h1
  · rw [he]; simp [guarded]
  · rw [he]; simp [guarded]
  · rw [he]; simp [guarded]

#print axioms ot_main
#print axioms ot_no_transfer
#print axioms fh_main
#print axioms fh_rcomb
