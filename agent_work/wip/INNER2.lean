/-
  agent_work/lean/INNER.lean  (non-universality agent, 2026-10-27).  CANON.lean (copied verbatim) plus the general
  innermost-dirty theorem `ordered_innermost`: from ANY S-headed ordered y-free datum (frozen atoms allowed), at a
  p-containing front, a right comb over y at position 3 whose wrappers are free of x, y, r has a p-containing
  innermost wrapper.  (Ingredients from CANON/OT: good_nb2_run, ot_main's Good invariant, last_has_p.)

  agent_work/lean/CANON.lean  (construction agent, 2026-10-27).  = SL.lean + OTD's OT/FH part + the combined corollary.  Plain Lean 4 core, no Mathlib.
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


/-! ## Theorem SL (single-level data): every P-element glued onto a Y-element is p-headed -/

/-- P: contains p (var 0), no x, y, r -/
def isP (t : T) : Prop := occ 0 t ≠ 0 ∧ occ 1 t = 0 ∧ occ 2 t = 0 ∧ occ 3 t = 0
/-- Y: contains x, y or r -/
def isY (t : T) : Prop := occ 1 t ≠ 0 ∨ occ 2 t ≠ 0 ∨ occ 3 t ≠ 0

theorem closed_iff_atoms (t : T) (h : closed t) : occ 0 t = 0 ∧ occ 1 t = 0 ∧ occ 2 t = 0 ∧ occ 3 t = 0 :=
  ⟨occ_closed 0 (by decide) t h, occ_closed 1 (by decide) t h, occ_closed 2 (by decide) t h,
   occ_closed 3 (by decide) t h⟩

theorem closed_of_zero : ∀ t : T, occ 0 t = 0 → occ 1 t = 0 → occ 2 t = 0 → occ 3 t = 0 → closed t
  | S, _, _, _, _ => trivial
  | var n, h0, h1, h2, h3 => by
    simp [occ] at h0 h1 h2 h3
    simp [closed]; omega
  | app f x, h0, h1, h2, h3 => by
    simp [occ] at h0 h1 h2 h3
    exact ⟨closed_of_zero f (by omega) (by omega) (by omega) (by omega),
           closed_of_zero x (by omega) (by omega) (by omega) (by omega)⟩

/-- every term is exactly one of closed, P, Y -/
theorem trichotomy (t : T) : closed t ∨ isP t ∨ isY t := by
  by_cases h1 : occ 1 t = 0
  · by_cases h2 : occ 2 t = 0
    · by_cases h3 : occ 3 t = 0
      · by_cases h0 : occ 0 t = 0
        · exact Or.inl (closed_of_zero t h0 h1 h2 h3)
        · exact Or.inr (Or.inl ⟨h0, h1, h2, h3⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
  · exact Or.inr (Or.inr (Or.inl h1))

theorem not_closed_P (t : T) (h : isP t) : ¬ closed t := fun hc => h.1 (occ_closed 0 (by decide) t hc)
theorem not_closed_Y (t : T) (h : isY t) : ¬ closed t := by
  intro hc
  rcases h with h | h | h
  · exact h (occ_closed 1 (by decide) t hc)
  · exact h (occ_closed 2 (by decide) t hc)
  · exact h (occ_closed 3 (by decide) t hc)
theorem not_PY (t : T) (hp : isP t) (hy : isY t) : False := by
  rcases hy with h | h | h
  · exact h hp.2.1
  · exact h hp.2.2.1
  · exact h hp.2.2.2

theorem occ_app (n : Nat) (f x : T) : occ n (app f x) = occ n f + occ n x := rfl

/-- args of a P-element have no x, y, r -/
theorem args_noXYR (t : T) (h1 : occ 1 t = 0) (h2 : occ 2 t = 0) (h3 : occ 3 t = 0) :
    ∀ s ∈ args t, occ 1 s = 0 ∧ occ 2 s = 0 ∧ occ 3 s = 0 := by
  intro s hs
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : occ 1 s = 0
    · exact h
    · exact absurd h1 (occ_args_le 1 t s hs h)
  · by_cases h : occ 2 s = 0
    · exact h
    · exact absurd h2 (occ_args_le 2 t s hs h)
  · by_cases h : occ 3 s = 0
    · exact h
    · exact absurd h3 (occ_args_le 3 t s hs h)

/-- hereditary: every S-headed Y-subterm has no P spine argument -/
def hy : T → Prop
  | app f x => hy f ∧ hy x ∧ (isY (app f x) → head f = S → ∀ a ∈ args (app f x), ¬ isP a)
  | _ => True

/-- hereditary: every subterm  w.q  with w in P and q in Y has w p-headed -/
def gl : T → Prop
  | app f x => gl f ∧ gl x ∧ (isP f → isY x → head f = var 0)
  | _ => True

theorem hy_args : ∀ t : T, hy t → ∀ s ∈ args t, hy s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact hy_args f h.1 s hs
    · subst hs; exact h.2.1

theorem gl_args : ∀ t : T, gl t → ∀ s ∈ args t, gl s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact gl_args f h.1 s hs
    · subst hs; exact h.2.1

theorem hy_noXYR : ∀ t : T, occ 1 t = 0 → occ 2 t = 0 → occ 3 t = 0 → hy t
  | S, _, _, _ => trivial
  | var _, _, _, _ => trivial
  | app f x, h1, h2, h3 => by
    simp [occ] at h1 h2 h3
    refine ⟨hy_noXYR f (by omega) (by omega) (by omega), hy_noXYR x (by omega) (by omega) (by omega), ?_⟩
    intro hY; exfalso
    rcases hY with h | h | h <;> simp [occ] at h <;> omega

theorem gl_noXYR : ∀ t : T, occ 1 t = 0 → occ 2 t = 0 → occ 3 t = 0 → gl t
  | S, _, _, _ => trivial
  | var _, _, _, _ => trivial
  | app f x, h1, h2, h3 => by
    simp [occ] at h1 h2 h3
    refine ⟨gl_noXYR f (by omega) (by omega) (by omega), gl_noXYR x (by omega) (by omega) (by omega), ?_⟩
    intro _ hY; exfalso
    rcases hY with h | h | h <;> omega

/-- the single-level invariant -/
def SLI (L : List T) : Prop :=
  (∃ C Pl Yl : List T, L = C ++ Pl ++ Yl ∧ (∀ c ∈ C, closed c) ∧ (∀ e ∈ Pl, isP e) ∧ (∀ e ∈ Yl, isY e) ∧
     (Pl = [] ∨ ∃ e ∈ Pl, head e = var 0) ∧
     (Pl.length = 2 → ∀ e ∈ Pl, head e ≠ var 0 → ∀ s ∈ args e, isP s → head s = var 0)) ∧
  (∀ e ∈ L, ordered e) ∧ (∀ e ∈ L, hy e) ∧ (∀ e ∈ L, gl e)

theorem isP_app (b c : T) (hb : closed b ∨ isP b) (hc : isP c) : isP (app b c) := by
  obtain ⟨c0, c1, c2, c3⟩ := hc
  have hb' : occ 1 b = 0 ∧ occ 2 b = 0 ∧ occ 3 b = 0 := by
    rcases hb with hb | hb
    · obtain ⟨_, h1, h2, h3⟩ := closed_iff_atoms b hb; exact ⟨h1, h2, h3⟩
    · exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2⟩
  obtain ⟨b1, b2, b3⟩ := hb'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [occ_app] <;> omega

theorem isY_app_r (b c : T) (hc : isY c) : isY (app b c) := by
  rcases hc with h | h | h
  · exact Or.inl (by simp [occ_app]; omega)
  · exact Or.inr (Or.inl (by simp [occ_app]; omega))
  · exact Or.inr (Or.inr (by simp [occ_app]; omega))

theorem isY_app_l (b c : T) (hb : isY b) : isY (app b c) := by
  rcases hb with h | h | h
  · exact Or.inl (by simp [occ_app]; omega)
  · exact Or.inr (Or.inl (by simp [occ_app]; omega))
  · exact Or.inr (Or.inr (by simp [occ_app]; omega))

theorem closed_app (b c : T) (hb : closed b) (hc : closed c) : closed (app b c) := ⟨hb, hc⟩

theorem not_isP_closed (t : T) (h : closed t) : ¬ isP t := fun hp => not_closed_P t hp h
theorem not_isP_Y (t : T) (h : isY t) : ¬ isP t := fun hp => not_PY t hp h

/-- the P-arguments of a P-element: its non-closed arguments are P -/
theorem P_args_nonclosed (a : T) (ha : isP a) : ∀ s ∈ args a, ¬ closed s → isP s := by
  intro s hs hnc
  obtain ⟨h1, h2, h3⟩ := args_noXYR a ha.2.1 ha.2.2.1 ha.2.2.2 s hs
  rcases trichotomy s with h | h | h
  · exact absurd h hnc
  · exact h
  · exfalso; rcases h with h | h | h <;> omega

theorem P_has_P_arg (a : T) (ha : isP a) (hS : head a = S) : ∃ s ∈ args a, isP s := by
  -- some argument contains p
  have : ∀ t : T, head t = S → occ 0 t ≠ 0 → ∃ s ∈ args t, occ 0 s ≠ 0 := by
    intro t
    induction t with
    | S => intro _ h; simp [occ] at h
    | var n => intro h; simp [head] at h
    | app f x ihf _ =>
      intro hh h0
      by_cases hx : occ 0 x = 0
      · have hf : occ 0 f ≠ 0 := by simp [occ_app] at h0; omega
        obtain ⟨s, hs, hs0⟩ := ihf (by simpa [head] using hh) hf
        exact ⟨s, by simp [args, hs], hs0⟩
      · exact ⟨x, by simp [args], hx⟩
  obtain ⟨s, hs, hs0⟩ := this a hS ha.1
  obtain ⟨h1, h2, h3⟩ := args_noXYR a ha.2.1 ha.2.2.1 ha.2.2.2 s hs
  exact ⟨s, hs, hs0, h1, h2, h3⟩

theorem sli_step_gen (a b c : T) (R : List T)
    (hO : ∀ e ∈ a :: b :: c :: R, ordered e) (hH : ∀ e ∈ a :: b :: c :: R, hy e)
    (hG : ∀ e ∈ a :: b :: c :: R, gl e)
    (hcb : head b = S → closed c → closed b)
    (hyt : isY (app b c) → head b = S → ∀ x ∈ args (app b c), ¬ isP x)
    (hgt : isP b → isY c → head b = var 0)
    (hseg : ∃ C Pl Yl : List T, args a ++ c :: app b c :: R = C ++ Pl ++ Yl ∧ (∀ x ∈ C, closed x) ∧
      (∀ e ∈ Pl, isP e) ∧ (∀ e ∈ Yl, isY e) ∧ (Pl = [] ∨ ∃ e ∈ Pl, head e = var 0) ∧
      (Pl.length = 2 → ∀ e ∈ Pl, head e ≠ var 0 → ∀ s ∈ args e, isP s → head s = var 0)) :
    SLI (args a ++ c :: app b c :: R) := by
  refine ⟨hseg, ?_, ?_, ?_⟩
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact ordered_args a (hO a (by simp)) e he
    · rw [he]; exact hO c (by simp)
    · rw [he]; exact ⟨hcb, hO b (by simp), hO c (by simp)⟩
    · exact hO e (by simp [he])
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact hy_args a (hH a (by simp)) e he
    · rw [he]; exact hH c (by simp)
    · rw [he]; exact ⟨hH b (by simp), hH c (by simp), hyt⟩
    · exact hH e (by simp [he])
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact gl_args a (hG a (by simp)) e he
    · rw [he]; exact hG c (by simp)
    · rw [he]; exact ⟨hG b (by simp), hG c (by simp), hgt⟩
    · exact hG e (by simp [he])

theorem args_app_mem (b c x : T) (h : x ∈ args (app b c)) : x ∈ args b ∨ x = c := by
  simp [args] at h; exact h

theorem hy_top : ∀ t : T, hy t → isY t → head t = S → ∀ a ∈ args t, ¬ isP a
  | S, _, _, _, a, ha => by simp [args] at ha
  | var _, _, _, h, _, _ => by simp [head] at h
  | app f x, h, hY, hS, a, ha => h.2.2 hY (by simpa [head] using hS) a ha

theorem Y_args_split (a : T) (hY : isY a) (hS : head a = S) (ho : ordered a) (hh : hy a) :
    ∃ C0 D0 : List T, args a = C0 ++ D0 ∧ (∀ x ∈ C0, closed x) ∧ (∀ x ∈ D0, isY x) := by
  obtain ⟨C0, D0, hs, hC, hD⟩ := args_split a ho hS
  refine ⟨C0, D0, hs, hC, ?_⟩
  intro x hx
  have hxa : x ∈ args a := by rw [hs]; simp [hx]
  rcases trichotomy x with h | h | h
  · exact absurd h (hD x hx)
  · exact absurd h (hy_top a hh hY hS x hxa)
  · exact h

theorem P_args_split (a : T) (hP : isP a) (hS : head a = S) (ho : ordered a) :
    ∃ C0 D0 : List T, args a = C0 ++ D0 ∧ (∀ x ∈ C0, closed x) ∧ (∀ x ∈ D0, isP x) ∧ D0 ≠ [] := by
  obtain ⟨C0, D0, hs, hC, hD⟩ := args_split a ho hS
  refine ⟨C0, D0, hs, hC, fun x hx => P_args_nonclosed a hP x (by rw [hs]; simp [hx]) (hD x hx), ?_⟩
  obtain ⟨s, hs', hsP⟩ := P_has_P_arg a hP hS
  intro h0; rw [hs, h0] at hs'
  simp at hs'
  exact not_closed_P s hsP (hC s hs')

theorem head_app (b c : T) : head (app b c) = head b := rfl


theorem sli_step (a b c : T) (R : List T) (ha : head a = S) (hI : SLI (a :: b :: c :: R)) :
    SLI (args a ++ c :: app b c :: R) := by
  obtain ⟨⟨C, Pl, Yl, hL, hC, hP, hY, hQ, hT⟩, hO, hH, hG⟩ := hI
  match C, Pl, hL, hC, hP, hQ, hT with
  -- Case A: a, b, c closed
  | c1 :: c2 :: c3 :: C', Pl, hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb' : closed b := hC b (by simp)
    have hcc : closed c := hC c (by simp)
    apply sli_step_gen a b c R hO hH hG (fun _ _ => hcb')
    · intro hYbc; exact absurd (closed_app b c hcb' hcc) (not_closed_Y _ hYbc)
    · intro hPb; exact absurd hcb' (not_closed_P b hPb)
    · refine ⟨args a ++ c :: app b c :: C', Pl, Yl, by simp [hR], ?_, hP, hY, hQ, hT⟩
      intro x hx; simp at hx
      rcases hx with hx | hx | hx | hx
      · exact closed_args a hca x hx
      · rw [hx]; exact hcc
      · rw [hx]; exact closed_app b c hcb' hcc
      · exact hC x (by simp [hx])
  -- Case B2: a, b closed, c the top of Y (P empty)
  | [c1, c2], [], hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb' : closed b := hC b (by simp)
    have hYc : isY c := hY c (by rw [← hR]; simp)
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
    · intro _ _ x hx
      rcases args_app_mem b c x hx with hx | hx
      · exact not_isP_closed x (closed_args b hcb' x hx)
      · rw [hx]; exact not_isP_Y c hYc
    · intro hPb; exact absurd hcb' (not_closed_P b hPb)
    · refine ⟨args a, [], c :: app b c :: R, by simp, closed_args a hca, by simp, ?_, Or.inl rfl, by simp⟩
      intro e he; simp at he
      rcases he with he | he | he
      · rw [he]; exact hYc
      · rw [he]; exact isY_app_r b c hYc
      · exact hY e (by rw [← hR]; simp [he])
  -- Case B1: a, b closed, c the top of P
  | [c1, c2], e :: Pl', hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb' : closed b := hC b (by simp)
    have hPc : isP c := hP c (by simp)
    have hPbc : isP (app b c) := isP_app b c (Or.inl hcb') hPc
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_P c hPc))
    · intro hYbc; exact absurd hYbc (fun h => not_PY _ hPbc h)
    · intro hPb; exact absurd hcb' (not_closed_P b hPb)
    · refine ⟨args a, c :: app b c :: Pl', Yl, by simp [hR], closed_args a hca, ?_, hY, ?_, ?_⟩
      · intro e he; simp at he
        rcases he with he | he | he
        · rw [he]; exact hPc
        · rw [he]; exact hPbc
        · exact hP e (by simp [he])
      · right
        rcases hQ with hQ | ⟨e', he', hh⟩
        · simp at hQ
        · simp at he'
          rcases he' with he' | he'
          · exact ⟨c, by simp, he' ▸ hh⟩
          · exact ⟨e', by simp [he'], hh⟩
      · intro hlen
        have hPl' : Pl' = [] := by simpa using hlen
        subst hPl'
        have hcp : head c = var 0 := by
          rcases hQ with hQ | ⟨e', he', hh⟩
          · simp at hQ
          · simp at he'; exact he' ▸ hh
        intro e he hne s hs hsP
        simp at he
        rcases he with he | he
        · exact absurd (he ▸ hcp) hne
        · rw [he] at hs
          rcases args_app_mem b c s hs with hs | hs
          · exact absurd hsP (not_isP_closed s (closed_args b hcb' s hs))
          · rw [hs]; exact hcp
  -- Case C3: a closed, b, c in Y
  | [c1], [], hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hYb : isY b := hY b (by rw [← hR]; simp)
    have hYc : isY c := hY c (by rw [← hR]; simp)
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
    · intro _ hbS x hx
      rcases args_app_mem b c x hx with hx | hx
      · exact hy_top b (hH b (by simp)) hYb hbS x hx
      · rw [hx]; exact not_isP_Y c hYc
    · intro hPb; exact absurd hYb (fun h => not_PY b hPb h)
    · refine ⟨args a, [], c :: app b c :: R, by simp, closed_args a hca, by simp, ?_, Or.inl rfl, by simp⟩
      intro e he; simp at he
      rcases he with he | he | he
      · rw [he]; exact hYc
      · rw [he]; exact isY_app_l b c hYb
      · exact hY e (by rw [← hR]; simp [he])
  -- Case C2: a closed, P = [b], c the top of Y: the step lemma case
  | [c1], [e], hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hbp : head b = var 0 := by
      rcases hQ with hQ | ⟨e', he', hh⟩
      · simp at hQ
      · simp at he'; exact he' ▸ hh
    have hYc : isY c := hY c (by rw [← hR]; simp)
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
    · intro _ hbS; rw [hbp] at hbS; simp at hbS
    · intro _ _; exact hbp
    · refine ⟨args a, [], c :: app b c :: R, by simp, closed_args a hca, by simp, ?_, Or.inl rfl, by simp⟩
      intro e he; simp at he
      rcases he with he | he | he
      · rw [he]; exact hYc
      · rw [he]; exact isY_app_r b c hYc
      · exact hY e (by rw [← hR]; simp [he])
  -- Case C1: a closed, b, c in P
  | [c1], e1 :: e2 :: Pl', hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hPb : isP b := hP b (by simp)
    have hPc : isP c := hP c (by simp)
    have hPbc : isP (app b c) := isP_app b c (Or.inr hPb) hPc
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_P c hPc))
    · intro hYbc; exact absurd hYbc (fun h => not_PY _ hPbc h)
    · intro _ hYc; exact absurd hYc (fun h => not_PY c hPc h)
    · refine ⟨args a, c :: app b c :: Pl', Yl, by simp [hR], closed_args a hca, ?_, hY, ?_, ?_⟩
      · intro e he; simp at he
        rcases he with he | he | he
        · rw [he]; exact hPc
        · rw [he]; exact hPbc
        · exact hP e (by simp [he])
      · right
        rcases hQ with hQ | ⟨e', he', hh⟩
        · simp at hQ
        · simp at he'
          rcases he' with he' | he' | he'
          · exact ⟨app b c, by simp, by rw [head_app, ← he']; exact hh⟩
          · exact ⟨c, by simp, he' ▸ hh⟩
          · exact ⟨e', by simp [he'], hh⟩
      · intro hlen
        have hPl' : Pl' = [] := by simpa using hlen
        subst hPl'
        have hT' := hT (by simp)
        intro e he hne s hs hsP
        simp at he
        rcases he with he | he
        · rw [he] at hne hs; exact hT' c (by simp) hne s hs hsP
        · rw [he] at hne hs
          rw [head_app] at hne
          rcases args_app_mem b c s hs with hs | hs
          · exact hT' b (by simp) hne s hs hsP
          · rw [hs]
            rcases hQ with hQ | ⟨e', he', hh⟩
            · simp at hQ
            · simp at he'
              rcases he' with he' | he'
              · exact absurd (he' ▸ hh) hne
              · exact he' ▸ hh
  -- Case D4: a, b, c in Y (C and P empty)
  | [], [], hL, hC, hP, hQ, hT =>
    simp at hL
    have hYa : isY a := hY a (by rw [← hL]; simp)
    have hYb : isY b := hY b (by rw [← hL]; simp)
    have hYc : isY c := hY c (by rw [← hL]; simp)
    obtain ⟨C0, D0, hs, hC0, hD0⟩ := Y_args_split a hYa ha (hO a (by simp)) (hH a (by simp))
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
    · intro _ hbS x hx
      rcases args_app_mem b c x hx with hx | hx
      · exact hy_top b (hH b (by simp)) hYb hbS x hx
      · rw [hx]; exact not_isP_Y c hYc
    · intro hPb; exact absurd hYb (fun h => not_PY b hPb h)
    · refine ⟨C0, [], D0 ++ c :: app b c :: R, by simp [hs], hC0, by simp, ?_, Or.inl rfl, by simp⟩
      intro e he; simp at he
      rcases he with he | he | he | he
      · exact hD0 e he
      · rw [he]; exact hYc
      · rw [he]; exact isY_app_l b c hYb
      · exact hY e (by rw [← hL]; simp [he])
  -- Case D3: P = [a] with a S-headed: impossible
  | [], [e], hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    exfalso
    rcases hQ with hQ | ⟨e', he', hh⟩
    · simp at hQ
    · simp at he'; rw [he', ha] at hh; simp at hh
  -- Case D2: P = [a, b], c the top of Y
  | [], [e1, e2], hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, hR⟩ := hL
    have hPa : isP a := hP a (by simp)
    have hbp : head b = var 0 := by
      rcases hQ with hQ | ⟨e', he', hh⟩
      · simp at hQ
      · simp at he'
        rcases he' with he' | he'
        · rw [he', ha] at hh; simp at hh
        · exact he' ▸ hh
    have hTa : ∀ s ∈ args a, isP s → head s = var 0 :=
      hT (by simp) a (by simp) (by rw [ha]; simp)
    have hYc : isY c := hY c (by rw [← hR]; simp)
    obtain ⟨C0, D0, hs, hC0, hD0, hne⟩ := P_args_split a hPa ha (hO a (by simp))
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
    · intro _ hbS; rw [hbp] at hbS; simp at hbS
    · intro _ _; exact hbp
    · refine ⟨C0, D0, c :: app b c :: R, by simp [hs], hC0, hD0, ?_, ?_, ?_⟩
      · intro e he; simp at he
        rcases he with he | he | he
        · rw [he]; exact hYc
        · rw [he]; exact isY_app_r b c hYc
        · exact hY e (by rw [← hR]; simp [he])
      · right
        match D0, hne with
        | d :: D0', _ =>
          exact ⟨d, by simp, hTa d (by rw [hs]; simp) (hD0 d (by simp))⟩
      · intro _ e he hne'
        exact absurd (hTa e (by rw [hs]; simp [he]) (hD0 e he)) hne'
  -- Case D1: a, b, c in P (at least three P-elements)
  | [], e1 :: e2 :: e3 :: Pl', hL, hC, hP, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hPa : isP a := hP a (by simp)
    have hPb : isP b := hP b (by simp)
    have hPc : isP c := hP c (by simp)
    have hPbc : isP (app b c) := isP_app b c (Or.inr hPb) hPc
    obtain ⟨C0, D0, hs, hC0, hD0, hne⟩ := P_args_split a hPa ha (hO a (by simp))
    apply sli_step_gen a b c R hO hH hG (fun _ hcc => absurd hcc (not_closed_P c hPc))
    · intro hYbc; exact absurd hYbc (fun h => not_PY _ hPbc h)
    · intro _ hYc; exact absurd hYc (fun h => not_PY c hPc h)
    · refine ⟨C0, D0 ++ c :: app b c :: Pl', Yl, by simp [hs, hR], hC0, ?_, hY, ?_, ?_⟩
      · intro e he; simp at he
        rcases he with he | he | he | he
        · exact hD0 e he
        · rw [he]; exact hPc
        · rw [he]; exact hPbc
        · exact hP e (by simp [he])
      · right
        rcases hQ with hQ | ⟨e', he', hh⟩
        · simp at hQ
        · simp at he'
          rcases he' with he' | he' | he' | he'
          · rw [he', ha] at hh; simp at hh
          · exact ⟨app b c, by simp, by rw [head_app, ← he']; exact hh⟩
          · exact ⟨c, by simp, he' ▸ hh⟩
          · exact ⟨e', by simp [he'], hh⟩
      · intro hlen
        exfalso
        match D0, hne with
        | d :: D0', _ => simp at hlen; omega

theorem sli_step' (L L' : List T) (hI : SLI L) (hs : step L = some L') : SLI L' := by
  match L, hs with
  | a :: b :: c :: R, hs =>
    simp only [step] at hs
    split at hs
    · rename_i ha
      injection hs with hs; subst hs
      exact sli_step a b c R ha hI
    · exact absurd hs (by simp)

theorem sli_run : ∀ (k : Nat) (L L' : List T), SLI L → run k L = some L' → SLI L'
  | 0, L, L', hI, h => by simp [run] at h; subst h; exact hI
  | k + 1, L, L', hI, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      exact sli_run k L1 L' (sli_step' L L1 hI hs) h
    · exact absurd h (by simp)

theorem closed_ordered' : ∀ t : T, closed t → ordered t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => ⟨fun _ _ => h.1, closed_ordered' f h.1, closed_ordered' x h.2⟩

theorem sli_init (K : T) (hK : closed K) (_hS : head K = S) :
    SLI (args K ++ [var 0, var 2, app (var 1) (var 2), var 3]) := by
  have hargs := closed_args K hK
  refine ⟨⟨args K, [var 0], [var 2, app (var 1) (var 2), var 3], by simp, hargs, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e he; simp at he; subst he
    exact ⟨by simp [occ], by simp [occ], by simp [occ], by simp [occ]⟩
  · intro e he; simp at he
    rcases he with he | he | he
    · subst he; exact Or.inr (Or.inl (by simp [occ]))
    · subst he; exact Or.inr (Or.inl (by simp [occ]))
    · subst he; exact Or.inr (Or.inr (by simp [occ]))
  · exact Or.inr ⟨var 0, by simp, rfl⟩
  · intro h; simp at h
  · intro e he; simp at he
    rcases he with he | he | he | he | he
    · exact closed_ordered' e (hargs e he)
    · subst he; trivial
    · subst he; trivial
    · subst he; exact ⟨fun h => by simp [head] at h, trivial, trivial⟩
    · subst he; trivial
  · intro e he; simp at he
    rcases he with he | he | he | he | he
    · obtain ⟨_, h1, h2, h3⟩ := closed_iff_atoms e (hargs e he); exact hy_noXYR e h1 h2 h3
    · subst he; trivial
    · subst he; trivial
    · subst he; exact ⟨trivial, trivial, fun _ h => by simp [head] at h⟩
    · subst he; trivial
  · intro e he; simp at he
    rcases he with he | he | he | he | he
    · obtain ⟨_, h1, h2, h3⟩ := closed_iff_atoms e (hargs e he); exact gl_noXYR e h1 h2 h3
    · subst he; trivial
    · subst he; trivial
    · subst he; exact ⟨trivial, trivial, fun h _ => by simp [isP, occ] at h⟩
    · subst he; trivial

/-- **Theorem SL.** For a single-level datum K.p (K free of p, x, y, r; frozen atoms allowed), along the generic run
    every subterm  w.q  of every list element with w in P (contains p, no x, y, r) and q in Y (contains x, y or r)
    has w p-headed.  In particular the wrapper applied directly to y in any transfer is p-headed. -/
theorem sl_main (K : T) (hK : closed K) (hS : head K = S) (k : Nat) (L : List T)
    (hrun : run k (args K ++ [var 0, var 2, app (var 1) (var 2), var 3]) = some L) : ∀ e ∈ L, gl e :=
  (sli_run k _ L (sli_init K hK hS) hrun).2.2.2

/-- the step lemma: a step that glues a P-element onto a Y-element glues a p-headed one -/
theorem sl_step_lemma (K : T) (hK : closed K) (hS : head K = S) (k : Nat) (a b c : T) (R : List T)
    (hrun : run k (args K ++ [var 0, var 2, app (var 1) (var 2), var 3]) = some (a :: b :: c :: R))
    (ha : head a = S) (hb : isP b) (hc : isY c) : head b = var 0 := by
  have hI := sli_run k _ _ (sli_init K hK hS) hrun
  have hI' := sli_step a b c R ha hI
  have hgl := hI'.2.2.2 (app b c) (by simp)
  exact hgl.2.2 hb hc


/-! ===== OTD part (copied from OTD.lean) ===== -/

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


/-! ===== The combined corollary: canonical Church chains ===== -/

/-- hereditary: no subterm w.U with U proper pure-y and w containing p -/
def nb2 : T → Prop
  | app f x => nb2 f ∧ nb2 x ∧ (ppy x → occ 0 f = 0)
  | _ => True

theorem nb2_args : ∀ t : T, nb2 t → ∀ s ∈ args t, nb2 s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact nb2_args f h.1 s hs
    · subst hs; exact h.2.1

theorem nb2_noY : ∀ t : T, occ 2 t = 0 → nb2 t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    simp [occ] at h
    exact ⟨nb2_noY f h.1, nb2_noY x h.2, fun hp => absurd (ppy_hasY x hp) (by omega)⟩

/-- Good (OT invariant) together with nb2 is preserved -/
theorem good_nb2_step (L L' : List T) (hG : Good L) (hN : ∀ e ∈ L, nb2 e) (hs : step L = some L') :
    ∀ e ∈ L', nb2 e := by
  match L, hs with
  | a :: b :: c :: R, hs =>
    simp only [step] at hs
    split at hs
    · injection hs with hs; subst hs
      intro e he; simp at he
      rcases he with he | he | he | he
      · exact nb2_args a (hN a (by simp)) e he
      · rw [he]; exact hN c (by simp)
      · rw [he]
        refine ⟨hN b (by simp), hN c (by simp), ?_⟩
        intro hpc
        by_cases h0 : occ 0 b = 0
        · exact h0
        · exfalso
          exact hG.2.2.1 (Or.inr (Or.inl ⟨h0, c, by simp, hpc⟩))
      · exact hN e (by simp [he])
    · exact absurd hs (by simp)

theorem good_nb2_run : ∀ (k : Nat) (L L' : List T), Good L → (∀ e ∈ L, nb2 e) → run k L = some L' →
    Good L' ∧ ∀ e ∈ L', nb2 e
  | 0, L, L', hG, hN, h => by simp [run] at h; subst h; exact ⟨hG, hN⟩
  | k + 1, L, L', hG, hN, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      exact good_nb2_run k L1 L' (good_step L L1 hG hs) (good_nb2_step L L1 hG hN hs) h
    · exact absurd h (by simp)

/-- right combs over y -/
def rcy : List T → T
  | [] => var 2
  | d :: ds => app d (rcy ds)

theorem rcy_ppy : ∀ ds : List T, ds ≠ [] → (∀ d ∈ ds, closed d) → ppy (rcy ds)
  | [], h, _ => absurd rfl h
  | [d], _, hc => ⟨hc d (by simp), Or.inl rfl⟩
  | d :: d' :: ds, _, hc => ⟨hc d (by simp), Or.inr (rcy_ppy (d' :: ds) (by simp) (fun x hx => hc x (by simp [hx])))⟩

theorem last_has_p : ∀ ds : List T, (hne : ds ≠ []) →
    (∀ d ∈ ds, occ 1 d = 0 ∧ occ 2 d = 0 ∧ occ 3 d = 0) → nb2 (rcy ds) → (∃ d ∈ ds, occ 0 d ≠ 0) →
    occ 0 (ds.getLast hne) ≠ 0
  | [], hne, _, _, _ => absurd rfl hne
  | [d], _, _, _, ⟨d', hd', h⟩ => by simp at hd'; subst hd'; simpa using h
  | d :: d' :: ds, _, hx, hn, ⟨e, he, h⟩ => by
    have hrest : (d' :: ds).getLast (by simp) = (d :: d' :: ds).getLast (by simp) := by
      simp [List.getLast_cons]
    rw [← hrest]
    have hn' : nb2 (rcy (d' :: ds)) := hn.2.1
    by_cases hex : ∃ e' ∈ d' :: ds, occ 0 e' ≠ 0
    · exact last_has_p (d' :: ds) (by simp) (fun x hx' => hx x (by simp [hx'])) hn' hex
    · exfalso
      have hall : ∀ x ∈ d' :: ds, closed x := by
        intro x hxm
        have h0 : occ 0 x = 0 := by
          by_cases h0 : occ 0 x = 0
          · exact h0
          · exact absurd ⟨x, hxm, h0⟩ hex
        obtain ⟨h1, h2, h3⟩ := hx x (by simp [hxm])
        exact closed_of_zero x h0 h1 h2 h3
      have hp : ppy (rcy (d' :: ds)) := rcy_ppy (d' :: ds) (by simp) hall
      have hd0 : occ 0 d = 0 := hn.2.2 hp
      simp at he
      rcases he with he | he
      · rw [he] at h; exact h hd0
      · exact hex ⟨e, by simp [he], h⟩

theorem gl_last : ∀ ds : List T, (hne : ds ≠ []) → gl (rcy ds) → isP (ds.getLast hne) →
    head (ds.getLast hne) = var 0
  | [], hne, _, _ => absurd rfl hne
  | [d], _, hg, hp => by
    simp at hp ⊢
    exact hg.2.2 hp (Or.inr (Or.inl (by simp [rcy, occ])))
  | d :: d' :: ds, _, hg, hp => by
    have hrest : (d' :: ds).getLast (by simp) = (d :: d' :: ds).getLast (by simp) := by
      simp [List.getLast_cons]
    rw [← hrest] at hp ⊢
    exact gl_last (d' :: ds) (by simp) hg.2.1 hp

theorem args_Kp (K : T) : args (app K (var 0)) = args K ++ [var 0] := by simp [args]

/-- **Corollary (canonical Church chains), machine-checked.**  For a single-level datum K.p (K free of p, x, y, r;
    frozen atoms allowed): whenever the generic run reaches a list  f :: w :: V :: rest  with f containing p and
    V = d1.(d2.(...(dm.y))) (m >= 1, all d_i free of x, y, r), the innermost wrapper dm is p-headed.  (Then, with p
    frozen to c, the next datum V[y := p', p := c] has the c-headed level dm[p := c], and `fh_rcomb` shows that its
    run never produces a p'-headed element.) -/
theorem canonical_innermost (K : T) (hK : closed K) (hS : head K = S) (k : Nat) (f w : T) (ds rest : List T)
    (hne : ds ≠ []) (hds : ∀ d ∈ ds, occ 1 d = 0 ∧ occ 2 d = 0 ∧ occ 3 d = 0)
    (hrun : run k (args K ++ [var 0, var 2, app (var 1) (var 2), var 3]) = some (f :: w :: rcy ds :: rest))
    (hf : occ 0 f ≠ 0) :
    head (ds.getLast hne) = var 0 := by
  -- OT side
  have hGinit : Good (args (app K (var 0)) ++ [var 2, app (var 1) (var 2), var 3]) :=
    good_init (app K (var 0)) (by simp [head, hS])
      ⟨fun _ h => by simp [closed] at h, closed_ordered' K hK, trivial⟩
      (by simp [occ, occ_closed 2 (by decide) K hK])
  rw [args_Kp, List.append_assoc] at hGinit
  have hNinit : ∀ e ∈ args K ++ [var 0] ++ [var 2, app (var 1) (var 2), var 3], nb2 e := by
    intro e he; simp at he
    rcases he with he | he | he | he | he
    · exact nb2_noY e (occ_closed 2 (by decide) e (closed_args K hK e he))
    · rw [he]; trivial
    · rw [he]; trivial
    · rw [he]; exact ⟨trivial, trivial, fun h => by simp [ppy] at h⟩
    · rw [he]; trivial
  simp only [List.append_assoc, List.singleton_append] at hNinit
  obtain ⟨hG, hN⟩ := good_nb2_run k _ _ hGinit hNinit hrun
  -- V is not proper pure-y with closed wrappers (f contains p and lies above it)
  have hex : ∃ d ∈ ds, occ 0 d ≠ 0 := by
    by_cases hex : ∃ d ∈ ds, occ 0 d ≠ 0
    · exact hex
    · exfalso
      have hall : ∀ d ∈ ds, closed d := by
        intro d hd
        have h0 : occ 0 d = 0 := by
          by_cases h0 : occ 0 d = 0
          · exact h0
          · exact absurd ⟨d, hd, h0⟩ hex
        obtain ⟨h1, h2, h3⟩ := hds d hd
        exact closed_of_zero d h0 h1 h2 h3
      exact hG.2.2.1 (Or.inl ⟨hf, rcy ds, by simp, rcy_ppy ds hne hall⟩)
  have hV : rcy ds ∈ f :: w :: rcy ds :: rest := by simp
  have hlast := last_has_p ds hne hds (hN (rcy ds) hV) hex
  obtain ⟨h1, h2, h3⟩ := hds (ds.getLast hne) (List.getLast_mem hne)
  -- SL side
  have hgl := sl_main K hK hS k _ hrun (rcy ds) hV
  exact gl_last ds hne hgl ⟨hlast, h1, h2, h3⟩

/-- **Innermost-dirty theorem for ORDERED data (general).**  For any S-headed ordered y-free datum G (frozen atoms
    allowed), whenever the generic run of [G, x, y, r] reaches a list f :: w :: V :: rest with f containing p and
    V = d1.(d2.(...(dm.y))) (m >= 1, all d_i free of x, y, r), the innermost wrapper dm contains p.  So every proper
    transfer (at position 3) from an ordered datum is innermost-dirty. -/
theorem ordered_innermost (G : T) (hh : head G = S) (ho : ordered G) (hy : occ 2 G = 0) (k : Nat) (f w : T)
    (ds rest : List T) (hne : ds ≠ []) (hds : ∀ d ∈ ds, occ 1 d = 0 ∧ occ 2 d = 0 ∧ occ 3 d = 0)
    (hrun : run k (args G ++ [var 2, app (var 1) (var 2), var 3]) = some (f :: w :: rcy ds :: rest))
    (hf : occ 0 f ≠ 0) : occ 0 (ds.getLast hne) ≠ 0 := by
  have hGinit := good_init G hh ho hy
  have hNinit : ∀ e ∈ args G ++ [var 2, app (var 1) (var 2), var 3], nb2 e := by
    intro e he; simp at he
    rcases he with he | he | he | he
    · apply nb2_noY e
      by_cases h2 : occ 2 e = 0
      · exact h2
      · exact absurd hy (occ_args_le 2 G e he h2)
    · rw [he]; trivial
    · rw [he]; exact ⟨trivial, trivial, fun h => by simp [ppy] at h⟩
    · rw [he]; trivial
  obtain ⟨hG, hN⟩ := good_nb2_run k _ _ hGinit hNinit hrun
  have hex : ∃ d ∈ ds, occ 0 d ≠ 0 := by
    by_cases hex : ∃ d ∈ ds, occ 0 d ≠ 0
    · exact hex
    · exfalso
      have hall : ∀ d ∈ ds, closed d := by
        intro d hd
        have h0 : occ 0 d = 0 := by
          by_cases h0 : occ 0 d = 0
          · exact h0
          · exact absurd ⟨d, hd, h0⟩ hex
        obtain ⟨h1, h2, h3⟩ := hds d hd
        exact closed_of_zero d h0 h1 h2 h3
      exact hG.2.2.1 (Or.inl ⟨hf, rcy ds, by simp, rcy_ppy ds hne hall⟩)
  have hV : rcy ds ∈ f :: w :: rcy ds :: rest := by simp
  exact last_has_p ds hne hds (hN (rcy ds) hV) hex


/-! ### Every datum after the first transfer is an ordered right comb, so all later transfers are innermost-dirty -/

/-- freeze the predecessor: var 0 -> var c -/
def sbc (c : Nat) : T → T
  | S => S
  | var n => if n = 0 then var c else var n
  | app f x => app (sbc c f) (sbc c x)

theorem sbc_closed (c : Nat) (hc : 4 ≤ c) : ∀ t : T, occ 1 t = 0 → occ 2 t = 0 → occ 3 t = 0 → closed (sbc c t)
  | S, _, _, _ => by simp [sbc, closed]
  | var n, h1, h2, h3 => by
    by_cases h0 : n = 0
    · subst h0; simp [sbc, closed]; omega
    · simp [sbc, h0, closed]
      simp [occ] at h1 h2 h3
      omega
  | app f x, h1, h2, h3 => by
    simp only [occ] at h1 h2 h3
    exact ⟨sbc_closed c hc f (by omega) (by omega) (by omega), sbc_closed c hc x (by omega) (by omega) (by omega)⟩

theorem rcomb_not_closed : ∀ (ds : List T) (b : T), ¬ closed b → ¬ closed (rcomb ds b)
  | [], b, hb => by simpa [rcomb] using hb
  | d :: ds, b, hb => by
    simp only [rcomb, closed]
    intro h; exact rcomb_not_closed ds b hb h.2

theorem rcomb_ordered : ∀ (ds : List T) (b : T), (∀ d ∈ ds, closed d) → ordered b → ¬ closed b →
    ordered (rcomb ds b)
  | [], b, _, hb, _ => by simpa [rcomb] using hb
  | d :: ds, b, hds, hb, hnc => by
    simp only [rcomb]
    refine ⟨fun _ hX => absurd hX (rcomb_not_closed ds b hnc), closed_ordered' d (hds d (by simp)),
      rcomb_ordered ds b (fun x hx => hds x (by simp [hx])) hb hnc⟩

theorem rcomb_occ2 : ∀ (ds : List T) (b : T), (∀ d ∈ ds, closed d) → occ 2 b = 0 → occ 2 (rcomb ds b) = 0
  | [], b, _, hb => by simpa [rcomb] using hb
  | d :: ds, b, hds, hb => by
    simp only [rcomb, occ]
    rw [occ_closed 2 (by decide) d (hds d (by simp)), rcomb_occ2 ds b (fun x hx => hds x (by simp [hx])) hb]

theorem rcomb_head (d : T) (ds : List T) (b : T) : head (rcomb (d :: ds) b) = head d := by
  simp [rcomb, head]

/-- **Chain step.**  If a proper transfer hands over V = d1.(...(dm.y)) (wrappers free of x, y, r), the next datum
    V[y := p', p := c] = rcomb (ds.map (sbc c)) p' (c >= 4 a fresh frozen atom) is an ordered y-free right comb; so
    whenever its first wrapper is S-headed, `ordered_innermost` applies to it: every proper transfer of the next
    phase is innermost-dirty. -/
theorem chain_step_innermost (ds : List T) (c : Nat) (hc : 4 ≤ c)
    (hds : ∀ d ∈ ds, occ 1 d = 0 ∧ occ 2 d = 0 ∧ occ 3 d = 0) (d0 : T) (ds0 : List T)
    (hcons : ds.map (sbc c) = d0 :: ds0) (hS : head d0 = S)
    (k : Nat) (f w : T) (es rest : List T) (hne : es ≠ []) (hes : ∀ e ∈ es, occ 1 e = 0 ∧ occ 2 e = 0 ∧ occ 3 e = 0)
    (hrun : run k (args (rcomb (ds.map (sbc c)) (var 0)) ++ [var 2, app (var 1) (var 2), var 3]) =
      some (f :: w :: rcy es :: rest))
    (hf : occ 0 f ≠ 0) : occ 0 (es.getLast hne) ≠ 0 := by
  have hcl : ∀ d ∈ ds.map (sbc c), closed d := by
    intro d hd
    simp at hd
    obtain ⟨d', hd', rfl⟩ := hd
    obtain ⟨h1, h2, h3⟩ := hds d' hd'
    exact sbc_closed c hc d' h1 h2 h3
  have hnc0 : ¬ closed (var 0) := by simp [closed]
  have ho : ordered (rcomb (ds.map (sbc c)) (var 0)) := rcomb_ordered _ _ hcl trivial hnc0
  have hy : occ 2 (rcomb (ds.map (sbc c)) (var 0)) = 0 := rcomb_occ2 _ _ hcl (by simp [occ])
  have hh : head (rcomb (ds.map (sbc c)) (var 0)) = S := by rw [hcons, rcomb_head]; exact hS
  exact ordered_innermost _ hh ho hy k f w es rest hne hes hrun hf

#print axioms canonical_innermost
#print axioms ordered_innermost
#print axioms chain_step_innermost
