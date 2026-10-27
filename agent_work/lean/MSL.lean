/-
  agent_work/lean/MSL.lean  (non-universality agent, 2026-10-27).  Theorem MSL (multi-level data: every P-element
  glued onto a Y-element is level-prefixed or has only level-prefixed P-arguments), on top of AB.lean (Lemma AB,
  absorbing P-count), which is copied verbatim above the MSL section.  Plain Lean 4 core, no Mathlib.
  Main results at the end: `msl_glue` (step form), `msl_main` (hereditary form), `msl_first_step`.
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

/-! ## Lemma AB: once the P-region has at least three elements it keeps at least three, and no P-element is glued
    onto a Y-element any more. -/

/-- segment invariant with a large P-region -/
def SegBig (L : List T) : Prop :=
  (∃ C Pl Yl : List T, L = C ++ Pl ++ Yl ∧ (∀ c ∈ C, closed c) ∧ (∀ e ∈ Pl, isP e) ∧ (∀ e ∈ Yl, isY e) ∧
     3 ≤ Pl.length) ∧ (∀ e ∈ L, ordered e)

theorem ab_step (a b c : T) (R : List T) (ha : head a = S) (hI : SegBig (a :: b :: c :: R)) :
    SegBig (args a ++ c :: app b c :: R) ∧ ¬ (isP b ∧ isY c) := by
  obtain ⟨⟨C, Pl, Yl, hL, hC, hP, hY, h3⟩, hO⟩ := hI
  have hOrd : ∀ e ∈ args a ++ c :: app b c :: R, ordered e := by
    intro e he; simp at he
    rcases he with he | he | he | he
    · exact ordered_args a (hO a (by simp)) e he
    · rw [he]; exact hO c (by simp)
    · rw [he]
      refine ⟨?_, hO b (by simp), hO c (by simp)⟩
      intro _ hcc
      -- c closed forces b closed: b lies above c in the segment order
      match C, Pl, hL, hC, hP with
      | c1 :: c2 :: c3 :: C', _, hL, hC, _ =>
        simp at hL; obtain ⟨_, rfl, rfl, _⟩ := hL; exact hC b (by simp)
      | [c1, c2], e :: Pl', hL, hC, hP =>
        simp at hL; obtain ⟨_, rfl, rfl, _⟩ := hL; exact hC b (by simp)
      | [c1, c2], [], hL, _, _ => simp at h3
      | [c1], e1 :: e2 :: Pl', hL, _, hP =>
        simp at hL; obtain ⟨_, rfl, rfl, _⟩ := hL
        exact absurd hcc (not_closed_P c (hP c (by simp)))
      | [c1], [e], _, _, _ => simp at h3
      | [c1], [], _, _, _ => simp at h3
      | [], e1 :: e2 :: e3 :: Pl', hL, _, hP =>
        simp at hL; obtain ⟨_, rfl, rfl, _⟩ := hL
        exact absurd hcc (not_closed_P c (hP c (by simp)))
      | [], [e1, e2], _, _, _ => simp at h3
      | [], [e], _, _, _ => simp at h3
      | [], [], _, _, _ => simp at h3
    · exact hO e (by simp [he])
  match C, Pl, hL, hC, hP with
  | c1 :: c2 :: c3 :: C', Pl, hL, hC, hP =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb : closed b := hC b (by simp)
    have hcc : closed c := hC c (by simp)
    refine ⟨⟨⟨args a ++ c :: app b c :: C', Pl, Yl, by simp [hR], ?_, hP, hY, h3⟩, hOrd⟩, ?_⟩
    · intro x hx; simp at hx
      rcases hx with hx | hx | hx | hx
      · exact closed_args a hca x hx
      · rw [hx]; exact hcc
      · rw [hx]; exact ⟨hcb, hcc⟩
      · exact hC x (by simp [hx])
    · intro ⟨hpb, _⟩; exact not_closed_P b hpb hcb
  | [c1, c2], e :: Pl', hL, hC, hP =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb : closed b := hC b (by simp)
    have hPc : isP c := hP c (by simp)
    refine ⟨⟨⟨args a, c :: app b c :: Pl', Yl, by simp [hR], closed_args a hca, ?_, hY, ?_⟩, hOrd⟩, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · rw [he]; exact hPc
      · rw [he]; exact isP_app b c (Or.inl hcb) hPc
      · exact hP e (by simp [he])
    · simp at h3 ⊢; omega
    · intro ⟨hpb, _⟩; exact not_closed_P b hpb hcb
  | [c1, c2], [], _, _, _ => simp at h3
  | [c1], e1 :: e2 :: Pl', hL, hC, hP =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hPb : isP b := hP b (by simp)
    have hPc : isP c := hP c (by simp)
    refine ⟨⟨⟨args a, c :: app b c :: Pl', Yl, by simp [hR], closed_args a hca, ?_, hY, ?_⟩, hOrd⟩, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · rw [he]; exact hPc
      · rw [he]; exact isP_app b c (Or.inr hPb) hPc
      · exact hP e (by simp [he])
    · simp at h3 ⊢; omega
    · intro ⟨_, hyc⟩; exact not_PY c hPc hyc
  | [c1], [e], _, _, _ => simp at h3
  | [c1], [], _, _, _ => simp at h3
  | [], e1 :: e2 :: e3 :: Pl', hL, hC, hP =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hPa : isP a := hP a (by simp)
    have hPb : isP b := hP b (by simp)
    have hPc : isP c := hP c (by simp)
    obtain ⟨C0, D0, hs, hC0, hD0, hne⟩ := P_args_split a hPa ha (hO a (by simp))
    refine ⟨⟨⟨C0, D0 ++ c :: app b c :: Pl', Yl, by simp [hs, hR], hC0, ?_, hY, ?_⟩, hOrd⟩, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he | he
      · exact hD0 e he
      · rw [he]; exact hPc
      · rw [he]; exact isP_app b c (Or.inr hPb) hPc
      · exact hP e (by simp [he])
    · match D0, hne with
      | d :: D0', _ => simp; omega
    · intro ⟨_, hyc⟩; exact not_PY c hPc hyc
  | [], [e1, e2], _, _, _ => simp at h3
  | [], [e], _, _, _ => simp at h3
  | [], [], _, _, _ => simp at h3

/-- **Lemma AB.** Along any run from a list whose P-region has at least three elements, the P-region keeps at least
    three elements, and no step glues a P-element onto a Y-element. -/
theorem ab_run : ∀ (k : Nat) (L L' : List T), SegBig L → run k L = some L' → SegBig L'
  | 0, L, L', hI, h => by simp [run] at h; subst h; exact hI
  | k + 1, L, L', hI, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      apply ab_run k L1 L' _ h
      match L, hs with
      | a :: b :: c :: R, hs =>
        simp only [step] at hs
        split at hs
        · rename_i ha
          injection hs with hs; subst hs
          exact (ab_step a b c R ha hI).1
        · exact absurd hs (by simp)
    · exact absurd h (by simp)

theorem ab_no_glue (k : Nat) (L : List T) (a b c : T) (R : List T) (hI : SegBig L)
    (hrun : run k L = some (a :: b :: c :: R)) (ha : head a = S) : ¬ (isP b ∧ isY c) :=
  (ab_step a b c R ha (ab_run k L _ hI hrun)).2

/-! ## Theorem MSL (multi-level data).
  Lv = right combs over p with closed wrappers; LP = level-prefixed (some left-spine prefix is in Lv);
  good e = LP e or every P spine argument of e is LP.  From args K ++ [l, y, x.y, r] (K closed, l in Lv) every
  P-element glued onto a Y-element is good, and hereditarily every subterm w.q (w in P, q in Y) has good w. -/

def Lv : T → Prop
  | var n => n = 0
  | app d l => closed d ∧ Lv l
  | S => False

def LP : T → Prop
  | S => False
  | var n => n = 0
  | app f x => Lv (app f x) ∨ LP f

def good (t : T) : Prop := LP t ∨ ∀ s ∈ args t, isP s → LP s

/-- hereditary: S-headed subterms have no non-Y spine argument after a Y one -/
def ordY : T → Prop
  | app f x => (head f = S → ¬ isY x → ¬ isY f) ∧ ordY f ∧ ordY x
  | _ => True

/-- hereditary: every subterm l.u with l in Lv and u in P has good u -/
def ma : T → Prop
  | app f x => ma f ∧ ma x ∧ (Lv f → isP x → good x)
  | _ => True

/-- hereditary: every subterm w.q with w in P and q in Y has good w -/
def gm : T → Prop
  | app f x => gm f ∧ gm x ∧ (isP f → isY x → good f)
  | _ => True

theorem Lv_isP : ∀ t : T, Lv t → isP t
  | S, h => by simp [Lv] at h
  | var n, h => by
    simp [Lv] at h; subst h; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [occ]
  | app d l, h => by
    have hd := closed_iff_atoms d h.1
    have hl := Lv_isP l h.2
    obtain ⟨l0, l1, l2, l3⟩ := hl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [occ_app] <;> omega

theorem Lv_LP (t : T) (h : Lv t) : LP t := by
  cases t with
  | S => simp [Lv] at h
  | var n => simpa [Lv, LP] using h
  | app f x => exact Or.inl h

theorem LP_app (f x : T) (h : LP f) : LP (app f x) := Or.inr h

theorem LP_occ0 : ∀ t : T, LP t → occ 0 t ≠ 0
  | S, h => by simp [LP] at h
  | var n, h => by simp [LP] at h; subst h; simp [occ]
  | app f x, h => by
    rcases h with h | h
    · exact (Lv_isP _ h).1
    · have := LP_occ0 f h; simp [occ_app]; omega

theorem good_of_LP (t : T) (h : LP t) : good t := Or.inl h

theorem ordY_args : ∀ t : T, ordY t → ∀ s ∈ args t, ordY s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact ordY_args f h.2.1 s hs
    · subst hs; exact h.2.2

theorem ma_args : ∀ t : T, ma t → ∀ s ∈ args t, ma s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact ma_args f h.1 s hs
    · subst hs; exact h.2.1

theorem gm_args : ∀ t : T, gm t → ∀ s ∈ args t, gm s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact gm_args f h.1 s hs
    · subst hs; exact h.2.1

theorem not_Lv_closed (t : T) (h : closed t) : ¬ Lv t := fun hl => not_closed_P t (Lv_isP t hl) h
theorem not_Lv_Y (t : T) (h : isY t) : ¬ Lv t := fun hl => not_PY t (Lv_isP t hl) h

theorem isY_app_split (f x : T) (h : isY (app f x)) : isY f ∨ isY x := by
  rcases h with h | h | h <;> simp only [occ_app] at h
  · by_cases hf : occ 1 f = 0
    · right; left; omega
    · left; left; exact hf
  · by_cases hf : occ 2 f = 0
    · right; right; left; omega
    · left; right; left; exact hf
  · by_cases hf : occ 3 f = 0
    · right; right; right; omega
    · left; right; right; exact hf

theorem isP_left (f x : T) (hP : isP (app f x)) (h0 : occ 0 f ≠ 0) : isP f := by
  obtain ⟨_, h1, h2, h3⟩ := hP
  simp only [occ_app] at h1 h2 h3
  exact ⟨h0, by omega, by omega, by omega⟩

theorem isP_right (f x : T) (hP : isP (app f x)) (hnc : ¬ closed x) : isP x := by
  obtain ⟨_, h1, h2, h3⟩ := hP
  simp only [occ_app] at h1 h2 h3
  rcases trichotomy x with h | h | h
  · exact absurd h hnc
  · exact h
  · exfalso; rcases h with h | h | h <;> omega

/-- opening a level-prefixed P-element: its P-arguments contain an LP element; if there is exactly one P-argument
    the element is a level itself; if there are exactly two, both are good (by ma). -/
theorem LP_open : ∀ a : T, LP a → head a = S → isP a → ordered a → ma a →
    ∃ Ca Pa : List T, args a = Ca ++ Pa ∧ (∀ x ∈ Ca, closed x) ∧ (∀ x ∈ Pa, isP x) ∧ (∃ e ∈ Pa, LP e) ∧
      (Pa.length = 1 → Lv a) ∧ (Pa.length = 2 → ∀ e ∈ Pa, good e)
  | S, h, _, _, _, _ => by simp [LP] at h
  | var _, _, hS, _, _, _ => by simp [head] at hS
  | app f x, h, hS, hP, ho, hm => by
    have hfS : head f = S := by simpa [head] using hS
    by_cases hv : Lv (app f x)
    · obtain ⟨hcf, hlx⟩ := hv
      refine ⟨args f, [x], by simp [args], closed_args f hcf, ?_, ⟨x, by simp, Lv_LP x hlx⟩, fun _ => ⟨hcf, hlx⟩, ?_⟩
      · intro e he; simp at he; rw [he]; exact Lv_isP x hlx
      · intro hl; simp at hl
    · have hLf : LP f := by
        rcases h with h | h
        · exact absurd h hv
        · exact h
      have hPf : isP f := isP_left f x hP (LP_occ0 f hLf)
      have hncx : ¬ closed x := fun hcx => not_closed_P f hPf (ho.1 hfS hcx)
      have hPx : isP x := isP_right f x hP hncx
      obtain ⟨Cf, Pf, hsplit, hC, hPP, ⟨e0, he0, hLe0⟩, h1, h2⟩ := LP_open f hLf hfS hPf ho.2.1 hm.1
      refine ⟨Cf, Pf ++ [x], by simp [args, hsplit], hC, ?_, ⟨e0, by simp [he0], hLe0⟩, ?_, ?_⟩
      · intro e he; simp at he
        rcases he with he | he
        · exact hPP e he
        · subst he; exact hPx
      · intro hl
        have : Pf.length = 0 := by simp only [List.length_append, List.length_singleton] at hl; omega
        have hnil : Pf = [] := List.eq_nil_of_length_eq_zero this
        rw [hnil] at he0; simp at he0
      · intro hl
        have hl1 : Pf.length = 1 := by simp only [List.length_append, List.length_singleton] at hl; omega
        have hLvf : Lv f := h1 hl1
        have hgx : good x := hm.2.2 hLvf hPx
        intro e he; simp at he
        rcases he with he | he
        · match Pf, hl1, he0, he with
          | [e1], _, he0, he =>
            simp at he0 he; rw [he, ← he0]; exact good_of_LP e0 hLe0
        · subst he; exact hgx

theorem open_P (a : T) (hP : isP a) (hS : head a = S) (ho : ordered a) (hm : ma a) (hg : good a) :
    ∃ Ca Pa : List T, args a = Ca ++ Pa ∧ (∀ x ∈ Ca, closed x) ∧ (∀ x ∈ Pa, isP x) ∧
      (Pa = [] ∨ ∃ e ∈ Pa, LP e) ∧ (Pa.length = 2 → ∀ e ∈ Pa, good e) := by
  rcases hg with hg | hg
  · obtain ⟨Ca, Pa, h1, h2, h3, h4, _, h6⟩ := LP_open a hg hS hP ho hm
    exact ⟨Ca, Pa, h1, h2, h3, Or.inr h4, h6⟩
  · obtain ⟨C0, D0, hs, hC, hD, hne⟩ := P_args_split a hP hS ho
    refine ⟨C0, D0, hs, hC, hD, ?_, ?_⟩
    · right
      match D0, hne with
      | e :: D', _ => exact ⟨e, by simp, hg e (by rw [hs]; simp) (hD e (by simp))⟩
    · intro _ e he
      exact good_of_LP e (hg e (by rw [hs]; simp [he]) (hD e he))

theorem open_Y : ∀ a : T, isY a → head a = S → ordered a → ordY a → ma a → gm a →
    ∃ Ca Pa Ya : List T, args a = Ca ++ Pa ++ Ya ∧ (∀ x ∈ Ca, closed x) ∧ (∀ x ∈ Pa, isP x) ∧
      (∀ x ∈ Ya, isY x) ∧ (Pa = [] ∨ ∃ e ∈ Pa, LP e) ∧ (Pa.length = 2 → ∀ e ∈ Pa, good e)
  | S, hY, _, _, _, _, _ => by
    exfalso; rcases hY with h | h | h <;> simp [occ] at h
  | var _, _, hS, _, _, _, _ => by simp [head] at hS
  | app f x, hY, hS, ho, hoy, hm, hg => by
    have hfS : head f = S := by simpa [head] using hS
    have hYx : isY x := by
      by_cases hx : isY x
      · exact hx
      · exfalso
        have hnf := hoy.1 hfS hx
        rcases isY_app_split f x hY with h | h
        · exact hnf h
        · exact hx h
    rcases trichotomy f with hf | hf | hf
    · refine ⟨args f, [], [x], by simp [args], closed_args f hf, by simp, ?_, Or.inl rfl, by simp⟩
      intro e he; simp at he; subst he; exact hYx
    · have hgf : good f := hg.2.2 hf hYx
      obtain ⟨Cf, Pf, hs, hC, hPP, hQ, hT⟩ := open_P f hf hfS ho.2.1 hm.1 hgf
      refine ⟨Cf, Pf, [x], by simp [args, hs], hC, hPP, ?_, hQ, hT⟩
      intro e he; simp at he; subst he; exact hYx
    · obtain ⟨Cf, Pf, Yf, hs, hC, hPP, hYY, hQ, hT⟩ := open_Y f hf hfS ho.2.1 hoy.2.1 hm.1 hg.1
      refine ⟨Cf, Pf, Yf ++ [x], by simp [args, hs], hC, hPP, ?_, hQ, hT⟩
      intro e he; simp at he
      rcases he with he | he
      · exact hYY e he
      · subst he; exact hYx

/-! ### the small-P-region invariant -/

def MS (L : List T) : Prop :=
  (∃ C Pl Yl : List T, L = C ++ Pl ++ Yl ∧ (∀ c ∈ C, closed c) ∧ (∀ e ∈ Pl, isP e) ∧ (∀ e ∈ Yl, isY e) ∧
     Pl.length ≤ 2 ∧ (Pl = [] ∨ ∃ e ∈ Pl, LP e) ∧ (Pl.length = 2 → ∀ e ∈ Pl, good e)) ∧
  (∀ e ∈ L, ordered e) ∧ (∀ e ∈ L, ordY e) ∧ (∀ e ∈ L, ma e) ∧ (∀ e ∈ L, gm e)

theorem gm_step (a b c : T) (R : List T) (hG : ∀ e ∈ a :: b :: c :: R, gm e) (hgb : isP b → isY c → good b) :
    ∀ e ∈ args a ++ c :: app b c :: R, gm e := by
  intro e he; simp at he
  rcases he with he | he | he | he
  · exact gm_args a (hG a (by simp)) e he
  · rw [he]; exact hG c (by simp)
  · rw [he]; exact ⟨hG b (by simp), hG c (by simp), hgb⟩
  · exact hG e (by simp [he])

theorem ms_gen (a b c : T) (R : List T)
    (hO : ∀ e ∈ a :: b :: c :: R, ordered e) (hOY : ∀ e ∈ a :: b :: c :: R, ordY e)
    (hM : ∀ e ∈ a :: b :: c :: R, ma e) (hG : ∀ e ∈ a :: b :: c :: R, gm e)
    (hcb : head b = S → closed c → closed b) (hyb : head b = S → ¬ isY c → ¬ isY b)
    (hmb : Lv b → isP c → good c) (hgb : isP b → isY c → good b)
    (hseg : ∃ C Pl Yl : List T, args a ++ c :: app b c :: R = C ++ Pl ++ Yl ∧ (∀ x ∈ C, closed x) ∧
      (∀ e ∈ Pl, isP e) ∧ (∀ e ∈ Yl, isY e) ∧ (Pl = [] ∨ ∃ e ∈ Pl, LP e) ∧
      (Pl.length = 2 → ∀ e ∈ Pl, good e)) :
    MS (args a ++ c :: app b c :: R) ∨ SegBig (args a ++ c :: app b c :: R) := by
  have hO' : ∀ e ∈ args a ++ c :: app b c :: R, ordered e := by
    intro e he; simp at he
    rcases he with he | he | he | he
    · exact ordered_args a (hO a (by simp)) e he
    · rw [he]; exact hO c (by simp)
    · rw [he]; exact ⟨hcb, hO b (by simp), hO c (by simp)⟩
    · exact hO e (by simp [he])
  have hOY' : ∀ e ∈ args a ++ c :: app b c :: R, ordY e := by
    intro e he; simp at he
    rcases he with he | he | he | he
    · exact ordY_args a (hOY a (by simp)) e he
    · rw [he]; exact hOY c (by simp)
    · rw [he]; exact ⟨hyb, hOY b (by simp), hOY c (by simp)⟩
    · exact hOY e (by simp [he])
  have hM' : ∀ e ∈ args a ++ c :: app b c :: R, ma e := by
    intro e he; simp at he
    rcases he with he | he | he | he
    · exact ma_args a (hM a (by simp)) e he
    · rw [he]; exact hM c (by simp)
    · rw [he]; exact ⟨hM b (by simp), hM c (by simp), hmb⟩
    · exact hM e (by simp [he])
  have hG' := gm_step a b c R hG hgb
  obtain ⟨C, Pl, Yl, hL, hC, hP, hY, hQ, hT⟩ := hseg
  by_cases hlen : Pl.length ≤ 2
  · left; exact ⟨⟨C, Pl, Yl, hL, hC, hP, hY, hlen, hQ, hT⟩, hO', hOY', hM', hG'⟩
  · right; exact ⟨⟨C, Pl, Yl, hL, hC, hP, hY, by omega⟩, hO'⟩

theorem LP_of_single (x : T) (Pl : List T) (hPl : Pl = [x]) (hQ : Pl = [] ∨ ∃ e ∈ Pl, LP e) : LP x := by
  subst hPl
  rcases hQ with hQ | ⟨e', he', hh⟩
  · simp at hQ
  · simp at he'; exact he' ▸ hh

theorem ms_step (a b c : T) (R : List T) (ha : head a = S) (hI : MS (a :: b :: c :: R)) :
    (MS (args a ++ c :: app b c :: R) ∨ SegBig (args a ++ c :: app b c :: R)) ∧ (isP b → isY c → good b) := by
  obtain ⟨⟨C, Pl, Yl, hL, hC, hP, hY, hlen, hQ, hT⟩, hO, hOY, hM, hG⟩ := hI
  match C, Pl, hL, hC, hP, hlen, hQ, hT with
  -- A: a, b, c closed
  | c1 :: c2 :: c3 :: C', Pl, hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb' : closed b := hC b (by simp)
    have hcc : closed c := hC c (by simp)
    have hgb : isP b → isY c → good b := fun hPb => absurd hcb' (not_closed_P b hPb)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ _ => hcb') (fun _ _ hYb => not_closed_Y b hYb hcb')
      (fun hl => absurd hl (not_Lv_closed b hcb')) hgb ?_, hgb⟩
    refine ⟨args a ++ c :: app b c :: C', Pl, Yl, by simp [hR], ?_, hP, hY, hQ, hT⟩
    intro x hx; simp at hx
    rcases hx with hx | hx | hx | hx
    · exact closed_args a hca x hx
    · rw [hx]; exact hcc
    · rw [hx]; exact closed_app b c hcb' hcc
    · exact hC x (by simp [hx])
  -- B0: a, b closed, P empty, c the top of Y
  | [c1, c2], [], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb' : closed b := hC b (by simp)
    have hYc : isY c := hY c (by rw [← hR]; simp)
    have hgb : isP b → isY c → good b := fun hPb => absurd hcb' (not_closed_P b hPb)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
      (fun _ _ hYb => not_closed_Y b hYb hcb') (fun hl => absurd hl (not_Lv_closed b hcb')) hgb ?_, hgb⟩
    refine ⟨args a, [], c :: app b c :: R, by simp, closed_args a hca, by simp, ?_, Or.inl rfl, by simp⟩
    intro e he; simp at he
    rcases he with he | he | he
    · rw [he]; exact hYc
    · rw [he]; exact isY_app_r b c hYc
    · exact hY e (by rw [← hR]; simp [he])
  -- B1: a, b closed, P = [c]
  | [c1, c2], [e], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb' : closed b := hC b (by simp)
    have hPc : isP c := hP c (by simp)
    have hLc : LP c := LP_of_single c [c] rfl hQ
    have hPbc : isP (app b c) := isP_app b c (Or.inl hcb') hPc
    have hgb : isP b → isY c → good b := fun hPb => absurd hcb' (not_closed_P b hPb)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_P c hPc))
      (fun _ _ hYb => not_closed_Y b hYb hcb') (fun hl => absurd hl (not_Lv_closed b hcb')) hgb ?_, hgb⟩
    refine ⟨args a, [c, app b c], Yl, by simp [hR], closed_args a hca, ?_, hY, Or.inr ⟨c, by simp, hLc⟩, ?_⟩
    · intro x hx; simp at hx
      rcases hx with hx | hx
      · rw [hx]; exact hPc
      · rw [hx]; exact hPbc
    · intro _ x hx; simp at hx
      rcases hx with hx | hx
      · rw [hx]; exact good_of_LP c hLc
      · rw [hx]; right; intro s hs hsP
        rcases args_app_mem b c s hs with hs | hs
        · exact absurd hsP (not_isP_closed s (closed_args b hcb' s hs))
        · rw [hs]; exact hLc
  -- B2: a, b closed, P = [c, e2]: the P-region grows to three
  | [c1, c2], [e1, e2], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hcb' : closed b := hC b (by simp)
    have hPc : isP c := hP c (by simp)
    have hPe2 : isP e2 := hP e2 (by simp)
    have hPbc : isP (app b c) := isP_app b c (Or.inl hcb') hPc
    have hgb : isP b → isY c → good b := fun hPb => absurd hcb' (not_closed_P b hPb)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_P c hPc))
      (fun _ _ hYb => not_closed_Y b hYb hcb') (fun hl => absurd hl (not_Lv_closed b hcb')) hgb ?_, hgb⟩
    refine ⟨args a, [c, app b c, e2], Yl, by simp [hR], closed_args a hca, ?_, hY, ?_, by simp⟩
    · intro x hx; simp at hx
      rcases hx with hx | hx | hx
      · rw [hx]; exact hPc
      · rw [hx]; exact hPbc
      · rw [hx]; exact hPe2
    · right
      rcases hQ with hQ | ⟨e', he', hh⟩
      · simp at hQ
      · simp at he'
        rcases he' with he' | he'
        · exact ⟨c, by simp, he' ▸ hh⟩
        · exact ⟨e2, by simp, he' ▸ hh⟩
  -- C0: a closed, P empty, b, c in Y
  | [c1], [], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hYb : isY b := hY b (by rw [← hR]; simp)
    have hYc : isY c := hY c (by rw [← hR]; simp)
    have hgb : isP b → isY c → good b := fun hPb => absurd hYb (fun h => not_PY b hPb h)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
      (fun _ hnc => absurd hYc hnc) (fun hl => absurd hl (not_Lv_Y b hYb)) hgb ?_, hgb⟩
    refine ⟨args a, [], c :: app b c :: R, by simp, closed_args a hca, by simp, ?_, Or.inl rfl, by simp⟩
    intro e he; simp at he
    rcases he with he | he | he
    · rw [he]; exact hYc
    · rw [he]; exact isY_app_l b c hYb
    · exact hY e (by rw [← hR]; simp [he])
  -- C1: a closed, P = [b], c the top of Y: the glue case, b is LP
  | [c1], [e], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hLb : LP b := LP_of_single b [b] rfl hQ
    have hYc : isY c := hY c (by rw [← hR]; simp)
    have hgb : isP b → isY c → good b := fun _ _ => good_of_LP b hLb
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
      (fun _ hnc => absurd hYc hnc) (fun _ hPc => absurd hYc (fun h => not_PY c hPc h)) hgb ?_, hgb⟩
    refine ⟨args a, [], c :: app b c :: R, by simp, closed_args a hca, by simp, ?_, Or.inl rfl, by simp⟩
    intro e he; simp at he
    rcases he with he | he | he
    · rw [he]; exact hYc
    · rw [he]; exact isY_app_r b c hYc
    · exact hY e (by rw [← hR]; simp [he])
  -- C2: a closed, P = [b, c]
  | [c1], [e1, e2], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hca : closed a := hC a (by simp)
    have hPb : isP b := hP b (by simp)
    have hPc : isP c := hP c (by simp)
    have hPbc : isP (app b c) := isP_app b c (Or.inr hPb) hPc
    have hgT : ∀ e ∈ [b, c], good e := hT (by simp)
    have hgc : good c := hgT c (by simp)
    have hgb' : good b := hgT b (by simp)
    have hgb : isP b → isY c → good b := fun _ hYc => absurd hYc (fun h => not_PY c hPc h)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_P c hPc))
      (fun _ _ hYb => not_PY b hPb hYb) (fun _ _ => hgc) hgb ?_, hgb⟩
    refine ⟨args a, [c, app b c], Yl, by simp [hR], closed_args a hca, ?_, hY, ?_, ?_⟩
    · intro x hx; simp at hx
      rcases hx with hx | hx
      · rw [hx]; exact hPc
      · rw [hx]; exact hPbc
    · right
      rcases hQ with hQ | ⟨e', he', hh⟩
      · simp at hQ
      · simp at he'
        rcases he' with he' | he'
        · exact ⟨app b c, by simp, LP_app b c (he' ▸ hh)⟩
        · exact ⟨c, by simp, he' ▸ hh⟩
    · intro _ x hx; simp at hx
      rcases hx with hx | hx
      · rw [hx]; exact hgc
      · rw [hx]
        by_cases hLb : LP b
        · exact good_of_LP _ (LP_app b c hLb)
        · right
          have hb' : ∀ s ∈ args b, isP s → LP s := by
            rcases hgb' with h | h
            · exact absurd h hLb
            · exact h
          have hLc : LP c := by
            rcases hQ with hQ | ⟨e', he', hh⟩
            · simp at hQ
            · simp at he'
              rcases he' with he' | he'
              · exact absurd (he' ▸ hh) hLb
              · exact he' ▸ hh
          intro s hs hsP
          rcases args_app_mem b c s hs with hs | hs
          · exact hb' s hs hsP
          · rw [hs]; exact hLc
  -- D0: P empty, a, b, c in Y: a Y-front is opened
  | [], [], hL, hC, hP, hlen, hQ, hT =>
    simp at hL
    have hYa : isY a := hY a (by rw [← hL]; simp)
    have hYb : isY b := hY b (by rw [← hL]; simp)
    have hYc : isY c := hY c (by rw [← hL]; simp)
    obtain ⟨Ca, Pa, Ya, hs, hCa, hPa, hYa', hQa, hTa⟩ :=
      open_Y a hYa ha (hO a (by simp)) (hOY a (by simp)) (hM a (by simp)) (hG a (by simp))
    have hgb : isP b → isY c → good b := fun hPb => absurd hYb (fun h => not_PY b hPb h)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
      (fun _ hnc => absurd hYc hnc) (fun hl => absurd hl (not_Lv_Y b hYb)) hgb ?_, hgb⟩
    refine ⟨Ca, Pa, Ya ++ c :: app b c :: R, by rw [hs]; simp, hCa, hPa, ?_, hQa, hTa⟩
    intro e he; simp at he
    rcases he with he | he | he | he
    · exact hYa' e he
    · rw [he]; exact hYc
    · rw [he]; exact isY_app_l b c hYb
    · exact hY e (by rw [← hL]; simp [he])
  -- D1: P = [a], b, c in Y: a is LP and is opened
  | [], [e], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, hR⟩ := hL
    have hLa : LP a := LP_of_single a [a] rfl hQ
    have hPa : isP a := hP a (by simp)
    obtain ⟨Ca, Pa, hs, hCa, hPa', hQa, hTa⟩ :=
      open_P a hPa ha (hO a (by simp)) (hM a (by simp)) (good_of_LP a hLa)
    have hYb : isY b := hY b (by rw [← hR]; simp)
    have hYc : isY c := hY c (by rw [← hR]; simp)
    have hgb : isP b → isY c → good b := fun hPb => absurd hYb (fun h => not_PY b hPb h)
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
      (fun _ hnc => absurd hYc hnc) (fun hl => absurd hl (not_Lv_Y b hYb)) hgb ?_, hgb⟩
    refine ⟨Ca, Pa, c :: app b c :: R, by rw [hs], hCa, hPa', ?_, hQa, hTa⟩
    intro e he; simp at he
    rcases he with he | he | he
    · rw [he]; exact hYc
    · rw [he]; exact isY_app_l b c hYb
    · exact hY e (by rw [← hR]; simp [he])
  -- D2: P = [a, b], c the top of Y: the glue case, b good by Claim T
  | [], [e1, e2], hL, hC, hP, hlen, hQ, hT =>
    simp at hL; obtain ⟨rfl, rfl, hR⟩ := hL
    have hPa : isP a := hP a (by simp)
    have hgT : ∀ e ∈ [a, b], good e := hT (by simp)
    have hga : good a := hgT a (by simp)
    have hgb' : good b := hgT b (by simp)
    obtain ⟨Ca, Pa, hs, hCa, hPa', hQa, hTa⟩ := open_P a hPa ha (hO a (by simp)) (hM a (by simp)) hga
    have hYc : isY c := hY c (by rw [← hR]; simp)
    have hgb : isP b → isY c → good b := fun _ _ => hgb'
    refine ⟨ms_gen a b c R hO hOY hM hG (fun _ hcc => absurd hcc (not_closed_Y c hYc))
      (fun _ hnc => absurd hYc hnc) (fun _ hPc => absurd hYc (fun h => not_PY c hPc h)) hgb ?_, hgb⟩
    refine ⟨Ca, Pa, c :: app b c :: R, by rw [hs], hCa, hPa', ?_, hQa, hTa⟩
    intro e he; simp at he
    rcases he with he | he | he
    · rw [he]; exact hYc
    · rw [he]; exact isY_app_r b c hYc
    · exact hY e (by rw [← hR]; simp [he])
  -- P-regions with three or more elements are excluded by MS
  | _, _ :: _ :: _ :: _, _, _, _, hlen, _, _ =>
    simp only [List.length_cons] at hlen; omega

/-! ### combined invariant: small P-region (MS) or Lemma AB's regime, plus the hereditary GM -/

def MInv (L : List T) : Prop := (MS L ∨ SegBig L) ∧ ∀ e ∈ L, gm e

theorem minv_step (a b c : T) (R : List T) (ha : head a = S) (hI : MInv (a :: b :: c :: R)) :
    MInv (args a ++ c :: app b c :: R) ∧ (isP b → isY c → good b) := by
  obtain ⟨hI | hI, hG⟩ := hI
  · obtain ⟨h1, h2⟩ := ms_step a b c R ha hI
    exact ⟨⟨h1, gm_step a b c R hG h2⟩, h2⟩
  · obtain ⟨h1, h2⟩ := ab_step a b c R ha hI
    have hgb : isP b → isY c → good b := fun hb hc => absurd ⟨hb, hc⟩ h2
    exact ⟨⟨Or.inr h1, gm_step a b c R hG hgb⟩, hgb⟩

theorem minv_run : ∀ (k : Nat) (L L' : List T), MInv L → run k L = some L' → MInv L'
  | 0, L, L', hI, h => by simp [run] at h; subst h; exact hI
  | k + 1, L, L', hI, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      apply minv_run k L1 L' _ h
      match L, hs with
      | a :: b :: c :: R, hs =>
        simp only [step] at hs
        split at hs
        · rename_i ha
          injection hs with hs; subst hs
          exact (minv_step a b c R ha hI).1
        · exact absurd hs (by simp)
    · exact absurd h (by simp)

theorem closed_ordered' : ∀ t : T, closed t → ordered t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => ⟨fun _ _ => h.1, closed_ordered' f h.1, closed_ordered' x h.2⟩

theorem closed_ordY : ∀ t : T, closed t → ordY t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => ⟨fun _ _ hY => not_closed_Y f hY h.1, closed_ordY f h.1, closed_ordY x h.2⟩

theorem closed_ma : ∀ t : T, closed t → ma t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => ⟨closed_ma f h.1, closed_ma x h.2, fun hl => absurd hl (not_Lv_closed f h.1)⟩

theorem closed_gm : ∀ t : T, closed t → gm t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => ⟨closed_gm f h.1, closed_gm x h.2, fun hP => absurd h.1 (not_closed_P f hP)⟩

theorem Lv_all : ∀ t : T, Lv t → ordered t ∧ ordY t ∧ ma t ∧ gm t
  | S, h => by simp [Lv] at h
  | var _, _ => ⟨trivial, trivial, trivial, trivial⟩
  | app d l, h => by
    obtain ⟨hd, hl⟩ := h
    obtain ⟨h1, h2, h3, h4⟩ := Lv_all l hl
    exact ⟨⟨fun _ _ => hd, closed_ordered' d hd, h1⟩,
      ⟨fun _ _ hY => not_closed_Y d hY hd, closed_ordY d hd, h2⟩,
      ⟨closed_ma d hd, h3, fun hl' => absurd hl' (not_Lv_closed d hd)⟩,
      ⟨closed_gm d hd, h4, fun hP => absurd hd (not_closed_P d hP)⟩⟩

/-- the start of the phase: [K.l, x, y, r] after one step, K closed, l a right comb over p with closed wrappers -/
theorem minv_init (K l : T) (hK : closed K) (hl : Lv l) :
    MInv (args K ++ [l, var 2, app (var 1) (var 2), var 3]) := by
  have hargs := closed_args K hK
  have hY2 : isY (var 2) := Or.inr (Or.inl (by simp [occ]))
  have hYxy : isY (app (var 1) (var 2)) := isY_app_r _ _ hY2
  have hY3 : isY (var 3) := Or.inr (Or.inr (by simp [occ]))
  obtain ⟨hlo, hloy, hlm, hlg⟩ := Lv_all l hl
  have hnLv1 : ¬ Lv (var 1) := by simp [Lv]
  have hnP1 : ¬ isP (var 1) := fun h => h.1 (by simp [occ])
  have hgm : ∀ e ∈ args K ++ [l, var 2, app (var 1) (var 2), var 3], gm e := by
    intro e he; simp at he
    rcases he with he | he | he | he | he
    · exact closed_gm e (hargs e he)
    · rw [he]; exact hlg
    · rw [he]; trivial
    · rw [he]; exact ⟨trivial, trivial, fun h => absurd h hnP1⟩
    · rw [he]; trivial
  refine ⟨Or.inl ⟨⟨args K, [l], [var 2, app (var 1) (var 2), var 3], by simp, hargs, ?_, ?_, by simp,
    Or.inr ⟨l, by simp, Lv_LP l hl⟩, by simp⟩, ?_, ?_, ?_, hgm⟩, hgm⟩
  · intro e he; simp at he; rw [he]; exact Lv_isP l hl
  · intro e he; simp at he
    rcases he with he | he | he
    · rw [he]; exact hY2
    · rw [he]; exact hYxy
    · rw [he]; exact hY3
  · intro e he; simp at he
    rcases he with he | he | he | he | he
    · exact closed_ordered' e (hargs e he)
    · rw [he]; exact hlo
    · rw [he]; trivial
    · rw [he]; exact ⟨fun h => by simp [head] at h, trivial, trivial⟩
    · rw [he]; trivial
  · intro e he; simp at he
    rcases he with he | he | he | he | he
    · exact closed_ordY e (hargs e he)
    · rw [he]; exact hloy
    · rw [he]; trivial
    · rw [he]; exact ⟨fun h => by simp [head] at h, trivial, trivial⟩
    · rw [he]; trivial
  · intro e he; simp at he
    rcases he with he | he | he | he | he
    · exact closed_ma e (hargs e he)
    · rw [he]; exact hlm
    · rw [he]; trivial
    · rw [he]; exact ⟨trivial, trivial, fun h => absurd h hnLv1⟩
    · rw [he]; trivial

/-- **Theorem MSL (step form).**  In the generic run of a multi-level datum K.l (K closed, l = d2.(...(dk.p)) a
    right comb over p with closed wrappers), every step that glues a P-element b onto a Y-element glues a good b:
    b is level-prefixed, or every P spine argument of b is level-prefixed. -/
theorem msl_glue (K l : T) (hK : closed K) (hl : Lv l) (k : Nat) (a b c : T) (R : List T)
    (hrun : run k (args K ++ [l, var 2, app (var 1) (var 2), var 3]) = some (a :: b :: c :: R))
    (ha : head a = S) (hb : isP b) (hc : isY c) : good b :=
  (minv_step a b c R ha (minv_run k _ _ (minv_init K l hK hl) hrun)).2 hb hc

/-- **Theorem MSL (hereditary form).**  Every subterm w.q (w in P, q in Y) of every element of every reachable list
    has w good. -/
theorem msl_main (K l : T) (hK : closed K) (hl : Lv l) (k : Nat) (L : List T)
    (hrun : run k (args K ++ [l, var 2, app (var 1) (var 2), var 3]) = some L) : ∀ e ∈ L, gm e :=
  (minv_run k _ _ (minv_init K l hK hl) hrun).2

/-- the same run, started from the datum itself: [K.l, x, y, r] makes exactly this first step -/
theorem msl_first_step (K l : T) (hS : head K = S) :
    step [app K l, var 1, var 2, var 3] = some (args K ++ [l, var 2, app (var 1) (var 2), var 3]) := by
  simp [step, head, hS, args]

#print axioms msl_glue
#print axioms msl_main
#print axioms msl_first_step
