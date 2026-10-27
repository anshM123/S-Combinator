/-
  agent_work/lean/AB.lean  (non-universality agent, 2026-10-27).  Lemma AB (absorbing P-count) on top of SL.lean's definitions.  Plain Lean 4 core, no Mathlib.
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

#print axioms ab_no_glue
#print axioms ab_run
