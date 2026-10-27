/-
  Confluence of S-reduction and Proposition MW(d),(e) — machine-checked (main agent, 2026-10-27). Plain Lean 4 core.
  Reduction contracts one redex S x y z anywhere (as in lean/MW.lean). Proof of Church–Rosser by parallel reduction and
  Takahashi's complete development.
  * `confluence`: any two reducts of a term have a common reduct (the multiway system of S is confluent).
  * `nf_unique`: a term has at most one normal form.
  * `mw_e` (Proposition MW(e)): if a decoder maps reducts to configurations of a system M, respects reachability and is
    defined cofinally, then any two decoded configurations reachable from one start have a common M-descendant; so two
    distinct terminal configurations (e.g. accepting and rejecting halts) can never both be decoded.
-/

inductive T where
  | S : T
  | app : T → T → T
deriving DecidableEq, Repr

open T

inductive Red : T → T → Prop
  | redex (x y z : T) : Red (app (app (app S x) y) z) (app (app x z) (app y z))
  | left {f f' : T} (a : T) : Red f f' → Red (app f a) (app f' a)
  | right (f : T) {a a' : T} : Red a a' → Red (app f a) (app f a')

inductive RedStar : T → T → Prop
  | refl (t : T) : RedStar t t
  | tail {t u v : T} : RedStar t u → Red u v → RedStar t v

theorem RedStar.trans {t u v : T} (h1 : RedStar t u) (h2 : RedStar u v) : RedStar t v := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact RedStar.tail ih h

theorem RedStar.single {t u : T} (h : Red t u) : RedStar t u := RedStar.tail (RedStar.refl t) h

theorem redstar_left {f f' : T} (a : T) (h : RedStar f f') : RedStar (app f a) (app f' a) := by
  induction h with
  | refl => exact RedStar.refl _
  | tail _ h ih => exact RedStar.tail ih (Red.left a h)

theorem redstar_right (f : T) {a a' : T} (h : RedStar a a') : RedStar (app f a) (app f a') := by
  induction h with
  | refl => exact RedStar.refl _
  | tail _ h ih => exact RedStar.tail ih (Red.right f h)

theorem redstar_app {f f' a a' : T} (h1 : RedStar f f') (h2 : RedStar a a') : RedStar (app f a) (app f' a') :=
  (redstar_left a h1).trans (redstar_right f' h2)

/-- parallel reduction -/
inductive Par : T → T → Prop
  | S : Par S S
  | app {f f' a a' : T} : Par f f' → Par a a' → Par (app f a) (app f' a')
  | redex {x x' y y' z z' : T} : Par x x' → Par y y' → Par z z' →
      Par (app (app (app S x) y) z) (app (app x' z') (app y' z'))

theorem par_refl : ∀ t : T, Par t t
  | S => Par.S
  | app f a => Par.app (par_refl f) (par_refl a)

theorem red_par {t u : T} (h : Red t u) : Par t u := by
  induction h with
  | redex x y z => exact Par.redex (par_refl x) (par_refl y) (par_refl z)
  | left a _ ih => exact Par.app ih (par_refl a)
  | right f _ ih => exact Par.app (par_refl f) ih

theorem par_redstar {t u : T} (h : Par t u) : RedStar t u := by
  induction h with
  | S => exact RedStar.refl _
  | app _ _ ih1 ih2 => exact redstar_app ih1 ih2
  | redex _ _ _ ihx ihy ihz =>
    exact (redstar_app (redstar_app (redstar_app (RedStar.refl S) ihx) ihy) ihz).trans
      (RedStar.single (Red.redex _ _ _))

/-- complete development: contract every redex of the term at once -/
def cd : T → T
  | S => S
  | app (app (app S x) y) a => app (app (cd x) (cd a)) (app (cd y) (cd a))
  | app f a => app (cd f) (cd a)

/-- inversion: parallel reducts of S·x and S·x·y -/
theorem par_Sx {x u : T} (h : Par (app S x) u) : ∃ x', u = app S x' ∧ Par x x' := by
  cases h with
  | app h1 h2 => cases h1; exact ⟨_, rfl, h2⟩

theorem par_Sxy {x y u : T} (h : Par (app (app S x) y) u) : ∃ x' y', u = app (app S x') y' ∧ Par x x' ∧ Par y y' := by
  cases h with
  | app h1 h2 =>
    obtain ⟨x', rfl, hx⟩ := par_Sx h1
    exact ⟨x', _, rfl, hx, h2⟩

/-- Takahashi's lemma: every parallel reduct reduces in parallel to the complete development -/
theorem par_cd {t u : T} (h : Par t u) : Par u (cd t) := by
  induction h with
  | S => exact Par.S
  | @app f f' a a' hf ha ihf iha =>
    match f, hf, ihf with
    | app (app S x) y, hf, ihf =>
      obtain ⟨x', y', rfl, hx, hy⟩ := par_Sxy hf
      have e : cd (app (app S x) y) = app (app S (cd x)) (cd y) := rfl
      rw [e] at ihf
      obtain ⟨x'', y'', h3, hx'', hy''⟩ := par_Sxy ihf
      simp only [app.injEq] at h3
      obtain ⟨⟨_, rfl⟩, rfl⟩ := h3
      show Par (app (app (app S x') y') a') (app (app (cd x) (cd a)) (app (cd y) (cd a)))
      exact Par.redex hx'' hy'' iha
    | S, hf, ihf =>
      cases hf
      show Par (app S a') (app S (cd a))
      exact Par.app Par.S iha
    | app S x, hf, ihf =>
      show Par (app f' a') (app (cd (app S x)) (cd a))
      exact Par.app ihf iha
    | app (app (app p q) r) y, hf, ihf =>
      show Par (app f' a') (app (cd (app (app (app p q) r) y)) (cd a))
      exact Par.app ihf iha
  | @redex x x' y y' z z' _ _ _ ihx ihy ihz =>
    show Par (app (app x' z') (app y' z')) (app (app (cd x) (cd z)) (app (cd y) (cd z)))
    exact Par.app (Par.app ihx ihz) (Par.app ihy ihz)

theorem par_diamond {t u1 u2 : T} (h1 : Par t u1) (h2 : Par t u2) : ∃ v, Par u1 v ∧ Par u2 v :=
  ⟨cd t, par_cd h1, par_cd h2⟩

/-- strip lemma for parallel reduction against many single steps -/
theorem strip {t u1 u2 : T} (h1 : Par t u1) (h2 : RedStar t u2) : ∃ v, RedStar u1 v ∧ Par u2 v := by
  induction h2 generalizing u1 with
  | refl => exact ⟨u1, RedStar.refl _, h1⟩
  | tail _ h ih =>
    obtain ⟨v, hv1, hv2⟩ := ih h1
    obtain ⟨w, hw1, hw2⟩ := par_diamond hv2 (red_par h)
    exact ⟨w, hv1.trans (par_redstar hw1), hw2⟩

/-- **Confluence** (Church–Rosser for S-reduction): any two reducts have a common reduct -/
theorem confluence {t u1 u2 : T} (h1 : RedStar t u1) (h2 : RedStar t u2) : ∃ v, RedStar u1 v ∧ RedStar u2 v := by
  induction h1 generalizing u2 with
  | refl => exact ⟨u2, h2, RedStar.refl _⟩
  | tail _ h ih =>
    obtain ⟨v, hv1, hv2⟩ := ih h2
    obtain ⟨w, hw1, hw2⟩ := strip (red_par h) hv1
    exact ⟨w, hw1, hv2.trans (par_redstar hw2)⟩

/-- normal form: no redex anywhere -/
def NF (t : T) : Prop := ∀ u, ¬ Red t u

theorem nf_redstar {t u : T} (hn : NF t) (h : RedStar t u) : u = t := by
  induction h with
  | refl => rfl
  | tail _ h ih => subst ih; exact absurd h (hn _)

/-- a term has at most one normal form -/
theorem nf_unique {t u1 u2 : T} (h1 : RedStar t u1) (h2 : RedStar t u2) (n1 : NF u1) (n2 : NF u2) : u1 = u2 := by
  obtain ⟨v, hv1, hv2⟩ := confluence h1 h2
  rw [nf_redstar n1 hv1] at hv2
  exact nf_redstar n2 hv2

/-- **Proposition MW(e).** Let `Dec` decode some terms into configurations of a system M with reachability `RM` (any
    reflexive-transitive relation), respecting reachability, and defined on a cofinal set of the reducts of t. Then any
    two decoded configurations reachable from t have a common M-descendant. -/
theorem mw_e {M : Type} (RM : M → M → Prop) (htrans : ∀ a b c, RM a b → RM b c → RM a c)
    (Dec : T → Option M) (t : T)
    (hresp : ∀ u v c d, RedStar t u → RedStar u v → Dec u = some c → Dec v = some d → RM c d)
    (hcof : ∀ u, RedStar t u → ∃ w, RedStar u w ∧ (Dec w).isSome = true)
    (u1 u2 : T) (c1 c2 : M) (h1 : RedStar t u1) (h2 : RedStar t u2) (d1 : Dec u1 = some c1) (d2 : Dec u2 = some c2) :
    ∃ e, RM c1 e ∧ RM c2 e := by
  obtain ⟨w, hw1, hw2⟩ := confluence h1 h2
  obtain ⟨w', hw', hs⟩ := hcof w (h1.trans hw1)
  cases hd : Dec w' with
  | none => rw [hd] at hs; simp at hs
  | some e =>
    exact ⟨e, hresp u1 w' c1 e h1 (hw1.trans hw') d1 hd, hresp u2 w' c2 e h2 (hw2.trans hw') d2 hd⟩

/-- **Corollary.** Under the hypotheses of `mw_e`, two terminal configurations (no proper M-descendants) that are both
    decoded from reducts of t are equal: a nondeterministic machine with two different halting outcomes from one input
    cannot be emulated in this sense. -/
theorem mw_e_terminal {M : Type} (RM : M → M → Prop) (htrans : ∀ a b c, RM a b → RM b c → RM a c)
    (Dec : T → Option M) (t : T)
    (hresp : ∀ u v c d, RedStar t u → RedStar u v → Dec u = some c → Dec v = some d → RM c d)
    (hcof : ∀ u, RedStar t u → ∃ w, RedStar u w ∧ (Dec w).isSome = true)
    (u1 u2 : T) (c1 c2 : M) (h1 : RedStar t u1) (h2 : RedStar t u2) (d1 : Dec u1 = some c1) (d2 : Dec u2 = some c2)
    (term1 : ∀ e, RM c1 e → e = c1) (term2 : ∀ e, RM c2 e → e = c2) : c1 = c2 := by
  obtain ⟨e, he1, he2⟩ := mw_e RM htrans Dec t hresp hcof u1 u2 c1 c2 h1 h2 d1 d2
  rw [← term1 e he1, ← term2 e he2]

#print axioms confluence
#print axioms nf_unique
#print axioms mw_e_terminal
