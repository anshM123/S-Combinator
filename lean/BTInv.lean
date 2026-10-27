/-
  F5 (Böhm trees are invariant under reduction), on top of confluence, Proposition CF and the head normalisation theorem — machine-checked (main agent, 2026-10-27). Plain Lean 4 core.
  Generated from lean/CF.lean (code/gen_cf.py) and code/std_tail.lean.txt.
  S-terms with variables (opaque atoms). Reduction contracts one redex S x y z anywhere. Confluence is re-proved with
  variables (same proof as lean/Confluence.lean). A term is *head-normal* if its head is a variable, or S with at most
  two spine arguments (no head redex in any spine prefix).
  * `hnf_stable`: reducing a head-normal term keeps its head and arity and reduces the arguments position-wise.
  * `cf_control`: any two head-normal reducts of a term (reached by ANY evaluation orders) have the same head, the same
    number of arguments, and pairwise joinable arguments: which argument (or S) receives control, and with how many
    arguments, does not depend on the evaluation order. (That head reduction finds such a form whenever one exists is
    the standardization theorem, cited, not formalised here.)
-/

inductive T where
  | S : T
  | var : Nat → T
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
  | var (n : Nat) : Par (var n) (var n)
  | app {f f' a a' : T} : Par f f' → Par a a' → Par (app f a) (app f' a')
  | redex {x x' y y' z z' : T} : Par x x' → Par y y' → Par z z' →
      Par (app (app (app S x) y) z) (app (app x' z') (app y' z'))

theorem par_refl : ∀ t : T, Par t t
  | S => Par.S
  | var n => Par.var n
  | app f a => Par.app (par_refl f) (par_refl a)

theorem red_par {t u : T} (h : Red t u) : Par t u := by
  induction h with
  | redex x y z => exact Par.redex (par_refl x) (par_refl y) (par_refl z)
  | left a _ ih => exact Par.app ih (par_refl a)
  | right f _ ih => exact Par.app (par_refl f) ih

theorem par_redstar {t u : T} (h : Par t u) : RedStar t u := by
  induction h with
  | S => exact RedStar.refl _
  | var n => exact RedStar.refl _
  | app _ _ ih1 ih2 => exact redstar_app ih1 ih2
  | redex _ _ _ ihx ihy ihz =>
    exact (redstar_app (redstar_app (redstar_app (RedStar.refl S) ihx) ihy) ihz).trans
      (RedStar.single (Red.redex _ _ _))

/-- complete development: contract every redex of the term at once -/
def cd : T → T
  | S => S
  | var n => var n
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
  | var n => exact Par.var n
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
    | var n, hf, ihf =>
      show Par (app f' a') (app (cd (var n)) (cd a))
      exact Par.app ihf iha
    | app (var n) x, hf, ihf =>
      show Par (app f' a') (app (cd (app (var n) x)) (cd a))
      exact Par.app ihf iha
    | app (app (var n) x) y, hf, ihf =>
      show Par (app f' a') (app (cd (app (app (var n) x) y)) (cd a))
      exact Par.app ihf iha
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


/-! ## Head-normal forms are stable; control is order-independent -/

def args : T → List T
  | S => []
  | var _ => []
  | app f x => args f ++ [x]

def head : T → T
  | S => S
  | var n => var n
  | app f _ => head f

/-- head-normal: head is a variable, or S with at most two arguments -/
def HN (t : T) : Prop := head t ≠ S ∨ (args t).length ≤ 2

/-- position-wise reduction of argument lists -/
inductive Pw : List T → List T → Prop
  | nil : Pw [] []
  | cons {a a' : T} {l l' : List T} : RedStar a a' → Pw l l' → Pw (a :: l) (a' :: l')

theorem pw_refl : ∀ l : List T, Pw l l
  | [] => Pw.nil
  | a :: l => Pw.cons (RedStar.refl a) (pw_refl l)

theorem pw_trans : ∀ {l1 l2 l3 : List T}, Pw l1 l2 → Pw l2 l3 → Pw l1 l3
  | _, _, _, Pw.nil, Pw.nil => Pw.nil
  | _, _, _, Pw.cons h1 p1, Pw.cons h2 p2 => Pw.cons (h1.trans h2) (pw_trans p1 p2)

theorem pw_append : ∀ {l1 l1' l2 l2' : List T}, Pw l1 l1' → Pw l2 l2' → Pw (l1 ++ l2) (l1' ++ l2')
  | _, _, _, _, Pw.nil, p => p
  | _, _, _, _, Pw.cons h p1, p2 => Pw.cons h (pw_append p1 p2)

theorem pw_length : ∀ {l l' : List T}, Pw l l' → l.length = l'.length
  | _, _, Pw.nil => rfl
  | _, _, Pw.cons _ p => by simp [pw_length p]

theorem HN_left {f a : T} (h : HN (app f a)) : HN f := by
  unfold HN at *
  simp only [head, args, List.length_append, List.length_singleton] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- one step from a head-normal term keeps the head and reduces one argument -/
theorem hn_step {t u : T} (hn : HN t) (h : Red t u) : head u = head t ∧ Pw (args t) (args u) := by
  induction h with
  | redex x y z =>
    unfold HN at hn
    simp [head, args] at hn
  | @left f f' a h ih =>
    have ⟨e, p⟩ := ih (HN_left hn)
    refine ⟨by simp only [head]; exact e, ?_⟩
    simp only [args]
    exact pw_append p (pw_refl [a])
  | @right f a a' h _ =>
    refine ⟨rfl, ?_⟩
    simp only [args]
    exact pw_append (pw_refl (args f)) (Pw.cons (RedStar.single h) Pw.nil)

theorem hn_of_pw {t u : T} (hn : HN t) (e : head u = head t) (p : Pw (args t) (args u)) : HN u := by
  unfold HN at *
  rw [e, ← pw_length p]
  exact hn

/-- **Stability.** Reducing a head-normal term keeps its head and arity and reduces its arguments position-wise. -/
theorem hnf_stable {t u : T} (hn : HN t) (h : RedStar t u) : head u = head t ∧ Pw (args t) (args u) := by
  induction h with
  | refl => exact ⟨rfl, pw_refl _⟩
  | tail _ h ih =>
    obtain ⟨e, p⟩ := ih
    obtain ⟨e2, p2⟩ := hn_step (hn_of_pw hn e p) h
    exact ⟨e2.trans e, pw_trans p p2⟩

/-- pairwise joinable argument lists -/
inductive Jw : List T → List T → Prop
  | nil : Jw [] []
  | cons {a b : T} {l m : List T} : (∃ v, RedStar a v ∧ RedStar b v) → Jw l m → Jw (a :: l) (b :: m)

theorem jw_of_pw : ∀ {l1 l2 m : List T}, Pw l1 m → Pw l2 m → Jw l1 l2
  | _, _, _, Pw.nil, Pw.nil => Jw.nil
  | _, _, _, Pw.cons h1 p1, Pw.cons h2 p2 => Jw.cons ⟨_, h1, h2⟩ (jw_of_pw p1 p2)

/-- **Proposition CF (order-independent part).** Any two head-normal reducts of t, reached by any evaluation orders, have
    the same head, the same number of arguments and pairwise joinable arguments. -/
theorem cf_control {t h1 h2 : T} (r1 : RedStar t h1) (r2 : RedStar t h2) (n1 : HN h1) (n2 : HN h2) :
    head h1 = head h2 ∧ (args h1).length = (args h2).length ∧ Jw (args h1) (args h2) := by
  obtain ⟨v, v1, v2⟩ := confluence r1 r2
  obtain ⟨e1, p1⟩ := hnf_stable n1 v1
  obtain ⟨e2, p2⟩ := hnf_stable n2 v2
  exact ⟨e1.symm.trans e2, (pw_length p1).trans (pw_length p2).symm, jw_of_pw p1 p2⟩


/-! ## Head normalisation theorem (standardization for head normal forms) -/

/-- one head step: contract the head redex S x y z (with any further spine arguments) -/
inductive HStep : T → T → Prop
  | redex (x y z : T) : HStep (app (app (app S x) y) z) (app (app x z) (app y z))
  | left {f f' : T} (a : T) : HStep f f' → HStep (app f a) (app f' a)

/-- head reduction, any number of steps (head-first) -/
inductive HStar : T → T → Prop
  | refl (t : T) : HStar t t
  | step {t u v : T} : HStep t u → HStar u v → HStar t v

theorem HStar.trans {t u v : T} (h1 : HStar t u) (h2 : HStar u v) : HStar t v := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact HStar.step h (ih h2)

theorem hstar_left {f f' : T} (a : T) (h : HStar f f') : HStar (app f a) (app f' a) := by
  induction h with
  | refl => exact HStar.refl _
  | step h _ ih => exact HStar.step (HStep.left a h) ih

theorem hstep_red {t u : T} (h : HStep t u) : Red t u := by
  induction h with
  | redex x y z => exact Red.redex x y z
  | left a _ ih => exact Red.left a ih

theorem hstar_redstar {t u : T} (h : HStar t u) : RedStar t u := by
  induction h with
  | refl => exact RedStar.refl _
  | step h _ ih => exact (RedStar.single (hstep_red h)).trans ih

/-- internal parallel reduction: parallel reduction inside the arguments, never the head redex -/
inductive IPar : T → T → Prop
  | S : IPar S S
  | var (n : Nat) : IPar (var n) (var n)
  | app {f f' a a' : T} : IPar f f' → Par a a' → IPar (app f a) (app f' a')

theorem ipar_shape {s u : T} (h : IPar s u) : head s = head u ∧ (args s).length = (args u).length := by
  induction h with
  | S => exact ⟨rfl, rfl⟩
  | var n => exact ⟨rfl, rfl⟩
  | app _ _ ih =>
    simp only [head, args, List.length_append, List.length_singleton]
    exact ⟨ih.1, by rw [ih.2]⟩

theorem ipar_HN {s u : T} (h : IPar s u) (hn : HN u) : HN s := by
  unfold HN at *
  rw [(ipar_shape h).1, (ipar_shape h).2]
  exact hn

/-- decomposition: a parallel step = head steps followed by an internal parallel step -/
theorem par_decomp {t u : T} (h : Par t u) : ∃ t', HStar t t' ∧ IPar t' u := by
  induction h with
  | S => exact ⟨S, HStar.refl _, IPar.S⟩
  | var n => exact ⟨var n, HStar.refl _, IPar.var n⟩
  | @app f f' a a' _ ha ihf _ =>
    obtain ⟨f1, hf1, if1⟩ := ihf
    exact ⟨app f1 a, hstar_left a hf1, IPar.app if1 ha⟩
  | @redex x x' y y' z z' _ hy hz ihx _ _ =>
    obtain ⟨x1, hx1, ix1⟩ := ihx
    refine ⟨app (app x1 z) (app y z), HStar.step (HStep.redex x y z) ?_, ?_⟩
    · exact hstar_left (app y z) (hstar_left z hx1)
    · exact IPar.app (IPar.app ix1 hz) (Par.app hy hz)

/-- postponement: an internal parallel step followed by a head step = a head step followed by a parallel step -/
theorem ipar_hstep {s u u1 : T} (hi : IPar s u) (hh : HStep u u1) : ∃ w, HStep s w ∧ Par w u1 := by
  induction hh generalizing s with
  | redex x' y' z' =>
    cases hi with
    | app h1 hz =>
      cases h1 with
      | app h2 hy =>
        cases h2 with
        | app h3 hx =>
          cases h3
          exact ⟨_, HStep.redex _ _ _, Par.app (Par.app hx hz) (Par.app hy hz)⟩
  | left a' _ ih =>
    cases hi with
    | app hf ha =>
      obtain ⟨w, hw, pw⟩ := ih hf
      exact ⟨app w _, HStep.left _ hw, Par.app pw ha⟩

/-- if u head-normalises and s internally reduces to u, then s head-normalises -/
theorem ipar_hn {u v : T} (h : HStar u v) (hn : HN v) : ∀ s, IPar s u → ∃ s', HStar s s' ∧ HN s' := by
  induction h with
  | refl => intro s hs; exact ⟨s, HStar.refl _, ipar_HN hs hn⟩
  | step hh _ ih =>
    intro s hs
    obtain ⟨w, hw, pw⟩ := ipar_hstep hs hh
    obtain ⟨w', hw', iw'⟩ := par_decomp pw
    obtain ⟨s', hs', hn'⟩ := ih hn w' iw'
    exact ⟨s', HStar.step hw (hw'.trans hs'), hn'⟩

/-- head normalisation is closed under parallel expansion -/
theorem hn_back {t t1 : T} (h : Par t t1) (q : ∃ h1, HStar t1 h1 ∧ HN h1) : ∃ h', HStar t h' ∧ HN h' := by
  obtain ⟨h1, r1, n1⟩ := q
  obtain ⟨t', ht', it'⟩ := par_decomp h
  obtain ⟨s', hs', ns'⟩ := ipar_hn r1 n1 t' it'
  exact ⟨s', ht'.trans hs', ns'⟩

theorem hn_back_star {t u : T} (r : RedStar t u) : (∃ h1, HStar u h1 ∧ HN h1) → ∃ h', HStar t h' ∧ HN h' := by
  induction r with
  | refl => exact id
  | tail _ h ih => exact fun q => ih (hn_back (red_par h) q)

/-- **Head normalisation theorem.** If some reduct of t (any evaluation order) is head-normal, head reduction from t
    reaches a head-normal term. -/
theorem head_normalization {t h : T} (r : RedStar t h) (hn : HN h) : ∃ h', HStar t h' ∧ HN h' :=
  hn_back_star r ⟨h, HStar.refl _, hn⟩

/-- **Proposition CF** (complete): if some evaluation of t reaches a head normal form, head reduction reaches one, and
    every head normal form reachable from t, by any evaluation order, has the same head, the same number of arguments
    and pairwise joinable arguments. -/
theorem cf_full {t h : T} (r : RedStar t h) (hn : HN h) :
    ∃ h', HStar t h' ∧ HN h' ∧ ∀ h2, RedStar t h2 → HN h2 →
      head h' = head h2 ∧ (args h').length = (args h2).length ∧ Jw (args h') (args h2) := by
  obtain ⟨h', r', n'⟩ := head_normalization r hn
  exact ⟨h', r', n', fun h2 r2 n2 => cf_control (hstar_redstar r') r2 n' n2⟩


/-! ## F5: Böhm trees are invariant under reduction (every evaluation order sees the same Böhm tree) -/

/-- t has a head normal form: some reduct is head-normal -/
def HasHN (t : T) : Prop := ∃ h, RedStar t h ∧ HN h

/-- list-wise relation -/
def LRel (R : T → T → Prop) : List T → List T → Prop
  | [], [] => True
  | a :: l, b :: m => R a b ∧ LRel R l m
  | _, _ => False

/-- equal Böhm trees down to depth d: both or neither have a head normal form, and any two head normal forms have the
    same head, the same number of arguments and arguments with equal Böhm trees down to depth d - 1 -/
def BTeq : Nat → T → T → Prop
  | 0, _, _ => True
  | d + 1, t, u => (HasHN t ↔ HasHN u) ∧ ∀ h1 h2, RedStar t h1 → HN h1 → RedStar u h2 → HN h2 →
      head h1 = head h2 ∧ LRel (BTeq d) (args h1) (args h2)

def Joinable (t u : T) : Prop := ∃ v, RedStar t v ∧ RedStar u v

theorem joinable_trans {a b c : T} (h1 : Joinable a b) (h2 : Joinable b c) : Joinable a c := by
  obtain ⟨v1, a1, b1⟩ := h1
  obtain ⟨v2, b2, c2⟩ := h2
  obtain ⟨w, w1, w2⟩ := confluence b1 b2
  exact ⟨w, a1.trans w1, c2.trans w2⟩

theorem lrel_of_pw (R : T → T → Prop) (hR : ∀ a b v, RedStar a v → RedStar b v → R a b) :
    ∀ {l1 l2 m : List T}, Pw l1 m → Pw l2 m → LRel R l1 l2
  | _, _, _, Pw.nil, Pw.nil => trivial
  | _, _, _, Pw.cons h1 p1, Pw.cons h2 p2 => ⟨hR _ _ _ h1 h2, lrel_of_pw R hR p1 p2⟩

theorem hashn_join {t u : T} (j : Joinable t u) (h : HasHN t) : HasHN u := by
  obtain ⟨v, tv, uv⟩ := j
  obtain ⟨h1, th1, n1⟩ := h
  obtain ⟨w, h1w, vw⟩ := confluence th1 tv
  exact ⟨w, uv.trans vw, hn_of_pw n1 (hnf_stable n1 h1w).1 (hnf_stable n1 h1w).2⟩

/-- **F5.** Joinable terms (in particular a term and any of its reducts) have equal Böhm trees to every depth. -/
theorem bt_joinable : ∀ (d : Nat) (t u : T), Joinable t u → BTeq d t u
  | 0, _, _, _ => trivial
  | d + 1, t, u, j => by
    refine ⟨⟨hashn_join j, hashn_join (by obtain ⟨v, a, b⟩ := j; exact ⟨v, b, a⟩)⟩, ?_⟩
    intro h1 h2 th1 n1 uh2 n2
    have j1 : Joinable h1 t := ⟨h1, RedStar.refl _, th1⟩
    have j2 : Joinable u h2 := ⟨h2, uh2, RedStar.refl _⟩
    obtain ⟨w, h1w, h2w⟩ := joinable_trans (joinable_trans j1 j) j2
    obtain ⟨e1, p1⟩ := hnf_stable n1 h1w
    obtain ⟨e2, p2⟩ := hnf_stable n2 h2w
    exact ⟨e1.symm.trans e2, lrel_of_pw (BTeq d) (fun a b v av bv => bt_joinable d a b ⟨v, av, bv⟩) p1 p2⟩

/-- **F5 (reduction form).** Every reduct of t, reached by any evaluation order, has the Böhm tree of t. -/
theorem bt_invariant {t u : T} (r : RedStar t u) (d : Nat) : BTeq d t u :=
  bt_joinable d t u ⟨u, r, RedStar.refl _⟩

#print axioms bt_invariant
