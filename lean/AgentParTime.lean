/-
  Proposition CF and the head normalisation theorem — machine-checked (main agent, 2026-10-27). Plain Lean 4 core.
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


/-! ## Theorem PT (agent_work_P, parallel-universality agent, 2026-10-27)

A ReplaceAll run is the head (leftmost-outermost) run sampled at increasing times, with every spine element reduced.
`pass` is one ReplaceAll pass, Mathematica's  expr /. S[x_][y_][z_] :> x[z][y[z]] : the rule is tried at the root first;
a matched redex is replaced and its instantiated x, y, z are not entered; otherwise the pass recurses into function and
argument.  `passN n t` is the term after n passes.

* `pass_head_step`: if t is not head-normal, t →h u in ONE head step and u reduces to `pass t` by an internal parallel step.
* `pass_HN`: if t is head-normal, `pass t` is an internal parallel reduct of t.
* `commute_one`, `commute_star`: internal reductions can be postponed past head steps without losing head steps.
* `parallel_time_change` / `theoremPT`: for every n there is k and the k-th head reduct w of t (head reduction is
  deterministic: `hstepN_det`) such that `passN n t` has the same head and the same number of spine arguments as w, its
  spine arguments are position-wise reducts of w's, and k ≥ n as long as passN j t is not head-normal for j < n.
-/

/-- one ReplaceAll pass -/
def pass : T → T
  | S => S
  | var n => var n
  | app (app (app S x) y) a => app (app x a) (app y a)
  | app f a => app (pass f) (pass a)

def passN : Nat → T → T
  | 0, t => t
  | n + 1, t => pass (passN n t)

theorem pass_app (f a : T) (h : ∀ x y, f ≠ app (app S x) y) : pass (app f a) = app (pass f) (pass a) := by
  match f, h with
  | S, _ => rfl
  | var n, _ => rfl
  | app S x, _ => rfl
  | app (var n) x, _ => rfl
  | app (app S x) y, h => exact absurd rfl (h x y)
  | app (app (var n) x) y, _ => rfl
  | app (app (app p q) r) y, _ => rfl

theorem ipar_refl : ∀ t : T, IPar t t
  | S => IPar.S
  | var n => IPar.var n
  | app f a => IPar.app (ipar_refl f) (par_refl a)

/-- a pass is a parallel reduction step -/
theorem par_pass : ∀ t : T, Par t (pass t)
  | S => Par.S
  | var n => Par.var n
  | app f a => by
    by_cases hr : ∃ x y, f = app (app S x) y
    · obtain ⟨x, y, rfl⟩ := hr
      exact Par.redex (par_refl x) (par_refl y) (par_refl a)
    · have hr' : ∀ x y, f ≠ app (app S x) y := fun x y e => hr ⟨x, y, e⟩
      rw [pass_app f a hr']
      exact Par.app (par_pass f) (par_pass a)

theorem head_S_args0 : ∀ t : T, head t = S → (args t).length = 0 → t = S
  | S, _, _ => rfl
  | var n, h, _ => by simp [head] at h
  | app f a, _, h => by simp [args] at h

theorem head_S_args2 (f : T) (hS : head f = S) (h2 : (args f).length = 2) : ∃ x y, f = app (app S x) y := by
  match f, hS, h2 with
  | S, _, h2 => simp [args] at h2
  | var n, hS, _ => simp [head] at hS
  | app S y, _, h2 => simp [args] at h2
  | app (var n) y, hS, _ => simp [head] at hS
  | app (app g x) y, hS, h2 =>
    have hg : g = S := head_S_args0 g hS (by
      simp only [args, List.length_append, List.length_singleton] at h2; omega)
    exact ⟨x, y, by rw [hg]⟩

/-- one pass on a term with a head redex = one head step, then an internal parallel step -/
theorem pass_head_step : ∀ t : T, ¬ HN t → ∃ u, HStep t u ∧ IPar u (pass t)
  | S, h => absurd (Or.inr (by simp [args])) h
  | var n, h => absurd (Or.inl (by simp [head])) h
  | app f a, h => by
    by_cases hr : ∃ x y, f = app (app S x) y
    · obtain ⟨x, y, rfl⟩ := hr
      exact ⟨_, HStep.redex x y a, ipar_refl _⟩
    · have hr' : ∀ x y, f ≠ app (app S x) y := fun x y e => hr ⟨x, y, e⟩
      have hS : head f = S := Classical.byContradiction fun hc => h (Or.inl hc)
      have hlen : 2 ≤ (args f).length := by
        apply Classical.byContradiction
        intro hc
        apply h
        apply Or.inr
        simp only [args, List.length_append, List.length_singleton]
        omega
      have hf : ¬ HN f := by
        intro hnf
        rcases hnf with hnf | hnf
        · exact hnf hS
        · obtain ⟨x, y, e⟩ := head_S_args2 f hS (by omega)
          exact hr' x y e
      obtain ⟨u, hu, iu⟩ := pass_head_step f hf
      refine ⟨app u a, HStep.left a hu, ?_⟩
      rw [pass_app f a hr']
      exact IPar.app iu (par_pass a)

/-- on a head-normal term a pass is an internal parallel step -/
theorem pass_HN : ∀ t : T, HN t → IPar t (pass t)
  | S, _ => IPar.S
  | var n, _ => IPar.var n
  | app f a, h => by
    by_cases hr : ∃ x y, f = app (app S x) y
    · obtain ⟨x, y, rfl⟩ := hr
      exfalso
      rcases h with h | h
      · exact h rfl
      · simp [args] at h
    · have hr' : ∀ x y, f ≠ app (app S x) y := fun x y e => hr ⟨x, y, e⟩
      rw [pass_app f a hr']
      exact IPar.app (pass_HN f (HN_left h)) (par_pass a)

/-- head reduction with a step count -/
inductive HStepN : Nat → T → T → Prop
  | zero (t : T) : HStepN 0 t t
  | succ {k : Nat} {t u v : T} : HStep t u → HStepN k u v → HStepN (k + 1) t v

theorem hstepN_trans {a b : Nat} {t s w : T} (h1 : HStepN a t s) (h2 : HStepN b s w) : HStepN (a + b) t w := by
  revert h2
  induction h1 with
  | zero => intro h2; rw [Nat.zero_add]; exact h2
  | @succ k t0 u0 v0 h _ ih =>
    intro h2
    have := HStepN.succ h (ih h2)
    rw [show k + 1 + b = k + b + 1 by omega]
    exact this

theorem hstar_count {t u : T} (h : HStar t u) : ∃ k, HStepN k t u := by
  induction h with
  | refl => exact ⟨0, HStepN.zero _⟩
  | step h _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, HStepN.succ h hk⟩

/-- internal parallel steps, iterated -/
inductive IStar : T → T → Prop
  | refl (t : T) : IStar t t
  | tail {t u v : T} : IStar t u → IPar u v → IStar t v

/-- postponement with counting: an internal parallel step followed by k head steps = at least k head steps followed by
    an internal parallel step -/
theorem commute_one {k : Nat} {u v : T} (hk : HStepN k u v) :
    ∀ s, IPar s u → ∃ k', k ≤ k' ∧ ∃ w, HStepN k' s w ∧ IPar w v := by
  induction hk with
  | zero t => intro s hs; exact ⟨0, Nat.le_refl 0, s, HStepN.zero s, hs⟩
  | @succ k u0 u1 v0 hh _ ih =>
    intro s hs
    obtain ⟨w0, hw0, pw0⟩ := ipar_hstep hs hh
    obtain ⟨w1, hw1, iw1⟩ := par_decomp pw0
    obtain ⟨j, hj⟩ := hstar_count hw1
    obtain ⟨k', hk', w, hw, iw⟩ := ih w1 iw1
    refine ⟨j + k' + 1, by omega, w, ?_, iw⟩
    exact HStepN.succ hw0 (hstepN_trans hj hw)

theorem commute_star {s u : T} (hi : IStar s u) :
    ∀ k v, HStepN k u v → ∃ k', k ≤ k' ∧ ∃ w, HStepN k' s w ∧ IStar w v := by
  induction hi with
  | refl => intro k v hk; exact ⟨k, Nat.le_refl k, v, hk, IStar.refl v⟩
  | @tail u0 u1 _ iuu ih =>
    intro k v hk
    obtain ⟨k1, hk1, w1, hw1, iw1⟩ := commute_one hk u0 iuu
    obtain ⟨k2, hk2, w, hw, iw⟩ := ih k1 w1 hw1
    exact ⟨k2, by omega, w, hw, IStar.tail iw iw1⟩

/-- the ReplaceAll run, related to the head run: after n passes the term is an iterated internal parallel reduct of
    the k-th head reduct, and k ≥ n while the run has not reached a head normal form -/
theorem parallel_time_change (t : T) : ∀ n : Nat, ∃ k w, HStepN k t w ∧ IStar w (passN n t) ∧
    ((∀ j, j < n → ¬ HN (passN j t)) → n ≤ k)
  | 0 => ⟨0, t, HStepN.zero t, IStar.refl t, fun _ => Nat.le_refl 0⟩
  | n + 1 => by
    obtain ⟨k, w, hw, iw, hc⟩ := parallel_time_change t n
    by_cases hn : HN (passN n t)
    · refine ⟨k, w, hw, IStar.tail iw (pass_HN _ hn), ?_⟩
      intro hall
      exact absurd hn (hall n (Nat.lt_succ_self n))
    · obtain ⟨u1, hu1, iu1⟩ := pass_head_step _ hn
      obtain ⟨k', hk', w', hw', iw'⟩ := commute_star iw 1 u1 (HStepN.succ hu1 (HStepN.zero u1))
      refine ⟨k + k', w', hstepN_trans hw hw', IStar.tail iw' iu1, ?_⟩
      intro hall
      have := hc (fun j hj => hall j (by omega))
      omega

theorem ipar_pw {s u : T} (h : IPar s u) : head s = head u ∧ Pw (args s) (args u) := by
  induction h with
  | S => exact ⟨rfl, Pw.nil⟩
  | var n => exact ⟨rfl, Pw.nil⟩
  | app _ ha ih => exact ⟨ih.1, pw_append ih.2 (Pw.cons (par_redstar ha) Pw.nil)⟩

theorem istar_pw {s u : T} (h : IStar s u) : head s = head u ∧ Pw (args s) (args u) := by
  induction h with
  | refl => exact ⟨rfl, pw_refl _⟩
  | tail _ hi ih =>
    obtain ⟨e2, p2⟩ := ipar_pw hi
    exact ⟨ih.1.trans e2, pw_trans ih.2 p2⟩

/-- head reduction is deterministic, so the w of Theorem PT is THE k-th head reduct of t -/
theorem hstep_det {t u u' : T} (h : HStep t u) (h' : HStep t u') : u = u' := by
  induction h generalizing u' with
  | redex x y z =>
    cases h' with
    | redex => rfl
    | left _ h2 =>
      cases h2 with
      | left _ h3 => cases h3 with | left _ h4 => cases h4
  | left a h ih =>
    cases h' with
    | redex x y z => cases h with | left _ h3 => cases h3 with | left _ h4 => cases h4
    | left _ h2 => rw [ih h2]

theorem hstepN_det {k : Nat} {t w w' : T} (h : HStepN k t w) (h' : HStepN k t w') : w = w' := by
  induction h generalizing w' with
  | zero => cases h'; rfl
  | succ hh _ ih =>
    cases h' with
    | succ hh' h2 =>
      rw [hstep_det hh hh'] at ih
      exact ih h2

/-- **Theorem PT.** After n ReplaceAll passes, the term has the same head and the same number of spine arguments as the
    k-th head (leftmost-outermost) reduct w of t, its spine arguments are position-wise reducts of w's, and k ≥ n as
    long as no earlier pass reached a head normal form. -/
theorem theoremPT (t : T) (n : Nat) : ∃ k w, HStepN k t w ∧ head w = head (passN n t) ∧
    Pw (args w) (args (passN n t)) ∧ ((∀ j, j < n → ¬ HN (passN j t)) → n ≤ k) := by
  obtain ⟨k, w, hw, iw, hc⟩ := parallel_time_change t n
  obtain ⟨e, p⟩ := istar_pw iw
  exact ⟨k, w, hw, e, p, hc⟩

#print axioms par_pass
#print axioms pass_head_step
#print axioms parallel_time_change
#print axioms hstepN_det
#print axioms theoremPT

/-! ## Lemma LZ (prefix form) and Lemma PJ (process lemma: the max-plus law) for ReplaceAll
    (agent_work_P, 2026-10-27)

A list [e1, ..., em] stands for the term S e1 ... em, i.e. `(es.foldl app S)`.  More generally `R.foldl app u` is the
term u applied to the further arguments R.
* `pass_ext` (Lemma LZ (i), one pass): if u has head S and at least 3 spine arguments, a pass on u r1 ... rk is the pass
  on u followed by the arguments, each passed once: below the head window every element ages by exactly one pass.
* `passN_ext` (iterated): as long as u's own run has not reached a head normal form, j passes on u R⃗ are j passes of
  u's own run with every element of R⃗ aged j times — the waiting elements evolve autonomously.
* `lemmaPJ` (process lemma): if the list is [P^w(x0), r1, r2] ++ R and x0's own run is not head-normal at internal
  times w, ..., w + j - 1, then after 1 + j passes the term is P^(w+j)(x0) applied to P^j(r2), P^j(r1 r2) and
  P^(1+j)(r) for r in R.  With h = the first time x0's own run is head-normal and j = max(0, h - w): the head normal
  form of x0 reaches the front 1 + max(0, h - w) passes after x is opened, i.e. at 1 + max(T, b + h) where T is the
  opening pass and b = T - w the pass at which x0 began to wait.  Opening a waiting element is a max (join with its own
  clock); the head machine without aging (leftmost-outermost) needs h_LO(x0) more steps, a sum.
-/

theorem passN_add (t : T) (a : Nat) : ∀ b : Nat, passN (a + b) t = passN b (passN a t)
  | 0 => rfl
  | b + 1 => by
    show pass (passN (a + b) t) = pass (passN b (passN a t))
    rw [passN_add t a b]

theorem foldl_app_shape (u : T) : ∀ R : List T, args (R.foldl app u) = args u ++ R ∧ head (R.foldl app u) = head u
  | [] => by simp
  | r :: R => by
    have ih := foldl_app_shape (app u r) R
    simp only [List.foldl_cons]
    refine ⟨?_, ?_⟩
    · rw [ih.1]; simp [args]
    · rw [ih.2]; rfl

/-- Lemma LZ (i), one pass, with the waiting arguments: they are passed exactly once -/
theorem pass_ext (u : T) (hS : head u = S) (h3 : 3 ≤ (args u).length) :
    ∀ R : List T, pass (R.foldl app u) = (R.map pass).foldl app (pass u) := by
  intro R
  induction R generalizing u with
  | nil => rfl
  | cons r R ih =>
    show pass (R.foldl app (app u r)) = (R.map pass).foldl app (app (pass u) (pass r))
    have hne : ∀ x y, u ≠ app (app S x) y := by
      intro x y e
      subst e
      simp [args] at h3
    have h3' : 3 ≤ (args (app u r)).length := by
      simp only [args, List.length_append, List.length_singleton]
      omega
    rw [ih (app u r) hS h3', pass_app u r hne]

theorem map_passN_zero : ∀ R : List T, R.map (passN 0) = R
  | [] => rfl
  | r :: R => by
    show passN 0 r :: R.map (passN 0) = r :: R
    rw [map_passN_zero R]
    rfl

/-- iterated: while u's own run is not head-normal, the waiting arguments age autonomously -/
theorem passN_ext (u : T) (R : List T) : ∀ j : Nat, (∀ i, i < j → ¬ HN (passN i u)) →
    passN j (R.foldl app u) = (R.map (passN j)).foldl app (passN j u)
  | 0, _ => by
    show R.foldl app u = (R.map (passN 0)).foldl app u
    rw [map_passN_zero R]
  | j + 1, h => by
    show pass (passN j (R.foldl app u)) = (R.map (passN (j + 1))).foldl app (pass (passN j u))
    rw [passN_ext u R j (fun i hi => h i (by omega))]
    have hj := h j (by omega)
    have hS : head (passN j u) = S := Classical.byContradiction fun hc => hj (Or.inl hc)
    have h3 : 3 ≤ (args (passN j u)).length :=
      Classical.byContradiction fun hc => hj (Or.inr (by omega))
    rw [pass_ext _ hS h3, List.map_map]
    rfl

/-- **Lemma PJ** (process lemma, the max-plus law of ReplaceAll evaluation) -/
theorem lemmaPJ (x0 r1 r2 : T) (R : List T) (w j : Nat)
    (hrun : ∀ i, i < j → ¬ HN (passN (w + i) x0)) :
    passN (1 + j) (R.foldl app (app (app (app S (passN w x0)) r1) r2)) =
      ((passN j r2 :: passN j (app r1 r2) :: R.map (passN (1 + j))).foldl app (passN (w + j) x0)) := by
  -- the opening pass
  have h1 : passN 1 (R.foldl app (app (app (app S (passN w x0)) r1) r2)) =
      ((r2 :: app r1 r2 :: R.map pass).foldl app (passN w x0)) := by
    show pass (R.foldl app (app (app (app S (passN w x0)) r1) r2)) = _
    rw [pass_ext _ rfl (by simp [args])]
    rfl
  rw [passN_add _ 1 j, h1]
  -- x0's own run continues for j passes, everything below ages
  have hrun' : ∀ i, i < j → ¬ HN (passN i (passN w x0)) := by
    intro i hi
    rw [← passN_add x0 w i]
    exact hrun i hi
  rw [passN_ext (passN w x0) _ j hrun', ← passN_add x0 w j]
  simp only [List.map_cons, List.map_map]
  have hm : R.map (passN j ∘ pass) = R.map (passN (1 + j)) := by
    apply List.map_congr_left
    intro r _
    show passN j (pass r) = passN (1 + j) r
    rw [passN_add r 1 j]
    rfl
  rw [hm]

#print axioms passN_ext
#print axioms lemmaPJ

/-! ## Corollary PT-V: data placement is the same in every evaluation order (agent_work_P, 2026-10-27)

Data are opaque variables.  S-reduction neither erases nor creates variables, so a reduct of a list element contains
exactly the same data as the element.  With Theorem PT: after n ReplaceAll passes, the i-th list element contains
datum v iff the i-th list element of the head run at the sampled time σ(n) = k does.  So whatever combination of data
(which data share an element, in which list order) occurs under ReplaceAll already occurs in the leftmost-outermost
head run at the sampled time; the clock channel cannot put data together that the head run keeps apart.
-/

def occ (v : Nat) : T → Bool
  | S => false
  | var n => n == v
  | app f a => occ v f || occ v a

theorem red_occ {t u : T} (h : Red t u) (v : Nat) : occ v u = occ v t := by
  induction h with
  | redex x y z =>
    simp only [occ]
    generalize occ v x = a
    generalize occ v y = b
    generalize occ v z = c
    cases a <;> cases b <;> cases c <;> rfl
  | left a _ ih => simp only [occ, ih]
  | right f _ ih => simp only [occ, ih]

theorem redstar_occ {t u : T} (h : RedStar t u) (v : Nat) : occ v u = occ v t := by
  induction h with
  | refl => rfl
  | tail _ h ih => rw [red_occ h v, ih]

theorem pw_occ {L L' : List T} (h : Pw L L') (v : Nat) : L.map (occ v) = L'.map (occ v) := by
  induction h with
  | nil => rfl
  | cons ha _ ih => simp only [List.map_cons, redstar_occ ha v, ih]

/-- **Corollary PT-V.** After n ReplaceAll passes the list has the length and head of the head run's list at the
    sampled time k, and position by position the same data. -/
theorem corollaryPT_data (t : T) (n : Nat) : ∃ k w, HStepN k t w ∧ head w = head (passN n t) ∧
    (args w).length = (args (passN n t)).length ∧
    (∀ v, (args w).map (occ v) = (args (passN n t)).map (occ v)) ∧
    ((∀ j, j < n → ¬ HN (passN j t)) → n ≤ k) := by
  obtain ⟨k, w, hw, e, p, hc⟩ := theoremPT t n
  exact ⟨k, w, hw, e, pw_length p, fun v => pw_occ p v, hc⟩

#print axioms corollaryPT_data

/-! ## Corollary PT-F: ReplaceAll reaches a head normal form no later than leftmost-outermost (agent_work_P, 2026-10-27)

If the head (leftmost-outermost) run of t reaches a head-normal term after h steps, then some ReplaceAll iterate
passN n t with n ≤ h is head-normal.  (With Theorem PT: k ≥ n head steps are done by pass n while no hnf has been
reached; head reduction is deterministic and stops at a head-normal term.)  So h_par(t) ≤ h_LO(t): opening a waiting
element costs at most what leftmost-outermost pays (Lemma PJ: max instead of sum).
-/

theorem HN_no_hstep {t u : T} (hn : HN t) (h : HStep t u) : False := by
  induction h with
  | redex x y z =>
    rcases hn with hn | hn
    · exact hn rfl
    · simp [args] at hn
  | left a _ ih => exact ih (HN_left hn)

/-- k head steps from t can be split at any h ≤ k -/
theorem hstepN_split : ∀ (h k : Nat) {t w : T}, h ≤ k → HStepN k t w → ∃ v, HStepN h t v ∧ HStepN (k - h) v w
  | 0, k, t, w, _, hk => ⟨t, HStepN.zero t, by simpa using hk⟩
  | h + 1, 0, t, w, hle, _ => absurd hle (by omega)
  | h + 1, k + 1, t, w, hle, hk => by
    cases hk with
    | succ hs hk' =>
      obtain ⟨v, hv1, hv2⟩ := hstepN_split h k (by omega) hk'
      exact ⟨v, HStepN.succ hs hv1, by simpa using hv2⟩

theorem corollaryPT_fast (t w : T) (h : Nat) (hw : HStepN h t w) (hn : HN w) :
    ∃ n, n ≤ h ∧ HN (passN n t) := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ j, j < h + 1 → ¬ HN (passN j t) := by
    intro j hj hj'
    exact hno ⟨j, by omega, hj'⟩
  obtain ⟨k, w', hk, _, hc⟩ := parallel_time_change t (h + 1)
  have hk1 := hc hall
  obtain ⟨v, hv1, hv2⟩ := hstepN_split h k (by omega) hk
  have hvw : v = w := hstepN_det hv1 hw
  subst hvw
  obtain ⟨j, hj⟩ : ∃ j, k - h = j + 1 := ⟨k - h - 1, by omega⟩
  rw [hj] at hv2
  cases hv2 with
  | succ hs _ => exact HN_no_hstep hn hs

#print axioms corollaryPT_fast

/-! ## Theorem PT-all: every evaluation order is a head run followed by internal reductions (agent_work_P, 2026-10-27)

Head factorisation of arbitrary reductions: for every reduction sequence t →* u (any evaluation order, any path of the
multiway system) there are k and the k-th head reduct w of t such that u is an iterated internal parallel reduct of w.
So u has the head and the spine length of the head-run state w, its spine arguments are position-wise reducts of w's,
and it holds the same data at the same positions.  Theorem PT is the ReplaceAll case with the extra bound k ≥ n.
-/

theorem factorization {t u : T} (h : RedStar t u) : ∃ k w, HStepN k t w ∧ IStar w u := by
  induction h with
  | refl => exact ⟨0, t, HStepN.zero t, IStar.refl t⟩
  | @tail u0 v0 _ hr ih =>
    obtain ⟨k, w, hw, iw⟩ := ih
    obtain ⟨u1, hu1, iu1⟩ := par_decomp (red_par hr)
    obtain ⟨j, hj⟩ := hstar_count hu1
    obtain ⟨k', _, w', hw', iw'⟩ := commute_star iw j u1 hj
    exact ⟨k + k', w', hstepN_trans hw hw', IStar.tail iw' iu1⟩

/-- **Theorem PT-all.** Any state u reachable from t by any reduction sequence has the head, the spine length and the
    position-wise data of some leftmost-outermost head-run state w of t, and its spine arguments are position-wise
    reducts of w's. -/
theorem theoremPT_all {t u : T} (h : RedStar t u) : ∃ k w, HStepN k t w ∧ head w = head u ∧
    (args w).length = (args u).length ∧ Pw (args w) (args u) ∧ (∀ v, (args w).map (occ v) = (args u).map (occ v)) := by
  obtain ⟨k, w, hw, iw⟩ := factorization h
  obtain ⟨e, p⟩ := istar_pw iw
  exact ⟨k, w, hw, e, pw_length p, p, fun v => pw_occ p v⟩

#print axioms theoremPT_all

/-! ## Transfer principle (agent_work_P, 2026-10-27)

The *data signature* of a state is its head together with, for every spine position, the set of data (variables) the
element at that position contains.  Every property of data signatures that holds for all leftmost-outermost head-run
states of t holds for every state reachable from t by ANY reduction sequence (every evaluation order, ReplaceAll, the
multiway system).  So head-run barriers about which data sit where (data counts, which data share an element, their
order, closed material below data) are barriers for every evaluation order.
-/

def dsig (u : T) : T × List (Nat → Bool) := (head u, (args u).map (fun e => fun v => occ v e))

theorem pw_dsig {L L' : List T} (h : Pw L L') :
    L.map (fun e => fun v => occ v e) = L'.map (fun e => fun v => occ v e) := by
  induction h with
  | nil => rfl
  | @cons a a' l l' ha _ ih =>
    simp only [List.map_cons, ih]
    congr 1
    funext v
    exact (redstar_occ ha v).symm

theorem transfer_principle {t u : T} (Q : T × List (Nat → Bool) → Prop)
    (hQ : ∀ k w, HStepN k t w → Q (dsig w)) (h : RedStar t u) : Q (dsig u) := by
  obtain ⟨k, w, hw, iw⟩ := factorization h
  obtain ⟨e, p⟩ := istar_pw iw
  have hd : dsig w = dsig u := by
    simp only [dsig, e, pw_dsig p]
  rw [← hd]
  exact hQ k w hw

/-- the ReplaceAll instance -/
theorem transfer_principle_replaceAll {t : T} (Q : T × List (Nat → Bool) → Prop)
    (hQ : ∀ k w, HStepN k t w → Q (dsig w)) (n : Nat) : Q (dsig (passN n t)) := by
  have hr : RedStar t (passN n t) := by
    induction n with
    | zero => exact RedStar.refl t
    | succ n ih => exact ih.trans (par_redstar (par_pass (passN n t)))
  exact transfer_principle Q hQ hr

#print axioms transfer_principle
#print axioms transfer_principle_replaceAll

/-! ## Monotone re-timing (agent_work_P, 2026-10-27)

Along any run t →* u →* u' the head-run times of the factorisation can be chosen monotone: if u is an internal reduct of
the k-th head reduct of t, then u' is an internal reduct of the k'-th head reduct for some k' ≥ k.  So every evaluation
order traverses the leftmost-outermost head run monotonically (possibly pausing during internal steps), with list
elements internally reduced: the order can change WHEN the head-run states are visited and the syntax inside the list
elements, never the sequence of head-run states itself.
-/

theorem factorization_mono {t u u' : T} (k : Nat) (w : T) (hw : HStepN k t w) (iw : IStar w u)
    (h : RedStar u u') : ∃ k' w', k ≤ k' ∧ HStepN k' t w' ∧ IStar w' u' := by
  induction h with
  | refl => exact ⟨k, w, Nat.le_refl k, hw, iw⟩
  | @tail u0 v0 _ hr ih =>
    obtain ⟨k1, w1, hk1, hw1, iw1⟩ := ih
    obtain ⟨u1, hu1, iu1⟩ := par_decomp (red_par hr)
    obtain ⟨j, hj⟩ := hstar_count hu1
    obtain ⟨k', _, w', hw', iw'⟩ := commute_star iw1 j u1 hj
    exact ⟨k1 + k', w', by omega, hstepN_trans hw1 hw', IStar.tail iw' iu1⟩

#print axioms factorization_mono

/-! ## Monotone transfer principle (agent_work_P, 2026-10-27)

Relations between EARLIER and LATER states transfer too: if a relation on data signatures holds between every head-run
state and every later head-run state of t, it holds between every state u and every later state u' of any run
t →* u →* u' (any evaluation order).  Example: Lemma 8's 'the number of data elements never decreases' (as long as
no variable-headed element is opened) is such a relation, so it holds along every evaluation order.
-/

theorem transfer_monotone {t u u' : T} (R : T × List (Nat → Bool) → T × List (Nat → Bool) → Prop)
    (hR : ∀ k k' w w', k ≤ k' → HStepN k t w → HStepN k' t w' → R (dsig w) (dsig w'))
    (h1 : RedStar t u) (h2 : RedStar u u') : R (dsig u) (dsig u') := by
  obtain ⟨k, w, hw, iw⟩ := factorization h1
  obtain ⟨k', w', hk, hw', iw'⟩ := factorization_mono k w hw iw h2
  obtain ⟨e, p⟩ := istar_pw iw
  obtain ⟨e', p'⟩ := istar_pw iw'
  have hd : dsig w = dsig u := by simp only [dsig, e, pw_dsig p]
  have hd' : dsig w' = dsig u' := by simp only [dsig, e', pw_dsig p']
  rw [← hd, ← hd']
  exact hR k k' w w' hk hw hw'

#print axioms transfer_monotone

/-! ## Theorem BC-par: ReplaceAll reveals every node of the Böhm tree (agent_work_P, 2026-10-27)

`node t p`: the Böhm tree of t has a node at path p (p = list of argument positions; a node exists where some reduct is
head-normal).  `revealed u p`: along p the term u is already head-normal at every node.
`replaceAll_reveals`: if the Böhm tree of t has a node at p, then some ReplaceAll iterate passN n t has revealed it.
(Leftmost-outermost evaluation does not have this property: it never leaves an infinite leftmost subtree.)  So under
ReplaceAll every Böhm-tree node is observable by a detector after finitely many passes, and the two arguments of a
head normal form evolve independently and in lockstep (`passN_HN_exact`).
-/

def node : T → List Nat → Prop
  | t, [] => ∃ u, RedStar t u ∧ HN u
  | t, i :: p => ∃ u, RedStar t u ∧ HN u ∧ i < (args u).length ∧ node ((args u).getD i S) p

def revealed : T → List Nat → Prop
  | u, [] => HN u
  | u, i :: p => HN u ∧ i < (args u).length ∧ revealed ((args u).getD i S) p

theorem pass_HN_exact : ∀ u : T, HN u → head (pass u) = head u ∧ args (pass u) = (args u).map pass
  | S, _ => ⟨rfl, rfl⟩
  | var n, _ => ⟨rfl, rfl⟩
  | app f a, h => by
    have hr' : ∀ x y, f ≠ app (app S x) y := by
      intro x y e
      subst e
      rcases h with h | h
      · exact h rfl
      · simp [args] at h
    rw [pass_app f a hr']
    obtain ⟨e1, e2⟩ := pass_HN_exact f (HN_left h)
    refine ⟨e1, ?_⟩
    show args (pass f) ++ [pass a] = (args f ++ [a]).map pass
    rw [e2, List.map_append]
    rfl

theorem HN_of_shape {u v : T} (e1 : head v = head u) (e2 : (args v).length = (args u).length) (h : HN u) : HN v := by
  unfold HN at *
  rw [e1, e2]
  exact h

theorem passN_HN_exact (u : T) (h : HN u) : ∀ j : Nat,
    head (passN j u) = head u ∧ args (passN j u) = (args u).map (passN j)
  | 0 => by
    refine ⟨rfl, ?_⟩
    show args u = (args u).map (passN 0)
    rw [map_passN_zero]
  | j + 1 => by
    obtain ⟨e1, e2⟩ := passN_HN_exact u h j
    have hj : HN (passN j u) := HN_of_shape e1 (by rw [e2, List.length_map]) h
    obtain ⟨f1, f2⟩ := pass_HN_exact (passN j u) hj
    refine ⟨f1.trans e1, ?_⟩
    show args (pass (passN j u)) = (args u).map (passN (j + 1))
    rw [f2, e2, List.map_map]
    rfl

theorem passN_S : ∀ j : Nat, passN j S = S
  | 0 => rfl
  | j + 1 => by show pass (passN j S) = S; rw [passN_S j]; rfl

theorem getD_map_passN (j : Nat) : ∀ (L : List T) (i : Nat), (L.map (passN j)).getD i S = passN j (L.getD i S)
  | [], i => by simp [passN_S]
  | a :: L, 0 => by simp
  | a :: L, i + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact getD_map_passN j L i

theorem pw_getD : ∀ {L L' : List T}, Pw L L' → ∀ i, RedStar (L.getD i S) (L'.getD i S)
  | _, _, Pw.nil, i => by simp; exact RedStar.refl S
  | _, _, Pw.cons h _, 0 => by simpa using h
  | _, _, Pw.cons _ p, i + 1 => by simpa using pw_getD p i

/-- node existence is preserved forward along reductions (confluence + stability of head normal forms) -/
theorem node_forward : ∀ (p : List Nat) {a a' : T}, RedStar a a' → node a p → node a' p
  | [], a, a', r, ⟨u, ru, hu⟩ => by
    obtain ⟨v, uv, a'v⟩ := confluence ru r
    exact ⟨v, a'v, hn_of_pw hu (hnf_stable hu uv).1 (hnf_stable hu uv).2⟩
  | i :: p, a, a', r, ⟨u, ru, hu, hi, hn⟩ => by
    obtain ⟨v, uv, a'v⟩ := confluence ru r
    obtain ⟨e, pw⟩ := hnf_stable hu uv
    refine ⟨v, a'v, hn_of_pw hu e pw, by rw [← pw_length pw]; exact hi, ?_⟩
    exact node_forward p (pw_getD pw i) hn

/-- and backward (a reduct's node is the original's) -/
theorem node_backward : ∀ (p : List Nat) {a a' : T}, RedStar a a' → node a' p → node a p
  | [], a, a', r, ⟨u, ru, hu⟩ => ⟨u, r.trans ru, hu⟩
  | i :: p, a, a', r, ⟨u, ru, hu, hi, hn⟩ => ⟨u, r.trans ru, hu, hi, hn⟩

theorem redstar_passN' (t : T) : ∀ n : Nat, RedStar t (passN n t)
  | 0 => RedStar.refl t
  | n + 1 => (redstar_passN' t n).trans (par_redstar (par_pass (passN n t)))

/-- some ReplaceAll iterate is head-normal whenever any reduct is -/
theorem replaceAll_hn {t u : T} (r : RedStar t u) (hu : HN u) : ∃ n, HN (passN n t) := by
  obtain ⟨h', hh', nh'⟩ := head_normalization r hu
  obtain ⟨k, hk⟩ := hstar_count hh'
  obtain ⟨n, _, hn⟩ := corollaryPT_fast t h' k hk nh'
  exact ⟨n, hn⟩

/-- **Theorem BC-par.** ReplaceAll reveals every node of the Böhm tree. -/
theorem replaceAll_reveals : ∀ (p : List Nat) (t : T), node t p → ∃ n, revealed (passN n t) p
  | [], t, ⟨u, ru, hu⟩ => replaceAll_hn ru hu
  | i :: p, t, ⟨u, ru, hu, hi, hn⟩ => by
    obtain ⟨n0, h0⟩ := replaceAll_hn ru hu
    -- passN n0 t and u are head-normal reducts of t: common reduct, position-wise
    obtain ⟨v, uv, pv⟩ := confluence ru (redstar_passN' t n0)
    obtain ⟨eu, pwu⟩ := hnf_stable hu uv
    obtain ⟨ep, pwp⟩ := hnf_stable h0 pv
    have hlen : i < (args (passN n0 t)).length := by
      rw [pw_length pwp, ← pw_length pwu]; exact hi
    have hnode : node ((args (passN n0 t)).getD i S) p :=
      node_backward p (pw_getD pwp i) (node_forward p (pw_getD pwu i) hn)
    obtain ⟨n1, hr⟩ := replaceAll_reveals p _ hnode
    refine ⟨n0 + n1, ?_⟩
    rw [passN_add t n0 n1]
    obtain ⟨e1, e2⟩ := passN_HN_exact (passN n0 t) h0 n1
    refine ⟨HN_of_shape e1 (by rw [e2, List.length_map]) h0, by rw [e2, List.length_map]; exact hlen, ?_⟩
    rw [e2, getD_map_passN]
    exact hr

#print axioms replaceAll_reveals

/-! ## Cross-check: Lean `pass` = the project's Python ReplaceAll pass (code/parallel_eval.step_fn) on random terms
    (generated by agent_work_P/gen_pass_examples.py; each instance is checked by the kernel with `decide`) -/

example : passN 1 (app S (app (app S S) (app S (app S S)))) = (app S (app (app S S) (app S (app S S)))) := by decide
example : passN 1 (app S (app S (app (app S S) (app S S)))) = (app S (app S (app (app S S) (app S S)))) := by decide
example : passN 3 (app (app S (app (app S S) S)) S) = (app (app S (app (app S S) S)) S) := by decide
example : passN 3 (app (app (app S S) (app (app (app S S) (app S S)) S)) S) = (app (app S S) (app (app S S) (app (app (app S S) S) S))) := by decide
example : passN 3 (app (app S (app S S)) (app S (app S (app S S)))) = (app (app S (app S S)) (app S (app S (app S S)))) := by decide
example : passN 1 (app (app (app S S) (app S S)) (app (app S S) (app (app S S) S))) = (app (app S (app (app S S) (app (app S S) S))) (app (app S S) (app (app S S) (app (app S S) S)))) := by decide
example : passN 2 (app (app (app (app (app S S) S) S) S) (app (app S S) S)) = (app (app (app S S) (app (app S S) S)) (app (app S S) S)) := by decide
example : passN 2 (app (app S S) (app (app S S) S)) = (app (app S S) (app (app S S) S)) := by decide
example : passN 2 (app S (app (app S (app S (app S (app S S)))) (app S (app S S)))) = (app S (app (app S (app S (app S (app S S)))) (app S (app S S)))) := by decide
example : passN 3 (app (app (app S S) (app S (app S S))) (app S S)) = (app (app S (app S S)) (app (app S (app S S)) (app S S))) := by decide
example : passN 4 (app (app (app (app (app S S) (app S S)) (app S S)) (app (app S S) S)) (app S S)) = (app (app (app (app (app S S) (app S S)) (app (app S S) S)) (app S S)) (app (app (app (app S S) S) (app (app (app S S) (app S S)) (app (app S S) S))) (app S S))) := by decide
example : passN 2 (app (app S (app S (app S (app (app (app S S) (app (app S S) S)) S)))) (app S S)) = (app (app S (app S (app S (app (app S S) (app (app S S) (app S S)))))) (app S S)) := by decide
example : passN 2 (app S (app (app S (app S S)) (app S (app S S)))) = (app S (app (app S (app S S)) (app S (app S S)))) := by decide
example : passN 4 (app (app (app (app (app S S) S) S) S) S) = (app (app S S) (app (app S S) (app S S))) := by decide
example : passN 3 (app (app (app S S) (app (app (app S S) S) S)) S) = (app (app S S) (app (app S S) (app (app S S) S))) := by decide
example : passN 2 (app (app (app S S) (app S (app S (app (app S S) S)))) (app S S)) = (app (app S (app S S)) (app (app S (app S (app (app S S) S))) (app S S))) := by decide
example : passN 4 (app (app (app (app S (app S S)) S) (app S (app S S))) S) = (app (app (app S (app S S)) (app (app (app S (app S S)) (app S (app S (app S S)))) S)) (app S (app (app (app S (app S S)) (app S (app S (app S S)))) S))) := by decide
example : passN 2 (app S (app (app S S) (app S S))) = (app S (app (app S S) (app S S))) := by decide
example : passN 3 (app (app S S) (app S (app (app S S) S))) = (app (app S S) (app S (app (app S S) S))) := by decide
example : passN 2 (app (app (app S S) (app S (app S S))) (app S S)) = (app (app S (app S S)) (app (app S (app S S)) (app S S))) := by decide
example : passN 4 (app (app S S) (app S (app S (app S S)))) = (app (app S S) (app S (app S (app S S)))) := by decide
example : passN 3 (app (app (app (app S (app S S)) (app S (app S S))) (app S S)) (app S S)) = (app (app (app (app S (app S S)) (app S S)) (app S S)) (app (app (app S S) (app (app S (app S S)) (app S S))) (app S S))) := by decide
example : passN 2 (app S (app (app S S) (app S S))) = (app S (app (app S S) (app S S))) := by decide
example : passN 1 (app (app (app S S) (app S S)) (app (app (app S S) (app S S)) (app (app S S) S))) = (app (app S (app (app (app S S) (app S S)) (app (app S S) S))) (app (app S S) (app (app (app S S) (app S S)) (app (app S S) S)))) := by decide
example : passN 1 (app (app S S) (app S (app (app S (app (app S S) (app S S))) S))) = (app (app S S) (app S (app (app S (app (app S S) (app S S))) S))) := by decide
example : passN 3 (app (app S S) (app S (app (app S S) S))) = (app (app S S) (app S (app (app S S) S))) := by decide
example : passN 2 (app (app S (app S (app S S))) (app (app S S) (app (app S S) (app S S)))) = (app (app S (app S (app S S))) (app (app S S) (app (app S S) (app S S)))) := by decide
example : passN 2 (app (app (app (app S S) S) (app S S)) (app (app S S) S)) = (app (app (app S S) (app (app S S) S)) (app (app S (app S S)) (app (app S S) S))) := by decide
example : passN 1 (app (app (app (app (app S (app S S)) S) (app S (app (app S S) S))) S) S) = (app (app (app (app (app S S) (app S (app (app S S) S))) (app S (app S (app (app S S) S)))) S) S) := by decide
example : passN 2 (app S (app (app S S) (app (app S S) S))) = (app S (app (app S S) (app (app S S) S))) := by decide
