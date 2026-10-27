/-
  Leftmost Böhm-tree walks never repeat a node (given Waldmann's no-spiral theorem) — machine-checked
  (main agent, 2026-10-27, after the J agent's hand proof of 12:47). Plain Lean 4 core, no Mathlib.
  S-terms; one-step reduction `Red` anywhere; the head machine on argument lists; a leftmost child (`LChild`, the same
  definition as FH.LChild in lean/AgentEMA.lean): for a node with at most two arguments its first argument, otherwise
  the first component of the head normal form [u', d] reached by the head machine.
  * `lchild_red`: u →* v with u' a PROPER subterm of v (plug C u', C not the hole), and u →+ v when u has >= 3 arguments.
  * `no_repeat`: under the hypothesis NoSpiral (no term reduces in one or more steps to a context of itself with a
    non-trivial context — Waldmann's theorem, BEKW 'Dance of the starlings' Theorem 14, CITED, not proved here), no
    leftmost walk visits the same node twice. The trivial-context case is Proposition MW's acyclicity, re-proved here.
  * `no_periodic`: hence no infinite leftmost walk is eventually periodic.
-/

inductive T where
  | S : T
  | app : T → T → T
deriving DecidableEq, Repr

open T

def args : T → List T
  | S => []
  | app f x => args f ++ [x]

def size : T → Nat
  | S => 1
  | app f a => size f + size a

/-- one reduction step anywhere -/
inductive Red : T → T → Prop
  | redex (x y z : T) : Red (app (app (app S x) y) z) (app (app x z) (app y z))
  | left {f f' : T} (a : T) : Red f f' → Red (app f a) (app f' a)
  | right (f : T) {a a' : T} : Red a a' → Red (app f a) (app f a')

inductive RedStar : T → T → Prop
  | refl (t : T) : RedStar t t
  | tail {t u v : T} : RedStar t u → Red u v → RedStar t v

/-- one or more steps -/
def RedPlus (t v : T) : Prop := ∃ u, RedStar t u ∧ Red u v

theorem RedStar.trans {t u v : T} (h1 : RedStar t u) (h2 : RedStar u v) : RedStar t v := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact RedStar.tail ih h

/-- head machine on argument lists -/
def step : List T → Option (List T)
  | a :: b :: c :: R => some (args a ++ c :: app b c :: R)
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-- the leftmost child (as FH.LChild in lean/AgentEMA.lean) -/
def LChild (u u' : T) : Prop :=
  ((args u).length ≤ 2 ∧ ∃ rest, args u = u' :: rest) ∨
  (3 ≤ (args u).length ∧ ∃ n d, run n (args u) = some [u', d])

/-- one-hole contexts -/
inductive Ctx where
  | hole : Ctx
  | appL : Ctx → T → Ctx
  | appR : T → Ctx → Ctx

def plug : Ctx → T → T
  | Ctx.hole, u => u
  | Ctx.appL C x, u => app (plug C u) x
  | Ctx.appR f C, u => app f (plug C u)

def comp : Ctx → Ctx → Ctx
  | Ctx.hole, D => D
  | Ctx.appL C x, D => Ctx.appL (comp C D) x
  | Ctx.appR f C, D => Ctx.appR f (comp C D)

theorem plug_comp : ∀ (C D : Ctx) (u : T), plug (comp C D) u = plug C (plug D u)
  | Ctx.hole, _, _ => rfl
  | Ctx.appL C x, D, u => by simp [comp, plug, plug_comp C D u]
  | Ctx.appR f C, D, u => by simp [comp, plug, plug_comp C D u]

theorem comp_ne_hole (C D : Ctx) (h : C ≠ Ctx.hole) : comp C D ≠ Ctx.hole := by
  cases C with
  | hole => exact absurd rfl h
  | appL C x => simp [comp]
  | appR f C => simp [comp]

theorem size_pos : ∀ t : T, 1 ≤ size t
  | S => by simp [size]
  | app f a => by have := size_pos f; simp [size]; omega

theorem size_plug : ∀ (C : Ctx) (u : T), C ≠ Ctx.hole → size u < size (plug C u)
  | Ctx.hole, _, h => absurd rfl h
  | Ctx.appL C x, u, _ => by
    simp only [plug, size]
    have := size_pos x
    cases C with
    | hole => simp [plug]; omega
    | appL C' y => have := size_plug (Ctx.appL C' y) u (by simp); omega
    | appR g C' => have := size_plug (Ctx.appR g C') u (by simp); omega
  | Ctx.appR f C, u, _ => by
    simp only [plug, size]
    have := size_pos f
    cases C with
    | hole => simp [plug]; omega
    | appL C' y => have := size_plug (Ctx.appL C' y) u (by simp); omega
    | appR g C' => have := size_plug (Ctx.appR g C') u (by simp); omega

theorem red_plug (C : Ctx) {u v : T} (h : Red u v) : Red (plug C u) (plug C v) := by
  induction C with
  | hole => exact h
  | appL C x ih => exact Red.left x ih
  | appR f C ih => exact Red.right f ih

theorem redstar_plug (C : Ctx) {u v : T} (h : RedStar u v) : RedStar (plug C u) (plug C v) := by
  induction h with
  | refl => exact RedStar.refl _
  | tail _ h ih => exact RedStar.tail ih (red_plug C h)

/-- the spine term S·L -/
def sp (L : List T) : T := L.foldl app S

theorem sp_args : ∀ t : T, sp (args t) = t := by
  intro t
  induction t with
  | S => rfl
  | app f x ihf _ => simp [sp, args, List.foldl_append] at *; rw [ihf]

theorem foldl_red (R : List T) : ∀ {u v : T}, Red u v → Red (R.foldl app u) (R.foldl app v) := by
  induction R with
  | nil => intro u v h; exact h
  | cons x R ih => intro u v h; exact ih (Red.left x h)

/-- a head-machine step is one reduction step of the spine term -/
theorem step_red (L L' : List T) (h : step L = some L') : Red (sp L) (sp L') := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step, Option.some.injEq] at h
    subst h
    have e1 : sp (a :: b :: c :: R) = R.foldl app (app (app (app S a) b) c) := rfl
    have e2 : sp (args a ++ c :: app b c :: R) = R.foldl app (app (app (sp (args a)) c) (app b c)) := by
      simp [sp, List.foldl_append]
    rw [e1, e2, sp_args a]
    exact foldl_red R (Red.redex a b c)

theorem run_red : ∀ (n : Nat) (L L' : List T), run n L = some L' → RedStar (sp L) (sp L')
  | 0, L, L', h => by simp [run] at h; subst h; exact RedStar.refl _
  | n + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      exact (RedStar.tail (RedStar.refl _) (step_red L L1 hs)).trans (run_red n L1 L' h)

/-- a run of length >= 3 cannot reach a list of length 2 in zero steps -/
theorem run_pos (L L' : List T) (n : Nat) (h : run n L = some L') (hl : 3 ≤ L.length) (hl' : L'.length = 2) :
    ∃ m, n = m + 1 := by
  cases n with
  | zero => simp [run] at h; subst h; omega
  | succ m => exact ⟨m, rfl⟩

theorem redplus_of (x a b : T) (h1 : Red x a) (h2 : RedStar a b) : RedPlus x b := by
  induction h2 with
  | refl => exact ⟨x, RedStar.refl _, h1⟩
  | tail h3 h4 _ => exact ⟨_, (RedStar.tail (RedStar.refl _) h1).trans h3, h4⟩

theorem run_succ_red (m : Nat) (L L2 : List T) (h : run (m + 1) L = some L2) : RedPlus (sp L) (sp L2) := by
  simp only [run] at h
  cases hs : step L with
  | none => rw [hs] at h; simp at h
  | some L1 =>
    rw [hs] at h
    exact redplus_of _ _ _ (step_red L L1 hs) (run_red m L1 L2 h)

theorem args_cons_ctx (u u' : T) (rest : List T) (h : args u = u' :: rest) : ∃ C, C ≠ Ctx.hole ∧ u = plug C u' := by
  -- u = sp (u' :: rest) = rest.foldl app (app S u')
  have e : u = rest.foldl app (app S u') := by rw [← sp_args u, h]; rfl
  -- a fold of applications over app S u' is a context around u'
  have key : ∀ (R : List T) (C : Ctx), C ≠ Ctx.hole → ∃ D, D ≠ Ctx.hole ∧ R.foldl app (plug C u') = plug D u' := by
    intro R
    induction R with
    | nil => intro C hC; exact ⟨C, hC, rfl⟩
    | cons x R ih =>
      intro C hC
      have := ih (Ctx.appL C x) (by simp)
      simpa [List.foldl, plug] using this
  obtain ⟨D, hD, hD'⟩ := key rest (Ctx.appR S Ctx.hole) (by simp)
  exact ⟨D, hD, by rw [e]; simpa [plug] using hD'⟩

/-- **Leftmost step lemma.** u →* v with the leftmost child a proper subterm of v (v = plug C u', C non-trivial);
    if u has at least three arguments, u →+ v. -/
theorem lchild_red (u u' : T) (h : LChild u u') :
    ∃ C, C ≠ Ctx.hole ∧ ((3 ≤ (args u).length → RedPlus u (plug C u')) ∧
      ((args u).length ≤ 2 → u = plug C u')) := by
  rcases h with ⟨hl, rest, hr⟩ | ⟨hl, n, d, hrun⟩
  · obtain ⟨C, hC, e⟩ := args_cons_ctx u u' rest hr
    exact ⟨C, hC, fun h3 => absurd h3 (by omega), fun _ => e⟩
  · obtain ⟨m, rfl⟩ := run_pos _ _ n hrun hl (by simp)
    have hp := run_succ_red m _ _ hrun
    rw [sp_args u] at hp
    refine ⟨Ctx.appL (Ctx.appR S Ctx.hole) d, by simp, fun _ => ?_, fun h2 => absurd h2 (by omega)⟩
    simpa [sp, plug] using hp

/-- Waldmann's no-spiral theorem (BEKW Theorem 14), stated as a hypothesis: no term reduces in one or more steps to
    a non-trivial context of itself. -/
def NoSpiral : Prop := ∀ (M : T) (C : Ctx), C ≠ Ctx.hole → ¬ RedPlus M (plug C M)

/-- reduction never decreases the size, and contracting a redex S x y z with z = S keeps it -/
theorem red_size {t u : T} (h : Red t u) : size t ≤ size u := by
  induction h with
  | redex x y z => have := size_pos z; simp only [size]; omega
  | left a _ ih => simp only [size]; omega
  | right f _ ih => simp only [size]; omega

theorem redstar_size {t u : T} (h : RedStar t u) : size t ≤ size u := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ h ih => exact Nat.le_trans ih (red_size h)

/-- walk segment: from u N the walk reaches u M inside a non-trivial context, by reduction, with at least one step if
    some node in between has three or more arguments -/
theorem segment (u : Nat → T) (hw : ∀ j, LChild (u j) (u (j + 1))) (N : Nat) :
    ∀ d, ∃ C, C ≠ Ctx.hole ∧ RedStar (u N) (plug C (u (N + d + 1))) ∧
      ((∃ j, N ≤ j ∧ j ≤ N + d ∧ 3 ≤ (args (u j)).length) → RedPlus (u N) (plug C (u (N + d + 1)))) := by
  intro d
  induction d with
  | zero =>
    obtain ⟨C, hC, hp, he⟩ := lchild_red (u N) (u (N + 1)) (hw N)
    refine ⟨C, hC, ?_, ?_⟩
    · rcases Nat.lt_or_ge (args (u N)).length 3 with hl | hl
      · rw [← he (by omega)]; exact RedStar.refl _
      · obtain ⟨v, h1, h2⟩ := hp hl; exact RedStar.tail h1 h2
    · rintro ⟨j, h1, h2, h3⟩
      have : j = N := by omega
      subst this
      exact hp h3
  | succ d ih =>
    obtain ⟨C, hC, hs, hp⟩ := ih
    obtain ⟨D, hD, hp2, he2⟩ := lchild_red (u (N + d + 1)) (u (N + d + 1 + 1)) (hw (N + d + 1))
    have e : N + (d + 1) + 1 = N + d + 1 + 1 := by omega
    rw [e]
    refine ⟨comp C D, comp_ne_hole C D hC, ?_, ?_⟩
    · rcases Nat.lt_or_ge (args (u (N + d + 1))).length 3 with hl | hl
      · rw [plug_comp, ← he2 (by omega)]; exact hs
      · obtain ⟨v, h1, h2⟩ := hp2 hl
        rw [plug_comp]
        exact hs.trans (RedStar.tail (redstar_plug C h1) (red_plug C h2))
    · rintro ⟨j, h1, h2, h3⟩
      rcases Nat.lt_or_ge j (N + d + 1) with hj | hj
      · obtain ⟨v, hv1, hv2⟩ := hp ⟨j, h1, by omega, h3⟩
        rw [plug_comp]
        rcases Nat.lt_or_ge (args (u (N + d + 1))).length 3 with hl | hl
        · rw [← he2 (by omega)]; exact ⟨v, hv1, hv2⟩
        · obtain ⟨w, hw1, hw2⟩ := hp2 hl
          exact ⟨_, (RedStar.tail hv1 hv2).trans (redstar_plug C hw1), red_plug C hw2⟩
      · have : j = N + d + 1 := by omega
        subst this
        obtain ⟨w, hw1, hw2⟩ := hp2 h3
        rw [plug_comp]
        exact ⟨_, hs.trans (redstar_plug C hw1), red_plug C hw2⟩

/-- **No repeated node.** Under NoSpiral (Waldmann's theorem, cited), a leftmost walk never visits a node twice. -/
theorem no_repeat (hNS : NoSpiral) (u : Nat → T) (hw : ∀ j, LChild (u j) (u (j + 1))) (N M : Nat) (h : N < M) :
    u N ≠ u M := by
  intro heq
  obtain ⟨d, rfl⟩ : ∃ d, M = N + d + 1 := ⟨M - N - 1, by omega⟩
  obtain ⟨C, hC, hs, hp⟩ := segment u hw N d
  rw [← heq] at hs hp
  by_cases hcomp : ∃ j, N ≤ j ∧ j ≤ N + d ∧ 3 ≤ (args (u j)).length
  · exact hNS (u N) C hC (hp hcomp)
  · -- no computed node: every step is a pop or a jump, so no reduction happened and u N is a proper subterm of itself
    have hsz := redstar_size hs
    have := size_plug C (u N) hC
    -- u N →* plug C (u N) only by reflexivity? Not needed: size alone gives a contradiction only with equality,
    -- so use the structure: all steps are subterm steps, hence u N = plug C' (u N) for a non-trivial C'.
    have key : ∀ e, e ≤ d → ∃ D, D ≠ Ctx.hole ∧ u N = plug D (u (N + e + 1)) := by
      intro e
      induction e with
      | zero =>
        intro _
        obtain ⟨D, hD, _, he⟩ := lchild_red (u N) (u (N + 1)) (hw N)
        have hl : (args (u N)).length ≤ 2 := by
          rcases Nat.lt_or_ge (args (u N)).length 3 with hl | hl
          · omega
          · exact absurd ⟨N, Nat.le_refl _, by omega, hl⟩ hcomp
        exact ⟨D, hD, he hl⟩
      | succ e ih =>
        intro he'
        obtain ⟨D, hD, hDe⟩ := ih (by omega)
        obtain ⟨D2, hD2, _, he2⟩ := lchild_red (u (N + e + 1)) (u (N + e + 1 + 1)) (hw (N + e + 1))
        have hl : (args (u (N + e + 1))).length ≤ 2 := by
          rcases Nat.lt_or_ge (args (u (N + e + 1))).length 3 with hl | hl
          · omega
          · exact absurd ⟨N + e + 1, by omega, by omega, hl⟩ hcomp
        refine ⟨comp D D2, comp_ne_hole D D2 hD, ?_⟩
        rw [show N + (e + 1) + 1 = N + e + 1 + 1 by omega, plug_comp, ← he2 hl]
        exact hDe
    obtain ⟨D, hD, hDe⟩ := key d (Nat.le_refl d)
    rw [← heq] at hDe
    have := size_plug D (u N) hD
    rw [← hDe] at this
    omega

/-- **No eventually periodic infinite leftmost walk** (under NoSpiral). -/
theorem no_periodic (hNS : NoSpiral) (u : Nat → T) (hw : ∀ j, LChild (u j) (u (j + 1))) :
    ¬ ∃ N p, 0 < p ∧ ∀ j, N ≤ j → u (j + p) = u j := by
  rintro ⟨N, p, hp, hper⟩
  exact no_repeat hNS u hw N (N + p) (by omega) (hper N (Nat.le_refl N)).symm

#print axioms lchild_red
#print axioms no_repeat
#print axioms no_periodic
