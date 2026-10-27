
/-! ## Strict cuts in deep walks — SC (agent_work_EM, 2026-10-27) -/

namespace SC

open C
open C.T
open FM
open DP

/-- the Fibonacci child is determined by H(b) -/
theorem fib_next (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (s : Nat) (b X c : T) (K : Nat) (hX : ¬ Tower X) (hb : 2 ≤ (args b).length)
    (hs : u s = app b X) (hK : Reach (args b) [tw K, c]) : u (s + 1) = Fw X c K := by
  have hc := hchild s
  rw [hs] at hc
  rcases hc with ⟨hlen, _, _⟩ | ⟨_, dd, hrr⟩
  · exfalso; rw [args_app] at hlen; simp at hlen; omega
  obtain ⟨K', c', hK', hch⟩ := fib_step b X _ dd hb hX hrr
  have e := RC.reach_det _ _ _ hK hK' (by simp) (by simp)
  simp only [List.cons.injEq] at e
  obtain ⟨h1, h2, _⟩ := e
  have := SA3.tw_inj K K' h1
  subst this; subst h2
  exact hch

/-- every term is S(SS)^n Y with Y not headed by the letter S(SS) -/
theorem twr2_decomp : ∀ σ : T, ∃ n Y, σ = Twr2 Y n ∧ ∀ Y', Y ≠ app (tw 2) Y'
  | S => ⟨0, S, rfl, fun Y' h => by cases h⟩
  | app f x => by
    by_cases hf : f = tw 2
    · obtain ⟨n, Y, hx, hY⟩ := twr2_decomp x
      exact ⟨n + 1, Y, by rw [hf, hx]; rfl, hY⟩
    · exact ⟨0, app f x, rfl, fun Y' h => by
        simp only [app.injEq] at h; exact hf h.1⟩

/-- the base program: tail calls b 0 = Y, ..., b i0, then a step with K0 /= 1 -/
def BaseChain (Y : T) (i0 : Nat) (b : Nat → T) (K0 : Nat) (c0 : T) : Prop :=
  b 0 = Y ∧ (∀ i, i < i0 → 2 ≤ (args (b i)).length ∧ Reach (args (b i)) [tw 1, b (i + 1)]) ∧
  2 ≤ (args (b i0)).length ∧ Reach (args (b i0)) [tw K0, c0] ∧ K0 ≠ 1

/-- running the base program over any non-tower stack -/
theorem base_run (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (Y : T) (i0 : Nat) (b : Nat → T) (K0 : Nat) (c0 : T) (hBC : BaseChain Y i0 b K0 c0)
    (X : T) (hX : ¬ Tower X) (s : Nat) (hs : u s = app Y X) :
    (∀ i, i ≤ i0 → u (s + i) = app (b i) X) ∧ u (s + i0 + 1) = Fw X c0 K0 := by
  obtain ⟨hb0, htail, hlast2, hlast, _⟩ := hBC
  have hrun : ∀ i, i ≤ i0 → u (s + i) = app (b i) X := by
    intro i
    induction i with
    | zero => intro _; rw [hb0]; exact hs
    | succ i ih =>
      intro hi
      obtain ⟨h2, hr⟩ := htail i (by omega)
      have := fib_next u hchild (s + i) (b i) X (b (i + 1)) 1 hX h2 (ih (by omega)) hr
      rw [show s + (i + 1) = s + i + 1 by omega]
      exact this
  exact ⟨hrun, fib_next u hchild (s + i0) (b i0) X c0 K0 hX hlast2 (hrun i0 (Nat.le_refl _)) hlast⟩

/-- the base program exists when the walk never comes back to the stack X -/
theorem base_exists (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (s : Nat) (Y X : T) (hX : ¬ Tower X)
    (hs : u s = app Y X) (hnoX : ∀ e, u (s + e) ≠ X) :
    ∃ i0 b K0 c0, BaseChain Y i0 b K0 c0 := by
  let b : Nat → T := fun i => lchild (u (s + i))
  -- one step from a node (b i).X
  have hone : ∀ i, u (s + i) = app (b i) X → 2 ≤ (args (b i)).length ∧ ∃ K c,
      Reach (args (b i)) [tw K, c] ∧ u (s + i + 1) = Fw X c K ∧ K ≠ 0 := by
    intro i hi
    have hc := hchild (s + i)
    rw [hi] at hc
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hq : args (b i), hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        exact hnoX (i + 1) (by rw [show s + (i + 1) = s + i + 1 by omega]; exact hrr.1.symm)
      | [p], _, _ => exact hnj (s + i) p X (by rw [hi, TC.args_one' (b i) p hq])
      | _ :: _ :: _, hlen, _ => simp at hlen
    · rw [args_app] at hlen
      have h2 : 2 ≤ (args (b i)).length := by simp at hlen; omega
      obtain ⟨K, c, hK, hch⟩ := fib_step (b i) X _ dd h2 hX hrr
      refine ⟨h2, K, c, hK, hch, fun h0 => ?_⟩
      subst h0
      exact hnoX (i + 1) (by rw [show s + (i + 1) = s + i + 1 by omega]; exact hch)
  have hb0 : u (s + 0) = app (b 0) X := by
    show u (s + 0) = app (lchild (u (s + 0))) X
    rw [Nat.add_zero, hs]; rfl
  -- either some step has K /= 1, or all are tail calls (an infinite R2-chain)
  refine Classical.byContradiction (fun hno => ?_)
  have hall : ∀ i, u (s + i) = app (b i) X ∧ Reach (args (b i)) [tw 1, b (i + 1)] := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      have hi : u (s + i) = app (b i) X := by
        cases i with
        | zero => exact hb0
        | succ i' =>
          have h := (ih i' (by omega)).1
          obtain ⟨_, K, c, hK, hch, _⟩ := hone i' h
          have hK1 := (ih i' (by omega)).2
          have e := RC.reach_det _ _ _ hK hK1 (by simp) (by simp)
          simp only [List.cons.injEq] at e
          obtain ⟨e1, e2, _⟩ := e
          have := SA3.tw_inj K 1 e1
          subst this; subst e2
          have hn : u (s + (i' + 1)) = app (b (i' + 1)) X := by
            rw [show s + (i' + 1) = s + i' + 1 by omega]; exact hch
          exact hn
      refine ⟨hi, ?_⟩
      obtain ⟨h2, K, c, hK, hch, hK0⟩ := hone i hi
      by_cases hK1 : K = 1
      · subst hK1
        have hc' : c = b (i + 1) := by
          show c = lchild (u (s + (i + 1)))
          rw [show s + (i + 1) = s + i + 1 by omega, hch]; rfl
        rw [← hc']; exact hK
      · exfalso
        apply hno
        refine ⟨i, b, K, c, (by show lchild (u (s + 0)) = Y; rw [Nat.add_zero, hs]; rfl),
          fun i' hi' => ?_, h2, hK, hK1⟩
        have hp := (ih i' hi').2
        refine ⟨(hone i' (ih i' hi').1).1, hp⟩
  exact no_R2_chain b (fun i => (hall i).2)

end SC

#print axioms SC.fib_next
#print axioms SC.twr2_decomp
#print axioms SC.base_run
#print axioms SC.base_exists
