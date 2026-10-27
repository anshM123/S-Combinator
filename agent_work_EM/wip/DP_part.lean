
/-! ## The reading lemma for deep jump-free walks — DP (agent_work_EM, 2026-10-27) -/

namespace DP

open C
open C.T
open FM

theorem tower_S : Tower S := ⟨0, rfl⟩

theorem nontower_ne_S (x : T) (h : ¬ Tower x) : x ≠ S := fun e => h (e ▸ tower_S)

/-- **Reading lemma, node form.**  If the head run of the node (A.B).σ (A /= S) reaches a head normal form [ch, d] and
    B, σ are non-towers, then A = tw (k+1) (so H(A.B) = S (tw k) B) and ch = Fw σ B k. -/
theorem gamma_node (A B σ ch d : T) (hA : A ≠ S) (hB : ¬ Tower B) (hσ : ¬ Tower σ)
    (h : Reach (args (app (app A B) σ)) [ch, d]) : ∃ k, A = tw (k + 1) ∧ ch = Fw σ B k := by
  have hA1 := TC.args_ne_nil A hA
  have hQ : 2 ≤ (args (app A B)).length := by rw [args_app]; simp; omega
  obtain ⟨K, c0, hK, hch⟩ := fib_step (app A B) σ ch d hQ hσ h
  rw [args_app] at hK
  by_cases h2 : 2 ≤ (args A).length
  · exfalso
    have hK' : Reach (args (app A B)) [tw K, c0] := by rw [args_app]; exact hK
    obtain ⟨K', c', _, hfw⟩ := fib_step A B (tw K) c0 h2 hB hK'
    exact SA3.fw_nontower B c' hB K' (hfw ▸ ⟨K, rfl⟩)
  · match hax : args A, hA1, h2 with
    | [p], _, _ =>
      rw [hax] at hK
      have e := reach_stuck _ _ (by simp) hK
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
      obtain ⟨hp, hc, _⟩ := e
      refine ⟨K, ?_, ?_⟩
      · rw [TC.args_one' A p hax, ← hp]; rfl
      · rw [hch, ← hc]
    | [], h1, _ => simp at h1
    | _ :: _ :: _, _, h2 => simp at h2

/-- **Reading lemma, walk form.**  In a jump-free infinite leftmost walk, a node (A.B).σ with B and σ non-towers has
    A = tw (k+1) with k <= 2, and its child is σ (k = 0: a return), B.σ (k = 1) or σ.(B.σ) (k = 2). -/
theorem gamma_walk (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (A B σ : T) (hu : u t = app (app A B) σ)
    (hB : ¬ Tower B) (hσ : ¬ Tower σ) : ∃ k, k ≤ 2 ∧ A = tw (k + 1) ∧ u (t + 1) = Fw σ B k := by
  -- a computed node of the walk reaches its child
  have hreach : ∀ j X Y Z, u j = app (app X Y) Z → X ≠ S → ∃ dd, Reach (args (u j)) [u (j + 1), dd] := by
    intro j X Y Z hj hX
    rcases hchild j with ⟨hlen, _, _⟩ | ⟨_, dd, hr⟩
    · exfalso
      rw [hj, args_app, args_app] at hlen
      have h1 := TC.args_ne_nil X hX
      have h2 : (args X ++ [Y] ++ [Z]).length = (args X).length + 2 := by simp
      omega
    · exact ⟨dd, hr⟩
  have hAS : A ≠ S := by intro e; rw [e] at hu; exact hnj t B σ hu
  obtain ⟨dd, hr⟩ := hreach t A B σ hu hAS
  rw [hu] at hr
  obtain ⟨k, hk, hch⟩ := gamma_node A B σ _ dd hAS hB hσ hr
  refine ⟨k, ?_, hk, hch⟩
  refine Classical.byContradiction (fun hk2 => ?_)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  -- the child Fw (m+3) = (X.Y).Z with X, Y, Z non-towers: the reading lemma at t+1 makes X a tower
  have hnt : ∀ i, ¬ Tower (Fw σ B i) := fun i => SA3.fw_nontower σ B hσ i
  obtain ⟨X, Y, hXY, hX, hY⟩ : ∃ X Y, Fw σ B (m + 1) = app X Y ∧ ¬ Tower X ∧ ¬ Tower Y := by
    cases m with
    | zero => exact ⟨B, σ, rfl, hB, hσ⟩
    | succ m' => exact ⟨Fw σ B m', Fw σ B (m' + 1), Fw_add2 σ B m', hnt _, hnt _⟩
  have hu1 : u (t + 1) = app (app X Y) (Fw σ B (m + 2)) := by
    rw [hch, show m + 3 = (m + 1) + 2 by omega, Fw_add2, hXY]
  obtain ⟨dd1, hr1⟩ := hreach (t + 1) X Y _ hu1 (nontower_ne_S X hX)
  rw [hu1] at hr1
  obtain ⟨k1, hk1, _⟩ := gamma_node X Y _ _ dd1 (nontower_ne_S X hX) hY (hnt (m + 2)) hr1
  exact hX ⟨k1 + 1, hk1⟩

end DP

#print axioms DP.gamma_node
#print axioms DP.gamma_walk
