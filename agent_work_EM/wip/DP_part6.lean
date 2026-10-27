
namespace DP

open C
open C.T
open FM

theorem app_nontower (c Z : T) (hZ : ¬ Tower Z) : ¬ Tower (app c Z) :=
  suf_nontower Z (app c Z) (Suf.wrap c Z Suf.refl) hZ

theorem SS_nontower (ρ : T) : ¬ Tower (app (app S S) ρ) := by
  rintro ⟨m, hm⟩
  cases m with
  | zero => cases hm
  | succ m =>
    simp only [tw, app.injEq] at hm
    exact absurd hm.1 (by intro h; cases h)

theorem tw_eq_one (k : Nat) (h : app S S = tw (k + 1)) : k = 0 := by
  have := SA3.tw_inj 1 (k + 1) h
  omega

/-- **No SS letter on top of the stack.**  In a jump-free infinite leftmost walk no node has the form X.(SS.ρ) with ρ
    a non-tower.  (The segment SS.ρ = S S ρ is a jump node, hence frozen; by the reading lemma every step from a node
    X'.(SS.ρ) comes back to a node X''.(SS.ρ) after one or two steps — a pushed copy whose first letter is SS is read
    and returns at once — or reaches a jump node; so the walk would return infinitely often to the level directly
    above the fixed non-tower SS.ρ, which SA.no_scenarioA excludes.)  Consequence: no step ever pushes the letter SS
    over a non-tower stack (no K = 2 push of SS, no K = 3 push of SS). -/
theorem no_SS_letter (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (X ρ : T) (hρ : ¬ Tower ρ)
    (hu : u t = app X (app (app S S) ρ)) : False := by
  have hZnt : ¬ Tower (app (app S S) ρ) := SS_nontower ρ
  let v : Nat → T := fun j => u (t + j)
  have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
    show FH.LChild (u (t + j)) (u (t + (j + 1)))
    rw [show t + (j + 1) = t + j + 1 by omega]; exact hchild (t + j)
  have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hnj (t + j) p τ
  have habove : ∀ j, Suf (app (app S S) ρ) (v j) ∧ v j ≠ app (app S S) ρ := by
    intro j
    exact tower_letter_frozen u hchild hnj t 0 ρ (by rw [hu]; exact Suf.wrap _ _ Suf.refl) j
  have hcZ : ∀ c, ¬ Tower (app c (app (app S S) ρ)) := fun c => app_nontower c _ hZnt
  have hnext : ∀ j X', v j = app X' (app (app S S) ρ) →
      ∃ X'', v (j + 1) = app X'' (app (app S S) ρ) ∨ v (j + 2) = app X'' (app (app S S) ρ) := by
    intro j X' hj
    have hc := hv j
    rw [hj] at hc
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hX : args X', hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        exact hvnj (j + 1) S ρ hrr.1.symm
      | [p], _, _ => exact hvnj j p _ (by rw [hj, TC.args_one' X' p hX])
      | _ :: _ :: _, hlen, _ => simp at hlen
    · rw [args_app] at hlen
      have hX2 : 2 ≤ (args X').length := by simp at hlen; omega
      obtain ⟨K, c, _, hch⟩ := fib_step X' _ _ dd hX2 hZnt hrr
      match K, hch with
      | 0, hch => exact absurd hch (hvnj (j + 1) S ρ)
      | 1, hch => exact ⟨c, Or.inl hch⟩
      | 2, hch =>
        have e : Fw (app (app S S) ρ) c 2 = app (app (app S S) ρ) (app c (app (app S S) ρ)) := rfl
        rw [e] at hch
        obtain ⟨k, _, hk, h2⟩ := gamma_walk v hv hvnj (j + 1) (app S S) ρ _ hch hρ (hcZ c)
        have := tw_eq_one k hk
        subst this
        exact ⟨c, Or.inr h2⟩
      | 3, hch =>
        exfalso
        have e : Fw (app (app S S) ρ) c 3 =
            app (app c (app (app S S) ρ)) (app (app (app S S) ρ) (app c (app (app S S) ρ))) := rfl
        rw [e] at hch
        have hσ : ¬ Tower (app (app (app S S) ρ) (app c (app (app S S) ρ))) := app_nontower _ _ (hcZ c)
        obtain ⟨k, hk2, hk, h2⟩ := gamma_walk v hv hvnj (j + 1) c _ _ hch hZnt hσ
        match k, hk2, hk, h2 with
        | 0, _, hk, h2 =>
          have e0 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) (app (app S S) ρ) 0 =
              app (app (app S S) ρ) (app c (app (app S S) ρ)) := rfl
          rw [e0] at h2
          obtain ⟨k', _, hk', h3⟩ := gamma_walk v hv hvnj (j + 1 + 1) (app S S) ρ _ h2 hρ (hcZ c)
          have := tw_eq_one k' hk'
          subst this
          have e1 : Fw (app c (app (app S S) ρ)) ρ 0 = app c (app (app S S) ρ) := rfl
          rw [e1, hk] at h3
          exact hvnj (j + 1 + 1 + 1) S _ h3
        | 1, _, hk, h2 =>
          have e0 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) (app (app S S) ρ) 1 =
              app (app (app S S) ρ) (app (app (app S S) ρ) (app c (app (app S S) ρ))) := rfl
          rw [e0] at h2
          obtain ⟨k', _, hk', h3⟩ := gamma_walk v hv hvnj (j + 1 + 1) (app S S) ρ _ h2 hρ hσ
          have := tw_eq_one k' hk'
          subst this
          have e1 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) ρ 0 =
              app (app (app S S) ρ) (app c (app (app S S) ρ)) := rfl
          rw [e1] at h3
          obtain ⟨k'', _, hk'', h4⟩ := gamma_walk v hv hvnj (j + 1 + 1 + 1) (app S S) ρ _ h3 hρ (hcZ c)
          have := tw_eq_one k'' hk''
          subst this
          have e2 : Fw (app c (app (app S S) ρ)) ρ 0 = app c (app (app S S) ρ) := rfl
          rw [e2, hk] at h4
          exact hvnj (j + 1 + 1 + 1 + 1) (tw 1) _ h4
        | 2, _, _, h2 =>
          have e0 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) (app (app S S) ρ) 2 =
              app (app (app (app S S) ρ) (app c (app (app S S) ρ)))
                (app (app (app S S) ρ) (app (app (app S S) ρ) (app c (app (app S S) ρ)))) := rfl
          rw [e0] at h2
          obtain ⟨k', _, hk', _⟩ := gamma_walk v hv hvnj (j + 1 + 1) (app (app S S) ρ) _ _ h2 (hcZ c)
            (app_nontower _ _ hσ)
          exact hZnt ⟨k' + 1, hk'⟩
      | m + 4, hch =>
        exfalso
        have hnt : ∀ i, ¬ Tower (Fw (app (app S S) ρ) c i) := fun i => SA3.fw_nontower _ c hZnt i
        have e : Fw (app (app S S) ρ) c (m + 4) =
            app (app (Fw (app (app S S) ρ) c m) (Fw (app (app S S) ρ) c (m + 1)))
              (Fw (app (app S S) ρ) c (m + 3)) := by
          rw [show m + 4 = (m + 2) + 2 by omega, Fw_add2, Fw_add2]
        rw [e] at hch
        obtain ⟨k', _, hk', _⟩ := gamma_walk v hv hvnj (j + 1) _ _ _ hch (hnt (m + 1)) (hnt (m + 3))
        exact hnt m ⟨k' + 1, hk'⟩
  have hret : ∀ N, ∃ j, N ≤ j ∧ ∃ q, v j = app q (app (app S S) ρ) := by
    have hgo : ∀ N, ∃ j, N ≤ j ∧ ∃ q, v j = app q (app (app S S) ρ) := by
      intro N
      induction N with
      | zero => exact ⟨0, Nat.le_refl _, X, by show u (t + 0) = _; rw [Nat.add_zero]; exact hu⟩
      | succ N ih =>
        obtain ⟨j, hj, q, hq⟩ := ih
        obtain ⟨X'', h⟩ := hnext j q hq
        rcases h with h | h
        · exact ⟨j + 1, by omega, X'', h⟩
        · exact ⟨j + 2, by omega, X'', h⟩
    exact hgo
  exact SA.no_scenarioA v hv _ hZnt hvnj habove hret

end DP

#print axioms DP.no_SS_letter
