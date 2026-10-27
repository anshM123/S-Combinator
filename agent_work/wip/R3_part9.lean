
/-! ### LN0: if the next phase never opens a copy of its innermost level, it has no p'-front at all -/

theorem ln0_main (Ln : T) (hLnS : head Ln = S) (L0 : List T) (h0 : ∀ e ∈ L0, guarded Ln e)
    (hno : ∀ (m : Nat) (f : T) (L : List T), run m L0 = some (f :: L) → ¬ wpre Ln f) :
    ∀ (m : Nat) (f : T) (L : List T), run m L0 = some (f :: L) → head f ≠ var 0 := by
  intro m f L hm hf
  rcases guarded_phase Ln hLnS L0 h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exact guarded_head Ln (by rw [hLnS]; simp) f (hG f (by simp)) hf
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    rw [hL1] at hr1
    exact hno m1 f1 _ hr1 hwp
