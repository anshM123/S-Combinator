
namespace DP

open C
open C.T
open FM

theorem msl_Fw (z c : T) : ∀ i, SA2.msl (Fw z c i) = SA2.msl z + i ∧ SA2.msl (Fw z c (i + 1)) = SA2.msl z + i + 1
  | 0 => ⟨by simp [Fw], by simp [Fw, SA2.msl]⟩
  | i + 1 => by
    have ih := msl_Fw z c i
    refine ⟨by rw [ih.2]; omega, ?_⟩
    rw [show i + 1 + 1 = i + 2 from rfl, Fw_add2]
    simp only [SA2.msl]
    rw [ih.2]; omega

/-- an up-crossing of level d between a and a + n -/
theorem upcross (f : Nat → Nat) (d a : Nat) (ha : f a ≤ d) :
    ∀ n, d < f (a + n) → ∃ p, a ≤ p ∧ p < a + n ∧ f p ≤ d ∧ d < f (p + 1) := by
  intro n
  induction n with
  | zero => intro h; simp at h; omega
  | succ n ih =>
    intro h
    by_cases h2 : d < f (a + n)
    · obtain ⟨p, h1, h3, h4, h5⟩ := ih h2
      exact ⟨p, h1, by omega, h4, h5⟩
    · exact ⟨a + n, by omega, by omega, by omega, by rw [show a + n + 1 = a + (n + 1) by omega]; exact h⟩

/-- **EM_deep from tower pushes (TP).**  Let u be a jump-free infinite leftmost walk whose right-spine depth tends to
    infinity.  Suppose that from some time T on every stack (last argument) is a non-tower and every computed step that
    pushes K >= 2 multipliers is an Omega-type push of a TOWER LETTER: H(q) = S (tw 2) (tw (k+1)).  Then u is
    eventually monotone (no pops, jumps or returns).  Proof: a late return lands at a level d >= depth (u T); some step
    p in [T, r) crosses level d upwards, so it pushes K >= 2, hence a tower letter tw (k+1) at level d, which is
    frozen forever (tower_letter_depth) — the walk can never come back to level d. -/
theorem EM_of_TP (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ)
    (hdeep : ∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j)) (T : Nat)
    (hTP : ∀ t, T ≤ t → ¬ Tower (SA.rpart (u t)) ∧
      ∀ q σ K c, u t = app q σ → 2 ≤ (args q).length → Reach (args q) [tw K, c] → 2 ≤ K →
        K = 2 ∧ ∃ k, c = tw (k + 1)) :
    ∃ j0, ∀ j, j0 ≤ j → 3 ≤ (args (u j)).length ∧ u (j + 1) ≠ SA.rpart (u j) := by
  obtain ⟨N, hN⟩ := hdeep (SA2.msl (u T))
  have hnoret : ∀ r, T ≤ r → N ≤ r + 1 → u (r + 1) ≠ SA.rpart (u r) := by
    intro r hTr hNr hret
    have hr1 : SA2.msl (u r) = SA2.msl (u (r + 1)) + 1 := by
      rw [hret]
      match hur : u r with
      | S => exfalso; have := hchild r; rw [hur] at this; exact CA.no_child_S _ this
      | app f x => simp [SA.rpart, SA2.msl]
    have hTd : SA2.msl (u T) ≤ SA2.msl (u (r + 1)) := by have := hN (r + 1) hNr; omega
    obtain ⟨p, hp1, hp2, hp3, hp4⟩ := upcross (fun j => SA2.msl (u j)) (SA2.msl (u (r + 1))) T hTd (r - T)
      (by show SA2.msl (u (r + 1)) < SA2.msl (u (T + (r - T))); rw [show T + (r - T) = r by omega]; omega)
    have hp3' : SA2.msl (u p) ≤ SA2.msl (u (r + 1)) := hp3
    have hp4' : SA2.msl (u (r + 1)) < SA2.msl (u (p + 1)) := hp4
    clear hp3 hp4
    -- analyse the up-going step at p
    match hup : u p with
    | S => exfalso; have := hchild p; rw [hup] at this; exact CA.no_child_S _ this
    | app q σ =>
      have hc := hchild p
      rw [hup] at hc hp3'
      rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
      · rw [args_app] at hlen hrr
        match hq : args q, hlen, hrr with
        | [], _, hrr =>
          simp only [List.nil_append, List.cons.injEq] at hrr
          rw [← hrr.1] at hp4'
          simp only [SA2.msl] at hp3'
          omega
        | [x], _, _ => exact hnj p x σ (by rw [hup, TC.args_one' q x hq])
        | _ :: _ :: _, hlen, _ => simp at hlen
      · rw [args_app] at hlen
        have hq2 : 2 ≤ (args q).length := by simp at hlen; omega
        have hσ : ¬ Tower σ := by have := (hTP p hp1).1; rw [hup] at this; exact this
        obtain ⟨K, c, hK, hch⟩ := fib_step q σ _ dd hq2 hσ hrr
        have hm := (msl_Fw σ c K).1
        rw [← hch] at hm
        simp only [SA2.msl] at hp3'
        have hK2 : 2 ≤ K := by omega
        obtain ⟨hK2', k, hck⟩ := (hTP p hp1).2 q σ K c hup hq2 hK hK2
        subst hK2'
        -- the tower letter c.σ sits at level msl σ + 1 = msl (u (r+1)) and is frozen from p+1 on
        have hsuf : Suf (app (tw (k + 1)) σ) (u (p + 1)) := by
          rw [hch, ← hck]
          exact Suf.wrap _ _ Suf.refl
        have hfz := tower_letter_depth u hchild hnj (p + 1) k σ hsuf (r - p)
        rw [show p + 1 + (r - p) = r + 1 by omega] at hfz
        simp only [SA2.msl] at hfz
        omega
  refine ⟨T + N, fun j hj => ⟨?_, hnoret j (by omega) (by omega)⟩⟩
  have hc := hchild j
  match huj : u j with
  | S => rw [huj] at hc; exact absurd hc (CA.no_child_S _)
  | app q σ =>
    rw [huj] at hc
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, _, _⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hq : args q, hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        apply hnoret j (by omega) (by omega)
        rw [huj, ← hrr.1]; rfl
      | [x], _, _ => exact hnj j x σ (by rw [huj, TC.args_one' q x hq])
      | _ :: _ :: _, hlen, _ => simp at hlen
    · exact hlen

end DP

#print axioms DP.EM_of_TP
