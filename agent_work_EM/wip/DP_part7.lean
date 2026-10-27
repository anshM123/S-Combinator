
namespace DP

open C
open C.T
open FM

/-- the word of n letters S(SS) on top of Y -/
def Twr2 (Y : T) : Nat → T
  | 0 => Y
  | n + 1 => app (tw 2) (Twr2 Y n)

theorem Twr2_suf (Y : T) : ∀ n, Suf Y (Twr2 Y n)
  | 0 => Suf.refl
  | n + 1 => Suf.wrap _ _ (Twr2_suf Y n)

theorem Twr2_nontower (Y : T) (hY : ¬ Tower Y) (n : Nat) : ¬ Tower (Twr2 Y n) :=
  suf_nontower Y _ (Twr2_suf Y n) hY

/-- **S(SS) letters are skipped.**  A node (S(SS)^n Y).X with Y, X non-towers reaches Y.X in n steps. -/
theorem tw2_skips (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (Y X : T) (hY : ¬ Tower Y) (hX : ¬ Tower X) :
    ∀ n t, u t = app (Twr2 Y n) X → u (t + n) = app Y X := by
  intro n
  induction n with
  | zero => intro t h; exact h
  | succ n ih =>
    intro t h
    have h' : u t = app (app (tw 2) (Twr2 Y n)) X := h
    obtain ⟨k, _, hk, h1⟩ := gamma_walk u hchild hnj t (tw 2) (Twr2 Y n) X h' (Twr2_nontower Y hY n) hX
    have := SA3.tw_inj 2 (k + 1) hk
    obtain rfl : k = 1 := by omega
    have e : Fw X (Twr2 Y n) 1 = app (Twr2 Y n) X := rfl
    rw [e] at h1
    have := ih (t + 1) h1
    rwa [show t + 1 + n = t + (n + 1) by omega] at this

/-- **No Omega-type push over a stack S(SS)^n (S(S(SS)) B).**  In a jump-free infinite leftmost walk, no computed step
    with H(q) = S (S(SS)) c (a K = 2 push) starts from a node q.σ whose stack σ is a word of S(SS) letters on top of a
    letter S(S(SS)) with a non-tower rest B.  (The copy σ put on top is read: the S(SS) letters are skipped, the
    S(S(SS)) letter pushes B and puts the current stack c.σ on top; reading c.σ meets c (SS is excluded by
    no_SS_letter), then the same S(SS)-letters and S(S(SS)) letter again, and finally the non-tower letter B, which the
    reading lemma forbids.)  So every copy put on top by a K = 2 step is read through S(SS)-letters and never meets an
    S(S(SS)) letter before its first other letter. -/
theorem no_tw3_push (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (q c B : T) (n : Nat) (hB : ¬ Tower B)
    (hu : u t = app q (Twr2 (app (tw 3) B) n)) (hq : 2 ≤ (args q).length)
    (hK : Reach (args q) [tw 2, c]) : False := by
  have h3B : ¬ Tower (app (tw 3) B) := app_nontower _ _ hB
  have hσ : ¬ Tower (Twr2 (app (tw 3) B) n) := Twr2_nontower _ h3B n
  -- the K = 2 step
  have hc := hchild t
  rw [hu] at hc
  rcases hc with ⟨hlen, _, _⟩ | ⟨_, dd, hrr⟩
  · exfalso; rw [args_app] at hlen; simp at hlen; omega
  obtain ⟨K, c', hK', hch⟩ := fib_step q _ _ dd hq hσ hrr
  have e := RC.reach_det _ _ _ hK hK' (by simp) (by simp)
  simp only [List.cons.injEq] at e
  obtain ⟨hKK, hcc, _⟩ := e
  have hK2 : K = 2 := (SA3.tw_inj 2 K hKK).symm
  subst hK2; subst hcc
  -- u (t+1) = σ.(c.σ)
  have h1 : u (t + 1) = app (Twr2 (app (tw 3) B) n) (app c (Twr2 (app (tw 3) B) n)) := hch
  have hcσ : ¬ Tower (app c (Twr2 (app (tw 3) B) n)) := app_nontower _ _ hσ
  -- skip the S(SS) letters, then read S(S(SS))
  have h2 := tw2_skips u hchild hnj (app (tw 3) B) _ h3B hcσ n (t + 1) h1
  obtain ⟨k, _, hk, h3⟩ := gamma_walk u hchild hnj (t + 1 + n) (tw 3) B _ h2 hB hcσ
  have := SA3.tw_inj 3 (k + 1) hk
  obtain rfl : k = 2 := by omega
  have e2 : Fw (app c (Twr2 (app (tw 3) B) n)) B 2 =
      app (app c (Twr2 (app (tw 3) B) n)) (app B (app c (Twr2 (app (tw 3) B) n))) := rfl
  rw [e2] at h3
  have hBc : ¬ Tower (app B (app c (Twr2 (app (tw 3) B) n))) := app_nontower _ _ hcσ
  obtain ⟨k', hk'2, hk', h4⟩ := gamma_walk u hchild hnj (t + 1 + n + 1) c _ _ h3 hσ hBc
  match k', hk'2, hk', h4 with
  | 0, _, hk', _ =>
    -- c = SS: the node u (t+1) = σ.(SS.σ) is excluded by no_SS_letter
    exact no_SS_letter u hchild hnj (t + 1) _ _ hσ (by rw [h1, hk']; rfl)
  | 1, _, _, h4 =>
    have e3 : Fw (app B (app c (Twr2 (app (tw 3) B) n))) (Twr2 (app (tw 3) B) n) 1 =
        app (Twr2 (app (tw 3) B) n) (app B (app c (Twr2 (app (tw 3) B) n))) := rfl
    rw [e3] at h4
    have h5 := tw2_skips u hchild hnj (app (tw 3) B) _ h3B hBc n _ h4
    obtain ⟨k2, _, hk2, h6⟩ := gamma_walk u hchild hnj _ (tw 3) B _ h5 hB hBc
    have := SA3.tw_inj 3 (k2 + 1) hk2
    obtain rfl : k2 = 2 := by omega
    have e4 : Fw (app B (app c (Twr2 (app (tw 3) B) n))) B 2 =
        app (app B (app c (Twr2 (app (tw 3) B) n))) (app B (app B (app c (Twr2 (app (tw 3) B) n)))) := rfl
    rw [e4] at h6
    obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ B _ _ h6 hcσ (app_nontower _ _ hBc)
    exact hB ⟨k3 + 1, hk3⟩
  | 2, _, _, h4 =>
    have e3 : Fw (app B (app c (Twr2 (app (tw 3) B) n))) (Twr2 (app (tw 3) B) n) 2 =
        app (app B (app c (Twr2 (app (tw 3) B) n)))
          (app (Twr2 (app (tw 3) B) n) (app B (app c (Twr2 (app (tw 3) B) n)))) := rfl
    rw [e3] at h4
    obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ B _ _ h4 hcσ (app_nontower _ _ hBc)
    exact hB ⟨k3 + 1, hk3⟩

end DP

#print axioms DP.tw2_skips
#print axioms DP.no_tw3_push
