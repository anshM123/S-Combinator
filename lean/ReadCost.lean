/-
  Lemmas 11 (full-read principle) and 12 (right-depth cost), on top of Lemma 8 and Theorem J — machine-checked
  (main agent, 2026-10-27). Plain Lean 4 core, no Mathlib. Framework: the head machine with opaque atoms
  (copied from lean/AgentOC.lean): [a, b, c] ++ R => args a ++ [c, b·c] ++ R when a has head S; an atom-headed front
  is stuck. An element is *data* if it contains an atom.
  * `dcount_step` (Lemma 8): a step never lowers the number of data elements.
  * `no_hnf_of_three_data` (Corollary 8(i)): from a list with >= 3 data elements no list of length <= 2 is reachable.
  * `theoremJ`: in a run that reaches a head normal form, a *write* (b closed, c data) happens only when the data count
    is exactly 1, raises it to exactly 2, and there is at most one write.
-/

inductive T where
  | S : T
  | var : Nat → T
  | app : T → T → T
deriving DecidableEq, Repr

namespace T

def args : T → List T
  | S => []
  | var _ => []
  | app f x => args f ++ [x]

def head : T → T
  | S => S
  | var n => var n
  | app f _ => head f

/-- no atoms (Boolean) -/
def nv : T → Bool
  | S => true
  | var _ => false
  | app f x => nv f && nv x

end T

open T

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-- number of data elements (elements containing an atom) -/
def dcount : List T → Nat
  | [] => 0
  | x :: xs => (if nv x then 0 else 1) + dcount xs

theorem dcount_append : ∀ (A B : List T), dcount (A ++ B) = dcount A + dcount B
  | [], B => by simp [dcount]
  | x :: xs, B => by simp [dcount, dcount_append xs B]; omega

theorem dcount_le_length : ∀ L : List T, dcount L ≤ L.length
  | [] => by simp [dcount]
  | x :: xs => by have := dcount_le_length xs; simp [dcount]; split <;> omega

/-- an S-headed term with an atom has an argument with an atom -/
theorem args_data : ∀ a : T, head a = S → nv a = false → 1 ≤ dcount (args a)
  | S, _, h => by simp [nv] at h
  | var _, h, _ => by simp [head] at h
  | app f x, hh, hn => by
    have hf : head f = S := by simpa [head] using hh
    simp only [args, dcount_append]
    simp only [nv, Bool.and_eq_false_iff] at hn
    rcases hn with hf' | hx
    · have := args_data f hf hf'; omega
    · simp [dcount, hx]

/-- data weight of one element -/
def dv (x : T) : Nat := if nv x then 0 else 1

theorem dcount_cons (x : T) (xs : List T) : dcount (x :: xs) = dv x + dcount xs := by simp [dcount, dv]

theorem dv_app_left (b c : T) : dv b ≤ dv (app b c) := by
  unfold dv; simp only [nv]
  by_cases hb : nv b = true <;> by_cases hc : nv c = true <;> simp [hb, hc]

theorem dv_app_right (b c : T) : dv c ≤ dv (app b c) := by
  unfold dv; simp only [nv]
  by_cases hb : nv b = true <;> by_cases hc : nv c = true <;> simp [hb, hc]

theorem dv_args (a : T) (h : head a = S) : dv a ≤ dcount (args a) := by
  unfold dv
  cases ha : nv a
  · have := args_data a h ha; simp; omega
  · simp

/-- **Lemma 8** (data conservation) -/
theorem dcount_step (a b c : T) (R : List T) (h : head a = S) :
    dcount (a :: b :: c :: R) ≤ dcount (args a ++ c :: app b c :: R) := by
  rw [dcount_append]
  simp only [dcount_cons]
  have h1 := dv_args a h
  have h2 := dv_app_left b c
  omega

theorem dcount_step' (L L' : List T) (h : step L = some L') : dcount L ≤ dcount L' := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact dcount_step a b c R (by assumption)
    · simp at h

theorem dcount_run : ∀ (n : Nat) (L L' : List T), run n L = some L' → dcount L ≤ dcount L'
  | 0, L, L', h => by simp [run] at h; subst h; exact Nat.le_refl _
  | n + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 => rw [hs] at h; exact Nat.le_trans (dcount_step' L L1 hs) (dcount_run n L1 L' h)

/-- **Corollary 8(i).** From a list with at least three data elements no head normal form is reachable
    (the run either gets stuck at an atom-headed front or never shrinks below three elements). -/
theorem no_hnf_of_three_data (L : List T) (h3 : 3 ≤ dcount L) :
    ∀ n L', run n L = some L' → 3 ≤ L'.length := by
  intro n L' h
  have := dcount_run n L L' h
  have := dcount_le_length L'
  omega

/-- a write raises the data count by at least one -/
theorem dcount_write (a b c : T) (R : List T) (h : head a = S) (hb : nv b = true) (hc : nv c = false) :
    dcount (a :: b :: c :: R) + 1 ≤ dcount (args a ++ c :: app b c :: R) := by
  rw [dcount_append]
  simp only [dcount_cons]
  have h1 := dv_args a h
  have e1 : dv b = 0 := by simp [dv, hb]
  have e2 : dv c = 1 := by simp [dv, hc]
  have e3 : dv (app b c) = 1 := by simp [dv, nv, hc]
  omega

theorem run_add : ∀ (m n : Nat) (L L' : List T), run m L = some L' → run (m + n) L = run n L'
  | 0, n, L, L', h => by simp [run] at h; subst h; simp
  | m + 1, n, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [run, hs]; exact run_add m n L1 L' h

/-- **Theorem J** (global writes). Let the run from L0 reach a head normal form LN (length <= 2) at time N.
    If at time k < N the list is [a, b, c] ++ R with a S-headed, b closed and c data (a *write*), then the data count is
    exactly 1 before the write and exactly 2 after it. -/
theorem theoremJ (L0 LN : List T) (N k : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (a b c : T) (R : List T) (hk : run k L0 = some (a :: b :: c :: R)) (hkN : k < N)
    (ha : head a = S) (hb : nv b = true) (hc : nv c = false) :
    dcount (a :: b :: c :: R) = 1 ∧ dcount (args a ++ c :: app b c :: R) = 2 := by
  have hs : step (a :: b :: c :: R) = some (args a ++ c :: app b c :: R) := by simp [step, ha]
  have hafter : run (k + 1) L0 = some (args a ++ c :: app b c :: R) := by
    rw [run_add k 1 _ _ hk]; simp [run, hs]
  have hrest : run (N - (k + 1)) (args a ++ c :: app b c :: R) = some LN := by
    have := run_add (k + 1) (N - (k + 1)) _ _ hafter
    rw [show k + 1 + (N - (k + 1)) = N by omega, hN] at this
    exact this.symm
  have h1 := dcount_run _ _ _ hrest
  have h2 := dcount_le_length LN
  have h3 := dcount_write a b c R ha hb hc
  have h4 : 1 ≤ dcount (a :: b :: c :: R) := by
    simp only [dcount_cons]; have : dv c = 1 := by simp [dv, hc]
    omega
  omega

/-- **Theorem J (iii).** In a run that reaches a head normal form there is at most one write. -/
theorem theoremJ_unique (L0 LN : List T) (N k1 k2 : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (a1 b1 c1 a2 b2 c2 : T) (R1 R2 : List T)
    (hk1 : run k1 L0 = some (a1 :: b1 :: c1 :: R1)) (hk2 : run k2 L0 = some (a2 :: b2 :: c2 :: R2))
    (h12 : k1 < k2) (hk2N : k2 < N)
    (ha1 : head a1 = S) (hb1 : nv b1 = true) (hc1 : nv c1 = false)
    (ha2 : head a2 = S) (hb2 : nv b2 = true) (hc2 : nv c2 = false) : False := by
  have J1 := theoremJ L0 LN N k1 hN hlen a1 b1 c1 R1 hk1 (by omega) ha1 hb1 hc1
  have J2 := theoremJ L0 LN N k2 hN hlen a2 b2 c2 R2 hk2 hk2N ha2 hb2 hc2
  have hs : step (a1 :: b1 :: c1 :: R1) = some (args a1 ++ c1 :: app b1 c1 :: R1) := by simp [step, ha1]
  have hafter : run (k1 + 1) L0 = some (args a1 ++ c1 :: app b1 c1 :: R1) := by
    rw [run_add k1 1 _ _ hk1]; simp [run, hs]
  have hmid : run (k2 - (k1 + 1)) (args a1 ++ c1 :: app b1 c1 :: R1) = some (a2 :: b2 :: c2 :: R2) := by
    have := run_add (k1 + 1) (k2 - (k1 + 1)) _ _ hafter
    rw [show k1 + 1 + (k2 - (k1 + 1)) = k2 by omega, hk2] at this
    exact this.symm
  have := dcount_run _ _ _ hmid
  omega

/-- **Theorem J (i)** (writes are global): at a write, every other list element is atom-free, so c carries all the data. -/
theorem theoremJ_global (L0 LN : List T) (N k : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (a b c : T) (R : List T) (hk : run k L0 = some (a :: b :: c :: R)) (hkN : k < N)
    (ha : head a = S) (hb : nv b = true) (hc : nv c = false) :
    nv a = true ∧ dcount R = 0 := by
  have J := (theoremJ L0 LN N k hN hlen a b c R hk hkN ha hb hc).1
  simp only [dcount_cons] at J
  have e2 : dv c = 1 := by simp [dv, hc]
  have hA : dv a = 0 := by omega
  refine ⟨?_, by omega⟩
  unfold dv at hA
  by_cases h : nv a = true
  · exact h
  · simp [h] at hA


/-! ## Corollary 8(ii) / Lemma 9: with two live data, code cannot write into data, and data stay in control -/

/-- every data element is atom-headed -/
def dhead (L : List T) : Prop := ∀ e ∈ L, nv e = false → ∃ n, head e = var n

theorem nv_args : ∀ a : T, nv a = true → ∀ e ∈ args a, nv e = true
  | S, _, e, he => by simp [args] at he
  | var _, h, _, _ => by simp [nv] at h
  | app f x, h, e, he => by
    simp only [nv, Bool.and_eq_true] at h
    simp only [args, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact nv_args f h.1 e he
    · exact h.2

/-- **Corollary 8(ii).** If a list holds at least two data elements, all atom-headed, and the run reaches a head normal
    form, then every data element of every later list (in particular of the hnf) is atom-headed: closed code never ends up
    holding data. -/
theorem cor8ii : ∀ (N : Nat) (L1 LN : List T), run N L1 = some LN → LN.length ≤ 2 →
    2 ≤ dcount L1 → dhead L1 → dhead LN
  | 0, L1, LN, h, _, _, hd => by simp [run] at h; subst h; exact hd
  | N + 1, L1, LN, h, hlen, h2, hd => by
    simp only [run] at h
    cases hs : step L1 with
    | none => rw [hs] at h; simp at h
    | some L2 =>
      rw [hs] at h
      match L1, hs, h2, hd with
      | a :: b :: c :: R, hs, h2, hd =>
        simp only [step] at hs
        split at hs
        · rename_i ha
          simp only [Option.some.injEq] at hs
          subst hs
          have hgrow := dcount_step a b c R ha
          have hfin := dcount_run N _ LN h
          have hlenN := dcount_le_length LN
          -- the front is S-headed, so it is closed
          have hna : nv a = true := by
            cases hv : nv a
            · obtain ⟨n, hn⟩ := hd a (by simp) hv
              rw [ha] at hn
              exact absurd hn (by simp)
            · rfl
          refine cor8ii N _ LN h hlen (by omega) ?_
          intro e he hev
          rcases List.mem_append.1 he with he | he
          · rw [nv_args a hna e he] at hev
            exact absurd hev (by decide)
          · rcases List.mem_cons.1 he with rfl | he
            · exact hd e (by simp) hev
            · rcases List.mem_cons.1 he with rfl | he
              · cases hb : nv b
                · obtain ⟨n, hn⟩ := hd b (by simp) hb
                  exact ⟨n, by simp [head, hn]⟩
                · -- b closed and b·c data: a write, which would leave three data elements
                  have hc : nv c = false := by simp [nv, hb] at hev; exact hev
                  have := dcount_write a b c R ha hb hc
                  omega
              · exact hd e (by simp [he]) hev
        · simp at hs

/-- **Lemma 9 (no writing into data while two data are live).** In a run that reaches a head normal form, once the list
    holds at least two data elements, no later step is a write (b closed, c data). -/
theorem lemma9_nowrite (L0 LN : List T) (N k0 k : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (L1 : List T) (hk0 : run k0 L0 = some L1) (h2 : 2 ≤ dcount L1)
    (a b c : T) (R : List T) (hk : run k L0 = some (a :: b :: c :: R)) (hk0k : k0 ≤ k) (hkN : k < N)
    (ha : head a = S) (hb : nv b = true) : nv c = true := by
  cases hc : nv c
  · have J := (theoremJ L0 LN N k hN hlen a b c R hk hkN ha hb hc).1
    have hmid : run (k - k0) L1 = some (a :: b :: c :: R) := by
      have := run_add k0 (k - k0) _ _ hk0
      rw [show k0 + (k - k0) = k by omega, hk] at this
      exact this.symm
    have := dcount_run _ _ _ hmid
    omega
  · rfl


/-! ## Lemma 11 (full-read principle) and Lemma 12 (right-depth cost)

  Mark occurrences by atoms and substitute closed (or any) terms for them: `subst s` replaces every atom var n by s n.
  A replaced occurrence is *read* when the atom run reaches an atom-headed front (that front would be opened in the
  substituted run). -/

def subst (s : Nat → T) : T → T
  | S => S
  | var n => s n
  | app f x => app (subst s f) (subst s x)

theorem head_cases : ∀ t : T, head t = S ∨ ∃ n, head t = var n
  | S => Or.inl rfl
  | var n => Or.inr ⟨n, rfl⟩
  | app f _ => head_cases f

theorem subst_head (s : Nat → T) : ∀ a : T, head a = S → head (subst s a) = S
  | S, _ => rfl
  | var n, h => by simp [head] at h
  | app f _, h => subst_head s f h

theorem subst_args (s : Nat → T) : ∀ a : T, head a = S → args (subst s a) = (args a).map (subst s)
  | S, _ => rfl
  | var n, h => by simp [head] at h
  | app f x, h => by
    simp only [subst, args, List.map_append, List.map_cons, List.map_nil]
    rw [subst_args s f h]

/-- a step of the atom run is a step of the substituted run -/
theorem subst_step (s : Nat → T) (L L' : List T) (h : step L = some L') :
    step (L.map (subst s)) = some (L'.map (subst s)) := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.map_cons, step, subst_head s a ha, if_pos, subst_args s a ha, List.map_append]
      rfl
    · simp at h

theorem run_some_succ (k : Nat) (L L1 L2 : List T) (h1 : run k L = some L1) (h2 : step L1 = some L2) :
    run (k + 1) L = some L2 := by
  rw [run_add k 1 L L1 h1]
  simp [run, h2]

/-- **Lemma 11 (full-read principle).** Let L carry at least three data elements and let the substituted list reach a
    head normal form in N steps. Then the atom run reads an atom before step N: it reaches a list of length >= 3 whose
    front is atom-headed (in the substituted run that front, a replaced occurrence, is opened). -/
theorem lemma11 (s : Nat → T) (L : List T) (h3 : 3 ≤ dcount L) (N : Nat) (LN : List T)
    (hN : run N (L.map (subst s)) = some LN) (hlen : LN.length ≤ 2) :
    ∃ k, k < N ∧ ∃ a R n, run k L = some (a :: R) ∧ head a = var n ∧ 2 ≤ R.length := by
  have key : ∀ k, k ≤ N → (∃ j, j < k ∧ ∃ a R n, run j L = some (a :: R) ∧ head a = var n ∧ 2 ≤ R.length) ∨
      (∃ Lk, run k L = some Lk ∧ run k (L.map (subst s)) = some (Lk.map (subst s))) := by
    intro k
    induction k with
    | zero => intro _; exact Or.inr ⟨L, rfl, rfl⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨j, hj, rest⟩ | ⟨Lk, h1, h2⟩
      · exact Or.inl ⟨j, by omega, rest⟩
      · cases hs : step Lk with
        | some L' =>
          exact Or.inr ⟨L', run_some_succ k L Lk L' h1 hs,
            run_some_succ k _ _ _ h2 (subst_step s Lk L' hs)⟩
        | none =>
          -- the substituted run still steps at time k, the atom run does not: an atom-headed front
          left
          have hrest : run (N - k) (Lk.map (subst s)) = some LN := by
            have := run_add k (N - k) _ _ h2
            rw [show k + (N - k) = N by omega, hN] at this
            exact this.symm
          obtain ⟨m, hm⟩ : ∃ m, N - k = m + 1 := ⟨N - k - 1, by omega⟩
          rw [hm] at hrest
          simp only [run] at hrest
          cases hs2 : step (Lk.map (subst s)) with
          | none => rw [hs2] at hrest; simp at hrest
          | some L2 =>
            match Lk, hs, hs2, h1 with
            | a :: b :: c :: R, hs, hs2, h1 =>
              simp only [step] at hs
              split at hs
              · simp at hs
              · rename_i ha
                rcases head_cases a with h | ⟨n, hn⟩
                · exact absurd h ha
                · exact ⟨k, by omega, a, b :: c :: R, n, h1, hn, by simp⟩
            | [], _, hs2, _ => simp [step] at hs2
            | [_], _, hs2, _ => simp [step] at hs2
            | [_, _], _, hs2, _ => simp [step] at hs2
  rcases key N (Nat.le_refl N) with ⟨j, hj, rest⟩ | ⟨LN', h1, h2⟩
  · exact ⟨j, hj, rest⟩
  · exfalso
    rw [hN] at h2
    simp only [Option.some.injEq] at h2
    have hl : LN'.length ≤ 2 := by rw [← List.length_map (f := subst s), ← h2]; exact hlen
    have := dcount_run N L LN' h1
    have := dcount_le_length LN'
    omega

/-- some occurrence of the atom var 0 lies at right-depth at most d (d right edges from the root) -/
inductive RD : T → Nat → Prop
  | here (d : Nat) : RD (var 0) d
  | left {f : T} (x : T) {d : Nat} : RD f d → RD (app f x) d
  | right (f : T) {x : T} {d : Nat} : RD x d → RD (app f x) (d + 1)

theorem RD_mono {t : T} {d : Nat} (h : RD t d) : ∀ e, d ≤ e → RD t e := by
  induction h with
  | here d => intro e _; exact RD.here e
  | left x _ ih => intro e he; exact RD.left x (ih e he)
  | right f _ ih =>
    intro e he
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    exact RD.right f (ih e' (by omega))

theorem RD_head : ∀ t : T, head t = var 0 → RD t 0
  | S, h => by simp [head] at h
  | var n, h => by simp [head] at h; subst h; exact RD.here 0
  | app f x, h => RD.left x (RD_head f h)

theorem RD_args : ∀ (a e : T) (d : Nat), e ∈ args a → RD e d → RD a (d + 1)
  | S, _, _, h, _ => by simp [args] at h
  | var _, _, _, h, _ => by simp [args] at h
  | app f x, e, d, h, hr => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact RD.left x (RD_args f e d h hr)
    · exact RD.right f hr

theorem RD_app_inv {b c : T} {d : Nat} (h : RD (app b c) d) : RD b d ∨ ∃ d', d = d' + 1 ∧ RD c d' := by
  cases h with
  | left _ h => exact Or.inl h
  | right _ h => exact Or.inr ⟨_, rfl, h⟩

/-- a head step lowers the least right-depth of the marked occurrences by at most one -/
theorem RD_step (L L' : List T) (h : step L = some L') (e' : T) (he : e' ∈ L') (d : Nat) (hr : RD e' d) :
    ∃ e ∈ L, RD e (d + 1) := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_append.1 he with he | he
      · exact ⟨a, by simp, RD_args a e' d he hr⟩
      · rcases List.mem_cons.1 he with rfl | he
        · exact ⟨e', by simp, RD_mono hr _ (by omega)⟩
        · rcases List.mem_cons.1 he with rfl | he
          · rcases RD_app_inv hr with h1 | ⟨d', rfl, h2⟩
            · exact ⟨b, by simp, RD_mono h1 _ (by omega)⟩
            · exact ⟨c, by simp, RD_mono h2 _ (by omega)⟩
          · exact ⟨e', by simp [he], RD_mono hr _ (by omega)⟩
    · simp at h

theorem RD_run : ∀ (k : Nat) (L L' : List T), run k L = some L' → ∀ e' ∈ L', ∀ d, RD e' d → ∃ e ∈ L, RD e (d + k)
  | 0, L, L', h, e', he, d, hr => by simp [run] at h; subst h; exact ⟨e', he, hr⟩
  | k + 1, L, L', h, e', he, d, hr => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      obtain ⟨e1, he1, hr1⟩ := RD_run k L1 L' h e' he d hr
      obtain ⟨e0, he0, hr0⟩ := RD_step L L1 hs e1 he1 (d + k) hr1
      exact ⟨e0, he0, by rw [show d + (k + 1) = d + k + 1 by omega]; exact hr0⟩

/-- **Lemma 12 (right-depth cost).** If the run reaches, after k steps, a front headed by the marked atom (the marked
    occurrence is read), then some marked occurrence started at right-depth at most k: reading an occurrence that lies
    at right-depth D everywhere costs at least D head steps. -/
theorem lemma12 (k : Nat) (L : List T) (a : T) (R : List T) (h : run k L = some (a :: R)) (ha : head a = var 0) :
    ∃ e ∈ L, RD e k := by
  obtain ⟨e, he, hr⟩ := RD_run k L (a :: R) h a (by simp) 0 (RD_head a ha)
  exact ⟨e, he, by simpa using hr⟩

#print axioms lemma11
#print axioms lemma12
