/-
  Theorem N* (potential bound for counters), on top of Lemma 8 and Theorem J — machine-checked
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


/-! ## Theorem N* (potential bound for counters, all layer shapes) — list form

  Atoms x = var 0 and y = var 1. For an occurrence of x, its potential counts the nodes u·v on its root path that are
  LD-nodes (x in v, u atom-free, y not in v) or SUPP-nodes (x in u, v atom-free); `potT` is the maximum over the
  occurrences of x. In a list, an occurrence in element e_i also counts the atom-free elements below e_i (the spine
  nodes of S e_1 ... e_m above it with an atom-free argument). `potL` is the maximum over the list. -/

namespace T

/-- contains x = var 0 -/
def hx : T → Bool
  | S => false
  | var n => n == 0
  | app f a => hx f || hx a

/-- contains y = var 1 -/
def hy : T → Bool
  | S => false
  | var n => n == 1
  | app f a => hy f || hy a

end T

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- maximal LD + SUPP count over the occurrences of x -/
def potT : T → Nat
  | S => 0
  | var _ => 0
  | app u v => max (if hx v then potT v + b2n (nv u && !hy v) else 0) (if hx u then potT u + b2n (nv v) else 0)

/-- number of atom-free elements -/
def ncl : List T → Nat
  | [] => 0
  | e :: R => b2n (nv e) + ncl R

/-- list potential with k extra atom-free elements below the list -/
def potLo : List T → Nat → Nat
  | [], _ => 0
  | e :: R, k => max (if hx e then potT e + ncl R + k else 0) (potLo R k)

def potL (L : List T) : Nat := potLo L 0

theorem ncl_append : ∀ (A B : List T), ncl (A ++ B) = ncl A + ncl B
  | [], B => by simp [ncl]
  | e :: A, B => by simp [ncl, ncl_append A B]; omega

theorem potLo_append : ∀ (A B : List T) (k : Nat), potLo (A ++ B) k = max (potLo A (ncl B + k)) (potLo B k)
  | [], B, k => by simp [potLo]
  | e :: A, B, k => by
    simp only [List.cons_append, potLo]
    rw [potLo_append A B k, ncl_append]
    split <;> omega

theorem potLo_mono : ∀ (L : List T) (k k' : Nat), k ≤ k' → potLo L k ≤ potLo L k'
  | [], _, _, _ => by simp [potLo]
  | e :: R, k, k', h => by
    have := potLo_mono R k k' h
    simp only [potLo]
    split <;> omega

theorem hx_args : ∀ (t e : T), e ∈ args t → hx e = true → hx t = true
  | S, e, h, _ => by simp [args] at h
  | var _, e, h, _ => by simp [args] at h
  | app f v, e, h, he => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    simp only [hx, Bool.or_eq_true]
    rcases h with h | rfl
    · exact Or.inl (hx_args f e h he)
    · exact Or.inr he

theorem potLo_nox : ∀ (L : List T) (k : Nat), (∀ e ∈ L, hx e = false) → potLo L k = 0
  | [], _, _ => by simp [potLo]
  | e :: R, k, h => by
    simp only [potLo]
    rw [h e (by simp), potLo_nox R k (fun f hf => h f (by simp [hf]))]
    simp

/-- spine lemma: splitting a term into its spine arguments does not raise the potential -/
theorem spine_le : ∀ (t : T) (k : Nat), potLo (args t) k ≤ potT t + k
  | S, k => by simp [args, potLo]
  | var _, k => by simp [args, potLo]
  | app f v, k => by
    simp only [args]
    rw [potLo_append]
    simp only [potLo, ncl]
    have ih := spine_le f (b2n (nv v) + 0 + k)
    simp only [potT]
    cases hfx : hx f
    · have z : potLo (args f) (b2n (nv v) + 0 + k) = 0 := by
        apply potLo_nox; intro e he
        cases hex : hx e
        · rfl
        · have := hx_args f e he hex; rw [hfx] at this; exact absurd this (by decide)
      rw [z]
      split <;> simp <;> omega
    · simp only [ite_true]
      split <;> omega

theorem nv_app (b c : T) : nv (app b c) = (nv b && nv c) := rfl

theorem nv_hy (t : T) (h : nv t = true) : hy t = false := by
  induction t with
  | S => rfl
  | var n => simp [nv] at h
  | app f v ihf ihv =>
    simp only [nv, Bool.and_eq_true] at h
    simp [hy, ihf h.1, ihv h.2]

theorem nv_hx (t : T) (h : nv t = true) : hx t = false := by
  induction t with
  | S => rfl
  | var n => simp [nv] at h
  | app f v ihf ihv =>
    simp only [nv, Bool.and_eq_true] at h
    simp [hx, ihf h.1, ihv h.2]

/-- **N* step.** One head step does not raise the list potential, unless it is a write whose c contains x but not y. -/
theorem nstar_step (a b c : T) (R : List T) (ha : head a = S)
    (hW : ¬ (nv b = true ∧ hx c = true ∧ hy c = false)) :
    potL (args a ++ c :: app b c :: R) ≤ potL (a :: b :: c :: R) := by
  unfold potL
  rw [potLo_append]
  have hsp := spine_le a (ncl (c :: app b c :: R) + 0)
  have hz : hx a = false → potLo (args a) (ncl (c :: app b c :: R) + 0) = 0 := fun h =>
    potLo_nox _ _ (fun e he => by
      cases hex : hx e
      · rfl
      · have := hx_args a e he hex; rw [h] at this; exact absurd this (by decide))
  have i1 := nv_hx b
  have i2 := nv_hx c
  generalize potLo (args a) (ncl (c :: app b c :: R) + 0) = P at hsp hz ⊢
  simp only [potLo, ncl, nv_app, potT, hx] at hsp hz ⊢
  rcases Bool.eq_false_or_eq_true (hx a) with e1 | e1 <;>
  rcases Bool.eq_false_or_eq_true (hx b) with e2 | e2 <;>
  rcases Bool.eq_false_or_eq_true (hx c) with e3 | e3 <;>
  rcases Bool.eq_false_or_eq_true (hy c) with e4 | e4 <;>
  rcases Bool.eq_false_or_eq_true (nv b) with e5 | e5 <;>
  rcases Bool.eq_false_or_eq_true (nv c) with e6 | e6 <;>
  simp_all [b2n] <;> omega

theorem hy_args_of : ∀ (a : T), head a = S → hy a = true → ∃ e ∈ args a, hy e = true
  | S, _, h => by simp [hy] at h
  | var n, ha, _ => by simp [head] at ha
  | app f v, ha, h => by
    simp only [hy, Bool.or_eq_true] at h
    simp only [head] at ha
    rcases h with h | h
    · obtain ⟨e, he, hye⟩ := hy_args_of f ha h
      exact ⟨e, List.mem_append.2 (Or.inl he), hye⟩
    · exact ⟨v, List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)), h⟩

/-- y is never lost: a step keeps some element containing y -/
theorem hy_step (a b c : T) (R : List T) (ha : head a = S) (h : ∃ e ∈ a :: b :: c :: R, hy e = true) :
    ∃ e ∈ args a ++ c :: app b c :: R, hy e = true := by
  obtain ⟨e, he, hye⟩ := h
  simp only [List.mem_cons] at he
  rcases he with rfl | rfl | rfl | he
  · obtain ⟨e', he', h'⟩ := hy_args_of e ha hye
    exact ⟨e', by simp [he'], h'⟩
  · exact ⟨app e c, by simp, by simp [hy, hye]⟩
  · exact ⟨e, by simp, hye⟩
  · exact ⟨e, by simp [he], hye⟩

theorem hy_run : ∀ (n : Nat) (L L' : List T), run n L = some L' → (∃ e ∈ L, hy e = true) → ∃ e ∈ L', hy e = true
  | 0, L, L', h, hy0 => by simp [run] at h; subst h; exact hy0
  | n + 1, L, L', h, hy0 => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      apply hy_run n L1 L' h
      match L, hs, hy0 with
      | a :: b :: c :: R, hs, hy0 =>
        simp only [step] at hs
        split at hs
        · rename_i ha
          simp only [Option.some.injEq] at hs
          subst hs
          exact hy_step a b c R ha hy0
        · simp at hs

theorem run_split : ∀ (k : Nat) (L0 L : List T), run (k + 1) L0 = some L →
    ∃ L1, run k L0 = some L1 ∧ step L1 = some L
  | 0, L0, L, h => by
    simp only [run] at h
    cases hs : step L0 with
    | none => rw [hs] at h; simp at h
    | some L2 => rw [hs] at h; simp only [run] at h; exact ⟨L0, rfl, by rw [hs, h]⟩
  | k + 1, L0, L, h => by
    simp only [run] at h
    cases hs : step L0 with
    | none => rw [hs] at h; simp at h
    | some L2 =>
      rw [hs] at h
      obtain ⟨L1, h1, h2⟩ := run_split k L2 L h
      exact ⟨L1, by simp only [run, hs]; exact h1, h2⟩

theorem dcount_zero_nv : ∀ (R : List T), dcount R = 0 → ∀ f ∈ R, nv f = true
  | [], _, f, hf => by simp at hf
  | g :: R', hd, f, hf => by
    simp only [dcount] at hd
    have hg : nv g = true := by
      cases hng : nv g
      · simp [hng] at hd
      · rfl
    have hR' : dcount R' = 0 := by simp [hg] at hd; exact hd
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hg
    · exact dcount_zero_nv R' hR' f hf

/-- **Theorem N* (one head run).** In a head run that reaches a head normal form and contains y, the list potential
    never increases. -/
theorem nstar_run (L0 LN : List T) (N : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (hy0 : ∃ e ∈ L0, hy e = true) : ∀ k, k ≤ N → ∀ L, run k L0 = some L → potL L ≤ potL L0 := by
  intro k
  induction k with
  | zero => intro _ L h; simp [run] at h; subst h; exact Nat.le_refl _
  | succ k ih =>
    intro hk L h
    obtain ⟨L1, h1, h2⟩ := run_split k L0 L h
    have prev := ih (by omega) L1 h1
    have hyL := hy_run k L0 L1 h1 hy0
    match L1, h1, h2, hyL with
    | a :: b :: c :: R, h1, h2, hyL =>
      simp only [step] at h2
      split at h2
      · rename_i ha
        simp only [Option.some.injEq] at h2
        subst h2
        have hW : ¬ (nv b = true ∧ hx c = true ∧ hy c = false) := by
          rintro ⟨hb, hxc, hyc⟩
          have hc : nv c = false := by
            cases hnc : nv c
            · rfl
            · rw [nv_hx c hnc] at hxc; exact absurd hxc (by decide)
          have G := theoremJ_global L0 LN N k hN hlen a b c R h1 (by omega) ha hb hc
          obtain ⟨e, he, hye⟩ := hyL
          rcases List.mem_cons.1 he with rfl | he
          · rw [nv_hy e G.1] at hye; exact absurd hye (by decide)
          rcases List.mem_cons.1 he with rfl | he
          · rw [nv_hy e hb] at hye; exact absurd hye (by decide)
          rcases List.mem_cons.1 he with rfl | he
          · rw [hyc] at hye; exact absurd hye (by decide)
          rw [nv_hy e (dcount_zero_nv R G.2 e he)] at hye
          exact absurd hye (by decide)
        exact Nat.le_trans (nstar_step a b c R ha hW) prev
      · simp at h2

/-- **Theorem N* (Böhm-tree step).** The next node (a component e of the head normal form) has list potential at most the
    potential of the final list. -/
theorem nstar_node (LN : List T) (e : T) (he : e ∈ LN) : potL (args e) ≤ potL LN := by
  unfold potL
  have h1 := spine_le e 0
  induction LN with
  | nil => simp at he
  | cons g R ih =>
    simp only [potLo]
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · cases hxe : hx e
      · have z : potLo (args e) 0 = 0 := by
          apply potLo_nox; intro f hf
          cases hxf : hx f
          · rfl
          · have := hx_args e f hf hxf; rw [hxe] at this; exact absurd this (by decide)
        rw [z]; exact Nat.zero_le _
      · simp only [ite_true]; omega
    · have := ih he; omega

#print axioms nstar_step
#print axioms nstar_run
#print axioms nstar_node

/-! ## Corollary N* (layer bound): a counter cannot grow above an unread core beyond the potential -/

/-- closed one-hole contexts (the layers of a unary counter) -/
inductive Ctx where
  | hole : Ctx
  | appL : Ctx → T → Ctx
  | appR : T → Ctx → Ctx

def plug : Ctx → T → T
  | Ctx.hole, u => u
  | Ctx.appL C x, u => app (plug C u) x
  | Ctx.appR f C, u => app f (plug C u)

/-- all side terms of the context are atom-free -/
def cclosed : Ctx → Prop
  | Ctx.hole => True
  | Ctx.appL C x => cclosed C ∧ nv x = true
  | Ctx.appR f C => nv f = true ∧ cclosed C

/-- m layers: L^m[u] -/
def iter (C : Ctx) : Nat → T → T
  | 0, u => u
  | m + 1, u => plug C (iter C m u)

theorem plug_hx (u : T) : ∀ C : Ctx, cclosed C → hx (plug C u) = hx u
  | Ctx.hole, _ => rfl
  | Ctx.appL C x, h => by simp only [plug, hx, plug_hx u C h.1, nv_hx x h.2, Bool.or_false]
  | Ctx.appR f C, h => by simp only [plug, hx, plug_hx u C h.2, nv_hx f h.1, Bool.false_or]

theorem plug_hy (u : T) : ∀ C : Ctx, cclosed C → hy (plug C u) = hy u
  | Ctx.hole, _ => rfl
  | Ctx.appL C x, h => by simp only [plug, hy, plug_hy u C h.1, nv_hy x h.2, Bool.or_false]
  | Ctx.appR f C, h => by simp only [plug, hy, plug_hy u C h.2, nv_hy f h.1, Bool.false_or]

/-- **Layer lemma.** A closed layer around a term that contains x but not y adds at least one to the potential. -/
theorem layer (u : T) (hxu : hx u = true) (hyu : hy u = false) :
    ∀ C : Ctx, cclosed C → C ≠ Ctx.hole → potT u + 1 ≤ potT (plug C u)
  | Ctx.hole, _, hne => absurd rfl hne
  | Ctx.appL C x, h, _ => by
    have hx1 : hx (plug C u) = true := by rw [plug_hx u C h.1]; exact hxu
    have ih : potT u ≤ potT (plug C u) := by
      cases C with
      | hole => exact Nat.le_refl _
      | appL C' x' => have := layer u hxu hyu (Ctx.appL C' x') h.1 (by simp); omega
      | appR f' C' => have := layer u hxu hyu (Ctx.appR f' C') h.1 (by simp); omega
    simp only [plug, potT, hx1, h.2, b2n]
    simp
    omega
  | Ctx.appR f C, h, _ => by
    have hx1 : hx (plug C u) = true := by rw [plug_hx u C h.2]; exact hxu
    have hy1 : hy (plug C u) = false := by rw [plug_hy u C h.2]; exact hyu
    have ih : potT u ≤ potT (plug C u) := by
      cases C with
      | hole => exact Nat.le_refl _
      | appL C' x' => have := layer u hxu hyu (Ctx.appL C' x') h.2 (by simp); omega
      | appR f' C' => have := layer u hxu hyu (Ctx.appR f' C') h.2 (by simp); omega
    simp only [plug, potT, hx1, hy1, h.1, b2n]
    simp
    omega

theorem iter_hx (C : Ctx) (hC : cclosed C) (u : T) : ∀ m, hx (iter C m u) = hx u
  | 0 => rfl
  | m + 1 => by simp only [iter]; rw [plug_hx _ C hC, iter_hx C hC u m]

theorem iter_hy (C : Ctx) (hC : cclosed C) (u : T) : ∀ m, hy (iter C m u) = hy u
  | 0 => rfl
  | m + 1 => by simp only [iter]; rw [plug_hy _ C hC, iter_hy C hC u m]

/-- m closed layers add at least m to the potential -/
theorem iter_pot (C : Ctx) (hC : cclosed C) (hne : C ≠ Ctx.hole) (u : T) (hxu : hx u = true) (hyu : hy u = false) :
    ∀ m, potT u + m ≤ potT (iter C m u)
  | 0 => by simp [iter]
  | m + 1 => by
    have ih := iter_pot C hC hne u hxu hyu m
    have := layer (iter C m u) (by rw [iter_hx C hC]; exact hxu) (by rw [iter_hy C hC]; exact hyu) C hC hne
    simp only [iter]
    omega

/-- subterm relation -/
inductive SubT : T → T → Prop
  | refl (t : T) : SubT t t
  | left {s f : T} (a : T) : SubT s f → SubT s (app f a)
  | right (f : T) {s a : T} : SubT s a → SubT s (app f a)

theorem sub_hx {s t : T} (h : SubT s t) (hs : hx s = true) : hx t = true := by
  induction h with
  | refl => exact hs
  | left a _ ih => simp [hx, ih hs]
  | right f _ ih => simp [hx, ih hs]

/-- the potential of a subterm containing x is at most the potential of the term -/
theorem sub_pot {s t : T} (h : SubT s t) (hs : hx s = true) : potT s ≤ potT t := by
  induction h with
  | refl => exact Nat.le_refl _
  | @left s' f a h1 ih =>
    have hf := sub_hx h1 hs
    have := ih hs
    simp only [potT, hf]
    simp
    omega
  | @right f s' a h1 ih =>
    have ha := sub_hx h1 hs
    have := ih hs
    simp only [potT, ha]
    simp
    omega

theorem pot_mem : ∀ (L : List T) (e : T), e ∈ L → hx e = true → potT e ≤ potL L
  | [], _, h, _ => by simp at h
  | g :: R, e, h, hxe => by
    unfold potL at *
    simp only [potLo]
    rcases List.mem_cons.1 h with rfl | h
    · simp [hxe]; omega
    · have := pot_mem R e h hxe
      unfold potL at this
      omega

/-- **Corollary N* (layer bound).** In a head run that reaches a head normal form and contains y, no list along the run
    (in particular no component of the head normal form, i.e. the next Böhm-tree node) contains m closed layers of a
    counter around a core that contains x but not y with m larger than the starting potential. -/
theorem layer_bound (L0 LN : List T) (N : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (hy0 : ∃ e ∈ L0, hy e = true) (k : Nat) (hk : k ≤ N) (L : List T) (hL : run k L0 = some L)
    (e : T) (he : e ∈ L) (C : Ctx) (hC : cclosed C) (hne : C ≠ Ctx.hole) (u : T) (hxu : hx u = true)
    (hyu : hy u = false) (m : Nat) (hs : SubT (iter C m u) e) : m ≤ potL L0 := by
  have h1 := iter_pot C hC hne u hxu hyu m
  have hxi : hx (iter C m u) = true := by rw [iter_hx C hC]; exact hxu
  have h2 := sub_pot hs hxi
  have h3 := pot_mem L e he (sub_hx hs hxi)
  have h4 := nstar_run L0 LN N hN hlen hy0 k hk L hL
  omega

#print axioms layer_bound
