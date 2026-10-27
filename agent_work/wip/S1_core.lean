/-
  agent_work/wip/S1_core.lean (S1 agent, 2026-10-27): draft of the formalisation of the structural claim (S1).
  Base definitions copied verbatim from R3F.lean (T, args, head, step, run, occN, run_add, run_prefix).
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

/-- occurrences of the atom var n -/
def occN (n : Nat) : T → Nat
  | S => 0
  | var m => if m = n then 1 else 0
  | app f x => occN n f + occN n x

theorem run_add : ∀ (k i : Nat) (L : List T), run (k + i) L = (run k L).bind (fun L' => run i L')
  | 0, i, L => by simp [run]
  | k + 1, i, L => by
    have : k + 1 + i = (k + i) + 1 := by omega
    rw [this]
    simp only [run]
    cases step L with
    | none => simp
    | some L' => simp [run_add k i L']

theorem run_prefix (k j : Nat) (L L' : List T) (h : run k L = some L') (hj : j ≤ k) :
    ∃ Lj, run j L = some Lj ∧ run (k - j) Lj = some L' := by
  have h2 := run_add j (k - j) L
  rw [show j + (k - j) = k by omega, h] at h2
  cases hr : run j L with
  | none => rw [hr] at h2; simp at h2
  | some Lj => rw [hr] at h2; exact ⟨Lj, rfl, by simpa using h2.symm⟩

/-! ## S1 Part 1: class ranks, sorted spines, the segment invariant -/

/-- class rank: 0 = closed (no p, x, y, r; frozen atoms allowed), 1 = P (p, no x, y, r), 2 = Y (x, y or r) -/
def rk (t : T) : Nat := if occN 1 t + occN 2 t + occN 3 t ≠ 0 then 2 else if occN 0 t ≠ 0 then 1 else 0

theorem rk_le2 (t : T) : rk t ≤ 2 := by
  unfold rk; split <;> (try split) <;> omega

theorem rk_app (b c : T) : rk (app b c) = max (rk b) (rk c) := by
  unfold rk
  simp only [occN]
  by_cases h1 : occN 1 b + occN 2 b + occN 3 b = 0 <;> by_cases h2 : occN 1 c + occN 2 c + occN 3 c = 0 <;>
    by_cases h3 : occN 0 b = 0 <;> by_cases h4 : occN 0 c = 0 <;> simp_all <;> omega

theorem rk_app_left (b c : T) : rk b ≤ rk (app b c) := by rw [rk_app]; omega
theorem rk_app_right (b c : T) : rk c ≤ rk (app b c) := by rw [rk_app]; omega

/-- argument occurrences are bounded by the term's -/
theorem occN_args_le (n : Nat) : ∀ t : T, ∀ s ∈ args t, occN n s ≤ occN n t
  | S, s, hs => by simp [args] at hs
  | var _, s, hs => by simp [args] at hs
  | app f x, s, hs => by
    simp [args] at hs
    simp only [occN]
    rcases hs with hs | hs
    · have := occN_args_le n f s hs; omega
    · subst hs; omega

theorem rk_spec (t : T) : (rk t = 2 ∧ occN 1 t + occN 2 t + occN 3 t ≠ 0) ∨
    (rk t = 1 ∧ occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t ≠ 0) ∨
    (rk t = 0 ∧ occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t = 0) := by
  unfold rk
  by_cases h : occN 1 t + occN 2 t + occN 3 t ≠ 0
  · rw [if_pos h]; exact Or.inl ⟨rfl, h⟩
  · rw [if_neg h]
    by_cases h0 : occN 0 t ≠ 0
    · rw [if_pos h0]; exact Or.inr (Or.inl ⟨rfl, by omega, h0⟩)
    · rw [if_neg h0]; exact Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)

theorem rk_eq2 (t : T) : rk t = 2 ↔ occN 1 t + occN 2 t + occN 3 t ≠ 0 := by
  rcases rk_spec t with h | h | h <;> constructor <;> intro e <;> omega

theorem rk_eq1 (t : T) : rk t = 1 ↔ (occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t ≠ 0) := by
  rcases rk_spec t with h | h | h <;> constructor <;> intro e <;> omega

theorem rk_eq0 (t : T) : rk t = 0 ↔ (occN 1 t + occN 2 t + occN 3 t = 0 ∧ occN 0 t = 0) := by
  rcases rk_spec t with h | h | h <;> constructor <;> intro e <;> omega

theorem rk_cases (t : T) : rk t = 0 ∨ rk t = 1 ∨ rk t = 2 := by
  have := rk_le2 t; omega

theorem rk_mono_occ (s t : T) (h : ∀ n, occN n s ≤ occN n t) : rk s ≤ rk t := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  rcases rk_cases s with hs | hs | hs <;> rcases rk_cases t with ht | ht | ht <;> try omega
  · rw [rk_eq1] at hs; rw [rk_eq0] at ht; omega
  · rw [rk_eq2] at hs; rw [rk_eq0] at ht; omega
  · rw [rk_eq2] at hs; rw [rk_eq1] at ht; omega

theorem rk_args_le (t : T) (s : T) (hs : s ∈ args t) : rk s ≤ rk t :=
  rk_mono_occ s t (fun n => occN_args_le n t s hs)

/-- the occurrences of an S-headed term are those of its arguments -/
theorem occN_spine (n : Nat) : ∀ t : T, head t = S → occN n t = ((args t).map (occN n)).sum
  | S, _ => by simp [occN, args]
  | var _, h => by simp [head] at h
  | app f x, h => by
    simp only [head] at h
    simp [occN, args, occN_spine n f h]

theorem sum_ne_zero_mem : ∀ (l : List T), (l.map (occN 0)).sum ≠ 0 → ∃ s ∈ l, occN 0 s ≠ 0
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : occN 0 a = 0
    · simp [ha] at h
      obtain ⟨s, hs, hs0⟩ := sum_ne_zero_mem l (by simpa using h)
      exact ⟨s, by simp [hs], hs0⟩
    · exact ⟨a, by simp, ha⟩

/-- an S-headed P-term has a P-argument -/
theorem P_has_P_arg (t : T) (hS : head t = S) (h1 : rk t = 1) : ∃ s ∈ args t, rk s = 1 := by
  have h1' := (rk_eq1 t).1 h1
  have h0 : ((args t).map (occN 0)).sum ≠ 0 := by rw [← occN_spine 0 t hS]; exact h1'.2
  obtain ⟨s, hs, hs0⟩ := sum_ne_zero_mem _ h0
  refine ⟨s, hs, ?_⟩
  have hle := rk_args_le t s hs
  rw [h1] at hle
  rcases rk_cases s with h | h | h
  · exact absurd ((rk_eq0 s).1 h).2 hs0
  · exact h
  · omega

/-- hereditarily sorted spines: every S-headed subterm has its arguments sorted by rank -/
def ordT : T → Prop
  | app f x => ordT f ∧ ordT x ∧ (head f = S → ∀ a ∈ args f, rk a ≤ rk x)
  | _ => True

theorem ordT_args : ∀ t : T, ordT t → ∀ s ∈ args t, ordT s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact ordT_args f h.1 s hs
    · subst hs; exact h.2.1

def srt (L : List T) : Prop := List.Pairwise (fun a b => rk a ≤ rk b) L

theorem ordT_srt : ∀ t : T, ordT t → head t = S → srt (args t)
  | S, _, _ => by simp [srt, args]
  | var _, _, h => by simp [head] at h
  | app f x, h, hh => by
    simp only [head] at hh
    unfold srt
    simp only [args]
    rw [List.pairwise_append]
    refine ⟨ordT_srt f h.1 hh, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    exact h.2.2 hh a ha

/-- the segment invariant: ranks sorted along the list, every element hereditarily sorted -/
def Seg (L : List T) : Prop := srt L ∧ ∀ e ∈ L, ordT e

theorem seg_step (a b c : T) (R : List T) (ha : head a = S) (h : Seg (a :: b :: c :: R)) :
    Seg (args a ++ c :: app b c :: R) := by
  obtain ⟨hs, ho⟩ := h
  unfold srt at hs
  simp only [List.pairwise_cons] at hs
  obtain ⟨ha', hb', hcR, hR⟩ := hs
  have hbc' : rk b ≤ rk c := hb' c (by simp)
  have hac' : rk a ≤ rk c := ha' c (by simp)
  have hrbc : rk (app b c) = rk c := by rw [rk_app]; omega
  refine ⟨?_, ?_⟩
  · unfold srt
    rw [List.pairwise_append]
    refine ⟨ordT_srt a (ho a (by simp)) ha, ?_, ?_⟩
    · simp only [List.pairwise_cons]
      refine ⟨?_, ?_, hR⟩
      · intro x hx
        simp at hx
        rcases hx with hx | hx
        · rw [hx, hrbc]; exact Nat.le_refl _
        · exact hcR x hx
      · intro x hx; rw [hrbc]; exact hcR x hx
    · intro x hx y hy
      have hxa := rk_args_le a x hx
      simp at hy
      rcases hy with hy | hy | hy
      · subst hy; omega
      · subst hy; rw [hrbc]; omega
      · have := hcR y hy; omega
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact ordT_args a (ho a (by simp)) e he
    · rw [he]; exact ho c (by simp)
    · rw [he]
      refine ⟨ho b (by simp), ho c (by simp), ?_⟩
      intro _ x hx
      have := rk_args_le b x hx; omega
    · exact ho e (by simp [he])

theorem step_some (L L' : List T) (h : step L = some L') :
    ∃ a b c R, L = a :: b :: c :: R ∧ head a = S ∧ L' = args a ++ c :: app b c :: R := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    by_cases hS : head a = S
    · rw [if_pos hS] at h
      injection h with h
      exact ⟨a, b, c, R, rfl, hS, h.symm⟩
    · rw [if_neg hS] at h; simp at h
  | [], h => simp [step] at h
  | [_], h => simp [step] at h
  | [_, _], h => simp [step] at h

theorem run_succ_some (k : Nat) (L L' : List T) (h : run (k + 1) L = some L') :
    ∃ L1, step L = some L1 ∧ run k L1 = some L' := by
  simp only [run] at h
  cases hs : step L with
  | none => rw [hs] at h; simp at h
  | some L1 => rw [hs] at h; exact ⟨L1, rfl, h⟩

theorem seg_run : ∀ (k : Nat) (L L' : List T), Seg L → run k L = some L' → Seg L'
  | 0, L, L', h, hr => by simp [run] at hr; subst hr; exact h
  | k + 1, L, L', h, hr => by
    obtain ⟨L1, hs, hr1⟩ := run_succ_some k L L' hr
    obtain ⟨a, b, c, R, rfl, hS, rfl⟩ := step_some L L1 hs
    exact seg_run k _ L' (seg_step a b c R hS h) hr1



/-! ## S1 Part 2: the P-region, the Y-top and Lemma AB (|P| >= 3 is absorbing and forbids a proper transfer) -/

def Preg (L : List T) : List T := L.filter (fun e => rk e == 1)
def Yl (L : List T) : List T := L.filter (fun e => rk e == 2)
def Ytop (L : List T) : Option T := (Yl L).head?

theorem Preg_cons (e : T) (L : List T) : Preg (e :: L) = if rk e = 1 then e :: Preg L else Preg L := by
  unfold Preg
  by_cases h : rk e = 1 <;> simp [List.filter_cons, h]

theorem Preg_append (A B : List T) : Preg (A ++ B) = Preg A ++ Preg B := by
  unfold Preg; simp [List.filter_append]

theorem Yl_cons (e : T) (L : List T) : Yl (e :: L) = if rk e = 2 then e :: Yl L else Yl L := by
  unfold Yl
  by_cases h : rk e = 2 <;> simp [List.filter_cons, h]

theorem Yl_append (A B : List T) : Yl (A ++ B) = Yl A ++ Yl B := by
  unfold Yl; simp [List.filter_append]

theorem Preg_nil_of (L : List T) (h : ∀ e ∈ L, rk e ≠ 1) : Preg L = [] := by
  unfold Preg
  rw [List.filter_eq_nil_iff]
  intro e he; simp [h e he]

theorem Yl_nil_of (L : List T) (h : ∀ e ∈ L, rk e ≠ 2) : Yl L = [] := by
  unfold Yl
  rw [List.filter_eq_nil_iff]
  intro e he; simp [h e he]

theorem Preg_length_le (L : List T) : (Preg L).length ≤ L.length := by
  unfold Preg; exact List.length_filter_le _ _

theorem srt_tail_ge (e : T) (L : List T) (h : srt (e :: L)) : ∀ x ∈ L, rk e ≤ rk x := by
  unfold srt at h; rw [List.pairwise_cons] at h; exact h.1

theorem srt_tail (e : T) (L : List T) (h : srt (e :: L)) : srt L := by
  unfold srt at h ⊢; rw [List.pairwise_cons] at h; exact h.2

/-- Lemma AB, one step -/
theorem ab3_step (a b c : T) (R : List T) (ha : head a = S) (hs : srt (a :: b :: c :: R))
    (h3 : 3 ≤ (Preg (a :: b :: c :: R)).length) : 3 ≤ (Preg (args a ++ c :: app b c :: R)).length := by
  have hab := srt_tail_ge a _ hs b (by simp)
  have hac := srt_tail_ge a _ hs c (by simp)
  have hbc := srt_tail_ge b _ (srt_tail a _ hs) c (by simp)
  have hcR := srt_tail_ge c _ (srt_tail b _ (srt_tail a _ hs))
  rw [Preg_append, List.length_append]
  simp only [Preg_cons] at h3 ⊢
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  rcases rk_cases c with hc | hc | hc
  · have ha0 : rk a = 0 := by omega
    have hb0 : rk b = 0 := by omega
    have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
    simp only [ha0, hb0, hc, hbc0] at h3 ⊢
    simp at h3 ⊢
    omega
  · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
    simp only [hc, hbc1, if_true, List.length_cons] at h3 ⊢
    rcases rk_cases a with ha' | ha' | ha'
    · have hb' : rk b = 0 ∨ rk b = 1 := by omega
      rcases hb' with hb' | hb' <;> simp [ha', hb'] at h3 <;> omega
    · obtain ⟨s, hs', hs1⟩ := P_has_P_arg a ha ha'
      have : 1 ≤ (Preg (args a)).length := by
        unfold Preg
        apply List.length_pos_iff_exists_mem.2
        exact ⟨s, by simp [hs', hs1]⟩
      omega
    · omega
  · -- rk c = 2: every element of R has rank 2, so at most a, b are P
    have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
    rw [hR] at h3
    rcases rk_cases a with ha' | ha' | ha' <;> rcases rk_cases b with hb' | hb' | hb' <;>
      simp [ha', hb', hc] at h3 <;> omega

theorem ab3_pos3 (f b d : T) (R : List T) (hs : srt (f :: b :: d :: R))
    (h3 : 3 ≤ (Preg (f :: b :: d :: R)).length) : rk d ≤ 1 := by
  rcases rk_cases d with hd | hd | hd
  · omega
  · omega
  · exfalso
    have hdR := srt_tail_ge d _ (srt_tail b _ (srt_tail f _ hs))
    have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hdR e he; omega)
    simp only [Preg_cons, hR, hd] at h3
    rcases rk_cases f with hf | hf | hf <;> rcases rk_cases b with hb | hb | hb <;> simp [hf, hb] at h3

theorem ab3_run : ∀ (k : Nat) (L L' : List T), Seg L → 3 ≤ (Preg L).length → run k L = some L' →
    3 ≤ (Preg L').length
  | 0, L, L', _, h3, hr => by simp [run] at hr; subst hr; exact h3
  | k + 1, L, L', hS, h3, hr => by
    obtain ⟨L1, hs, hr1⟩ := run_succ_some k L L' hr
    obtain ⟨a, b, c, R, rfl, ha, rfl⟩ := step_some _ L1 hs
    exact ab3_run k _ L' (seg_step a b c R ha hS) (ab3_step a b c R ha hS.1 h3) hr1

/-- before a proper transfer (a p-front whose third element contains x, y or r) the P-region has <= 2 elements -/
theorem ab3_bound (L1 : List T) (hS : Seg L1) (T' : Nat) (f b d : T) (R : List T)
    (hT : run T' L1 = some (f :: b :: d :: R)) (hd : rk d = 2) :
    ∀ t L, t ≤ T' → run t L1 = some L → (Preg L).length ≤ 2 := by
  intro t L ht hL
  rcases Nat.lt_or_ge (Preg L).length 3 with h3 | h3'
  · omega
  exfalso
  obtain ⟨Lt, hLt, hrest⟩ := run_prefix T' t L1 _ hT ht
  rw [hL] at hLt; injection hLt with hLt; subst hLt
  have hSL : Seg L := seg_run t L1 L hS hL
  have := ab3_run (T' - t) L _ hSL h3' hrest
  have hsT := (seg_run T' L1 _ hS hT).1
  have := ab3_pos3 f b d R hsT this
  omega

/-! ## S1 Part 3: spine and subterm toolkit -/

/-- subterm relation -/
def sub (u : T) : T → Prop
  | S => u = S
  | var n => u = var n
  | app f x => u = app f x ∨ sub u f ∨ sub u x

theorem sub_refl : ∀ t : T, sub t t
  | S => rfl
  | var _ => rfl
  | app _ _ => Or.inl rfl

theorem sub_trans : ∀ (u v t : T), sub u v → sub v t → sub u t
  | u, v, S, h1, h2 => by simp [sub] at h2; subst h2; exact h1
  | u, v, var n, h1, h2 => by simp [sub] at h2; subst h2; exact h1
  | u, v, app f x, h1, h2 => by
    rcases h2 with h2 | h2 | h2
    · subst h2; exact h1
    · exact Or.inr (Or.inl (sub_trans u v f h1 h2))
    · exact Or.inr (Or.inr (sub_trans u v x h1 h2))

theorem sub_left (f x : T) : sub f (app f x) := Or.inr (Or.inl (sub_refl f))
theorem sub_right (f x : T) : sub x (app f x) := Or.inr (Or.inr (sub_refl x))

theorem sub_of_args : ∀ (t s : T), s ∈ args t → sub s t
  | S, s, hs => by simp [args] at hs
  | var _, s, hs => by simp [args] at hs
  | app f x, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact sub_trans s f _ (sub_of_args f s hs) (sub_left f x)
    · subst hs; exact sub_right f s

/-- occurrence counts of subterms are bounded -/
theorem occN_sub_le (n : Nat) : ∀ (u t : T), sub u t → occN n u ≤ occN n t
  | u, S, h => by simp [sub] at h; subst h; exact Nat.le_refl _
  | u, var m, h => by simp [sub] at h; subst h; exact Nat.le_refl _
  | u, app f x, h => by
    rcases h with h | h | h
    · subst h; exact Nat.le_refl _
    · have := occN_sub_le n u f h; simp only [occN]; omega
    · have := occN_sub_le n u x h; simp only [occN]; omega

/-- the rank of an S-headed term is bounded by the ranks of its arguments -/
theorem rk_le_of_args (t : T) (hS : head t = S) (k : Nat) (h : ∀ s ∈ args t, rk s ≤ k) : rk t ≤ k := by
  have hsum : ∀ n, (∀ s ∈ args t, occN n s = 0) → occN n t = 0 := by
    intro n hn
    rw [occN_spine n t hS]
    have : ∀ (l : List T), (∀ s ∈ l, occN n s = 0) → (l.map (occN n)).sum = 0 := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => intro hl; simp [hl a (by simp), ih (fun s hs => hl s (by simp [hs]))]
    exact this _ hn
  have hm : ∀ m, (∀ s ∈ args t, occN m s = 0) → occN m t = 0 := hsum
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have e1 : occN 1 t = 0 := hm 1 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
    have e2 : occN 2 t = 0 := hm 2 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
    have e3 : occN 3 t = 0 := hm 3 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · have e0 : occN 0 t = 0 :=
        hm 0 (fun s hs => by have := h s hs; rcases rk_spec s with h' | h' | h' <;> omega)
      rcases rk_spec t with h' | h' | h' <;> omega
    · rcases rk_spec t with h' | h' | h' <;> omega
  · have := rk_le2 t; omega

/-- every sorted list of ranks splits as closed ++ P ++ Y -/
theorem srt_split : ∀ (L : List T), srt L → ∃ C P Y, L = C ++ P ++ Y ∧ (∀ e ∈ C, rk e = 0) ∧
    (∀ e ∈ P, rk e = 1) ∧ (∀ e ∈ Y, rk e = 2)
  | [], _ => ⟨[], [], [], by simp, by simp, by simp, by simp⟩
  | e :: L, h => by
    obtain ⟨C, P, Y, hL, hC, hP, hY⟩ := srt_split L (srt_tail e L h)
    have hge := srt_tail_ge e L h
    rcases rk_cases e with he | he | he
    · exact ⟨e :: C, P, Y, by simp [hL], by simp [he]; exact hC, hP, hY⟩
    · have hC0 : C = [] := by
        cases C with
        | nil => rfl
        | cons x C' => exfalso; have := hge x (by simp [hL]); have := hC x (by simp); omega
      exact ⟨[], e :: P, Y, by simp [hL, hC0], by simp, by simp [he]; exact hP, hY⟩
    · have hC0 : C = [] := by
        cases C with
        | nil => rfl
        | cons x C' => exfalso; have := hge x (by simp [hL]); have := hC x (by simp); omega
      have hP0 : P = [] := by
        cases P with
        | nil => rfl
        | cons x P' => exfalso; have := hge x (by simp [hL, hC0]); have := hP x (by simp); omega
      exact ⟨[], [], e :: Y, by simp [hL, hC0, hP0], by simp, by simp, by simp [he]; exact hY⟩

theorem Preg_split (C P Y : List T) (hC : ∀ e ∈ C, rk e = 0) (hP : ∀ e ∈ P, rk e = 1)
    (hY : ∀ e ∈ Y, rk e = 2) : Preg (C ++ P ++ Y) = P := by
  rw [Preg_append, Preg_append, Preg_nil_of C (fun e he => by rw [hC e he]; omega),
    Preg_nil_of Y (fun e he => by rw [hY e he]; omega)]
  unfold Preg
  simp only [List.nil_append, List.append_nil]
  rw [List.filter_eq_self]
  intro e he; simp [hP e he]

theorem Yl_split (C P Y : List T) (hC : ∀ e ∈ C, rk e = 0) (hP : ∀ e ∈ P, rk e = 1)
    (hY : ∀ e ∈ Y, rk e = 2) : Yl (C ++ P ++ Y) = Y := by
  rw [Yl_append, Yl_append, Yl_nil_of C (fun e he => by rw [hC e he]; omega),
    Yl_nil_of P (fun e he => by rw [hP e he]; omega)]
  unfold Yl
  simp only [List.nil_append]
  rw [List.filter_eq_self]
  intro e he; simp [hY e he]

/-- spine prefixes: an argument z of an S-headed term a sits on a left-spine prefix  M.z  of a -/
theorem spine_prefix : ∀ (a : T), head a = S → ∀ (A B : List T) (z : T), args a = A ++ z :: B →
    ∃ M, head M = S ∧ args M = A ∧ sub (app M z) a
  | S, _, A, B, z, h => by simp [args] at h
  | var _, hS, _, _, _, _ => by simp [head] at hS
  | app f x, hS, A, B, z, h => by
    simp only [head] at hS
    simp only [args] at h
    rcases List.eq_nil_or_concat B with hB | ⟨B', y', hB⟩
    · subst hB
      simp at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      exact ⟨f, hS, h1, sub_refl _⟩
    · subst hB
      rw [List.concat_eq_append] at h
      have h' : args f = A ++ z :: B' := by
        have := h
        rw [show A ++ z :: (B' ++ [y']) = (A ++ z :: B') ++ [y'] by simp] at this
        exact (List.append_inj' this rfl).1
      obtain ⟨M, hM, hMA, hsub⟩ := spine_prefix f hS A B' z h'
      exact ⟨M, hM, hMA, sub_trans _ _ _ hsub (sub_left f x)⟩

/-- if z is the LAST argument, a = M.z -/
theorem spine_last (a : T) (hS : head a = S) (A : List T) (z : T) (h : args a = A ++ [z]) :
    ∃ M, head M = S ∧ args M = A ∧ a = app M z := by
  match a, hS, h with
  | S, _, h => simp [args] at h
  | var _, hS, _ => simp [head] at hS
  | app f x, hS, h =>
    simp only [head] at hS
    simp only [args] at h
    have := List.append_inj' h rfl
    obtain ⟨h1, h2⟩ := this
    simp at h2; subst h2
    exact ⟨f, hS, h1, rfl⟩

/-! ## S1 Part 4: Claim C (no 2P term alone in the P-region; no subterm K.Z) -/

/-- a 2P term: an application of two P-terms -/
def twoP : T → Prop
  | app U V => rk U = 1 ∧ rk V = 1
  | _ => False

theorem twoP_rk (Z : T) (h : twoP Z) : rk Z = 1 := by
  match Z, h with
  | app U V, h => rw [rk_app, h.1, h.2]; rfl

/-- no subterm K.Z with K closed and Z a 2P term -/
def noKZ : T → Prop
  | app f x => noKZ f ∧ noKZ x ∧ ¬ (rk f = 0 ∧ twoP x)
  | _ => True

theorem noKZ_sub : ∀ (u t : T), noKZ t → sub u t → noKZ u
  | u, S, _, h => by simp [sub] at h; subst h; trivial
  | u, var n, _, h => by simp [sub] at h; subst h; trivial
  | u, app f x, hn, h => by
    rcases h with h | h | h
    · subst h; exact hn
    · exact noKZ_sub u f hn.1 h
    · exact noKZ_sub u x hn.2.1 h

def IC1 (L : List T) : Prop := ∀ Z, Preg L = [Z] → ¬ twoP Z
def IC2 (L : List T) : Prop := ∀ e ∈ L, noKZ e

/-- the first P-argument of a noKZ term is not 2P -/
theorem first_P_arg_not2P (a : T) (hS : head a = S) (ho : ordT a) (hn : noKZ a) (Z : T) (rest : List T)
    (hP : Preg (args a) = Z :: rest) : ¬ twoP Z := by
  intro hZ
  obtain ⟨C, P, Y, hs, hC, hPP, hY⟩ := srt_split (args a) (ordT_srt a ho hS)
  have hPe : Preg (args a) = P := by rw [hs]; exact Preg_split C P Y hC hPP hY
  rw [hPe] at hP; subst hP
  obtain ⟨M, hM, hMA, hsub⟩ := spine_prefix a hS C (rest ++ Y) Z (by rw [hs]; simp)
  have hM0 : rk M ≤ 0 := rk_le_of_args M hM 0 (fun s hs' => by rw [hMA] at hs'; exact Nat.le_of_eq (hC s hs'))
  have := noKZ_sub _ _ hn hsub
  exact this.2.2 ⟨by omega, hZ⟩

theorem srt3 (a b c : T) (R : List T) (h : srt (a :: b :: c :: R)) :
    rk a ≤ rk b ∧ rk b ≤ rk c ∧ ∀ x ∈ R, rk c ≤ rk x :=
  ⟨srt_tail_ge a _ h b (by simp), srt_tail_ge b _ (srt_tail a _ h) c (by simp),
   srt_tail_ge c _ (srt_tail b _ (srt_tail a _ h))⟩

theorem Preg_args_closed (a : T) (ha : rk a = 0) : Preg (args a) = [] :=
  Preg_nil_of _ (fun e he => by have := rk_args_le a e he; omega)

theorem Yl_args_le1 (a : T) (ha : rk a ≤ 1) : Yl (args a) = [] :=
  Yl_nil_of _ (fun e he => by have := rk_args_le a e he; omega)

theorem ic_step (a b c : T) (R : List T) (ha : head a = S) (hseg : Seg (a :: b :: c :: R))
    (h2 : (Preg (a :: b :: c :: R)).length ≤ 2) (h2' : (Preg (args a ++ c :: app b c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hc2 : IC2 (a :: b :: c :: R)) :
    IC1 (args a ++ c :: app b c :: R) ∧ IC2 (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hna : noKZ a := hc2 a (by simp)
  have hoa : ordT a := hseg.2 a (by simp)
  refine ⟨?_, ?_⟩
  · intro Z hZ hZ2
    rw [Preg_append] at hZ
    simp only [Preg_cons] at hZ h2
    rcases rk_cases c with hc | hc | hc
    · have ha0 : rk a = 0 := by omega
      have hb0 : rk b = 0 := by omega
      have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
      rw [Preg_args_closed a ha0] at hZ
      simp only [hc, hbc0] at hZ
      simp at hZ
      apply hc1 Z _ hZ2
      simp only [Preg_cons, ha0, hb0, hc]; simpa using hZ
    · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      simp only [hc, hbc1, if_true] at hZ
      have := congrArg List.length hZ
      simp at this
      omega
    · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
      have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
      simp only [hc, hbc2, hR] at hZ
      simp at hZ
      exact first_P_arg_not2P a ha hoa hna Z [] hZ hZ2
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact noKZ_sub e a hna (sub_of_args a e he)
    · rw [he]; exact hc2 c (by simp)
    · rw [he]
      refine ⟨hc2 b (by simp), hc2 c (by simp), ?_⟩
      rintro ⟨hb0, hc2P⟩
      have hc1' : rk c = 1 := twoP_rk c hc2P
      have ha0 : rk a = 0 := by omega
      have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      rw [Preg_append, Preg_args_closed a ha0] at h2'
      simp only [Preg_cons, hc1', hbc1, if_true, List.nil_append, List.length_cons] at h2'
      have hR : Preg R = [] := List.eq_nil_of_length_eq_zero (by omega)
      apply hc1 c _ hc2P
      simp only [Preg_cons, ha0, hb0, hc1', hR]; simp
    · exact hc2 e (by simp [he])

/-! ## S1 Part 5: FI-W (every pair-top above w and every P-prefix applied to w lies in the X-sequence of c0) -/

/-- U is the unique P-argument of the S-headed term M -/
def onlyP (M U : T) : Prop := head M = S ∧ Preg (args M) = [U]

/-- the X-sequence: X_0 = c0, X_{i+1} = the unique P-argument of X_i -/
inductive inX (c0 : T) : T → Prop
  | base : inX c0 c0
  | next (M U : T) : inX c0 M → onlyP M U → inX c0 U

def wsubOK (w c0 : T) : T → Prop
  | app f x => wsubOK w c0 f ∧ wsubOK w c0 x ∧ (x = w → rk f = 1 → inX c0 f)
  | _ => True

theorem wsubOK_sub (w c0 : T) : ∀ (u t : T), wsubOK w c0 t → sub u t → wsubOK w c0 u
  | u, S, _, h => by simp [sub] at h; subst h; trivial
  | u, var n, _, h => by simp [sub] at h; subst h; trivial
  | u, app f x, hn, h => by
    rcases h with h | h | h
    · subst h; exact hn
    · exact wsubOK_sub w c0 u f hn.1 h
    · exact wsubOK_sub w c0 u x hn.2.1 h

def IW (w c0 : T) (L : List T) : Prop := (∀ e ∈ L, wsubOK w c0 e) ∧ (∀ U, Preg L = [U, w] → inX c0 U)

/-- releasing the P-pair [U, z] from an S-headed front: the prefix M.z with M's unique P-argument U -/
theorem release_pair (a : T) (hS : head a = S) (ho : ordT a) (U z : T) (hP : Preg (args a) = [U, z]) :
    ∃ M, head M = S ∧ rk M = 1 ∧ onlyP M U ∧ sub (app M z) a ∧
      ∃ C Y, args a = C ++ U :: z :: Y ∧ args M = C ++ [U] ∧ (∀ e ∈ C, rk e = 0) ∧ (∀ e ∈ Y, rk e = 2) := by
  obtain ⟨C, P, Y, hs, hC, hPP, hY⟩ := srt_split (args a) (ordT_srt a ho hS)
  have hPe : Preg (args a) = P := by rw [hs]; exact Preg_split C P Y hC hPP hY
  rw [hPe] at hP; subst hP
  have hU : rk U = 1 := hPP U (by simp)
  obtain ⟨M, hM, hMA, hsub⟩ := spine_prefix a hS (C ++ [U]) Y z (by rw [hs]; simp)
  have hMle : rk M ≤ 1 := rk_le_of_args M hM 1 (fun s hs' => by
    rw [hMA] at hs'; simp at hs'
    rcases hs' with hs' | hs'
    · rw [hC s hs']; omega
    · rw [hs']; omega)
  have hMge : 1 ≤ rk M := by
    have := rk_args_le M U (by rw [hMA]; simp); omega
  refine ⟨M, hM, by omega, ⟨hM, ?_⟩, hsub, C, Y, by rw [hs]; simp, hMA, hC, hY⟩
  rw [hMA]
  have := Preg_split C [U] [] hC (by simp [hU]) (by simp)
  simpa using this

theorem iw_step (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1) (a b c : T) (R : List T) (ha : head a = S)
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (hiw : IW w c0 (a :: b :: c :: R)) : IW w c0 (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hoa : ordT a := hseg.2 a (by simp)
  have hwa : wsubOK w c0 a := hiw.1 a (by simp)
  refine ⟨?_, ?_⟩
  · intro e he
    simp at he
    rcases he with he | he | he | he
    · exact wsubOK_sub w c0 e a hwa (sub_of_args a e he)
    · rw [he]; exact hiw.1 c (by simp)
    · rw [he]
      refine ⟨hiw.1 b (by simp), hiw.1 c (by simp), ?_⟩
      intro hcw hb1
      subst hcw
      have ha0 : rk a ≠ 1 := by
        intro ha1
        simp only [Preg_cons, ha1, hb1, hwr, if_true, List.length_cons] at h2; omega
      have ha0' : rk a = 0 := by omega
      have hR : Preg R = [] := by
        have h2'' := h2
        simp [Preg_cons, ha0', hb1, hwr] at h2''
        first | exact h2'' | exact List.eq_nil_of_length_eq_zero (by omega)
      apply hiw.2 b
      simp [Preg_cons, ha0', hb1, hwr, hR]
    · exact hiw.1 e (by simp [he])
  · intro U hU
    rw [Preg_append] at hU
    rcases rk_cases c with hc | hc | hc
    · have ha0 : rk a = 0 := by omega
      have hb0 : rk b = 0 := by omega
      have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
      rw [Preg_args_closed a ha0] at hU
      simp only [Preg_cons, hc, hbc0] at hU
      apply hiw.2 U
      simp only [Preg_cons, ha0, hb0, hc]; simpa using hU
    · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      have ha0 : rk a = 0 := by
        rcases rk_cases a with h | h | h
        · exact h
        · exfalso
          have hb1 : rk b = 1 := by omega
          simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
        · omega
      rw [Preg_args_closed a ha0] at hU
      simp only [Preg_cons, hc, hbc1, if_true, List.nil_append] at hU
      have h1 := List.cons.inj hU
      have h2' := List.cons.inj h1.2
      have hbcw : app b c = w := h2'.1
      rw [hw] at hbcw
      injection hbcw with _ hcc
      rw [← h1.1, hcc]
      exact inX.base
    · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
      have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
      simp only [Preg_cons, hc, hbc2, hR] at hU
      simp at hU
      obtain ⟨M, _, hM1, hMU, hsub, _⟩ := release_pair a ha hoa U w hU
      have hwM := wsubOK_sub w c0 _ a hwa hsub
      exact inX.next M U (hwM.2.2 rfl hM1) hMU

/-! ## S1 Part 6: FI-A (2P terms in the P-region over the bare y were created over the bare y) -/

/-- U.V was created at some time s <= t by a step with the bare y as Y-top: run s L1 = k :: U :: V :: y :: R -/
def Good (L1 : List T) (t : Nat) (U V : T) : Prop :=
  ∃ s, s ≤ t ∧ ∃ k R, run s L1 = some (k :: U :: V :: var 2 :: R)

/-- every 2P term on the right spine of a term is Good -/
def rsg (L1 : List T) (t : Nat) : T → Prop
  | app U V => (rk U = 1 ∧ rk V = 1) → (Good L1 t U V ∧ rsg L1 t V)
  | _ => True

theorem rsg_mono (L1 : List T) (t t' : Nat) (htt : t ≤ t') : ∀ Z, rsg L1 t Z → rsg L1 t' Z
  | S, _ => trivial
  | var _, _ => trivial
  | app U V, h => by
    intro hUV
    obtain ⟨⟨s, hs, hk⟩, hr⟩ := h hUV
    exact ⟨⟨s, by omega, hk⟩, rsg_mono L1 t t' htt V hr⟩

theorem rsg_of_not2P (L1 : List T) (t : Nat) (Z : T) (h : ¬ twoP Z) : rsg L1 t Z := by
  match Z, h with
  | S, _ => trivial
  | var _, _ => trivial
  | app U V, h => intro hUV; exact absurd hUV h

def IA (L1 : List T) (t : Nat) (L : List T) : Prop :=
  ∀ Z, twoP Z → ((Z ∈ Preg L ∧ Ytop L = some (var 2)) ∨ (∃ e ∈ L, sub (app Z (var 2)) e)) → rsg L1 t Z

/-- releasing a 2P term as the LOWER element of a P-pair: the front is M'.Z (P-front) or (M'.Z).y'... -/
theorem pair_prefix (a : T) (hS : head a = S) (ho : ordT a) (V' Z : T) (hP : Preg (args a) = [V', Z]) :
    ∃ M', rk M' = 1 ∧ (Yl (args a) = [] → a = app M' Z) ∧
      (∀ y' Y', Yl (args a) = y' :: Y' → sub (app (app M' Z) y') a) := by
  obtain ⟨C, P, Y, hs, hC, hPP, hY⟩ := srt_split (args a) (ordT_srt a ho hS)
  have hPe : Preg (args a) = P := by rw [hs]; exact Preg_split C P Y hC hPP hY
  have hYe : Yl (args a) = Y := by rw [hs]; exact Yl_split C P Y hC hPP hY
  rw [hPe] at hP; subst hP
  have hV : rk V' = 1 := hPP V' (by simp)
  -- the prefix with arguments C ++ [V']
  obtain ⟨M', hM', hMA', _⟩ := spine_prefix a hS (C ++ [V']) Y Z (by rw [hs]; simp)
  have hMle : rk M' ≤ 1 := rk_le_of_args M' hM' 1 (fun s hs' => by
    rw [hMA'] at hs'; simp at hs'
    rcases hs' with hs' | hs'
    · rw [hC s hs']; omega
    · rw [hs']; omega)
  have hMge : 1 ≤ rk M' := by have := rk_args_le M' V' (by rw [hMA']; simp); omega
  refine ⟨M', by omega, ?_, ?_⟩
  · intro hY0
    rw [hYe] at hY0; subst hY0
    obtain ⟨M2, hM2, hMA2, ha⟩ := spine_last a hS (C ++ [V']) Z (by rw [hs]; simp)
    -- M2 and M' have the same spine, hence are equal
    have : M2 = M' := by
      have key : ∀ (m1 m2 : T), head m1 = S → head m2 = S → args m1 = args m2 → m1 = m2 := by
        intro m1; induction m1 with
        | S => intro m2 _ h2 he
               match m2, h2, he with
               | S, _, _ => rfl
               | var _, h2, _ => simp [head] at h2
               | app f x, _, he => simp [args] at he
        | var _ => intro m2 h1; simp [head] at h1
        | app f x ihf _ =>
          intro m2 h1 h2 he
          match m2, h2, he with
          | S, _, he => simp [args] at he
          | var _, h2, _ => simp [head] at h2
          | app g z, h2, he =>
            simp only [args] at he
            have := List.append_inj' he rfl
            simp at this
            rw [ihf g (by simpa [head] using h1) (by simpa [head] using h2) this.1, this.2]
      exact key M2 M' hM2 hM' (by rw [hMA2, hMA'])
    rw [ha, this]
  · intro y' Y' hY'
    rw [hYe] at hY'; subst hY'
    obtain ⟨M2, hM2, hMA2, hsub⟩ := spine_prefix a hS (C ++ [V', Z]) Y' y' (by rw [hs]; try simp)
    obtain ⟨M3, hM3, hMA3, hM2e⟩ := spine_last M2 hM2 (C ++ [V']) Z (by rw [hMA2]; simp)
    have key : ∀ (m1 m2 : T), head m1 = S → head m2 = S → args m1 = args m2 → m1 = m2 := by
      intro m1; induction m1 with
      | S => intro m2 _ h2 he
             match m2, h2, he with
             | S, _, _ => rfl
             | var _, h2, _ => simp [head] at h2
             | app f x, _, he => simp [args] at he
      | var _ => intro m2 h1; simp [head] at h1
      | app f x ihf _ =>
        intro m2 h1 h2 he
        match m2, h2, he with
        | S, _, he => simp [args] at he
        | var _, h2, _ => simp [head] at h2
        | app g z, h2, he =>
          simp only [args] at he
          have := List.append_inj' he rfl
          simp at this
          rw [ihf g (by simpa [head] using h1) (by simpa [head] using h2) this.1, this.2]
    have : M3 = M' := key M3 M' hM3 hM' (by rw [hMA3, hMA'])
    rw [hM2e, this] at hsub
    exact hsub

theorem Ytop_third (a b c : T) (R : List T) (ha : rk a ≤ 1) (hb : rk b ≤ 1) (hc : rk c = 2) :
    Ytop (a :: b :: c :: R) = some c := by
  unfold Ytop
  simp only [Yl_cons]
  have ha' : rk a ≠ 2 := by omega
  have hb' : rk b ≠ 2 := by omega
  simp [ha', hb', hc]

theorem Yl_args_ne_nil (a : T) (hS : head a = S) (ha : rk a = 2) : Yl (args a) ≠ [] := by
  intro h
  have : rk a ≤ 1 := rk_le_of_args a hS 1 (fun s hs => by
    rcases rk_cases s with h' | h' | h'
    · omega
    · omega
    · exfalso
      have : s ∈ Yl (args a) := by unfold Yl; simp [hs, h']
      rw [h] at this; simp at this)
  omega

/-- a list of length <= 2 containing Z -/
theorem mem_short (P : List T) (Z : T) (hZ : Z ∈ P) (hl : P.length ≤ 2) :
    P = [Z] ∨ (∃ V, P = [Z, V]) ∨ (∃ V, P = [V, Z]) := by
  match P, hZ, hl with
  | [x], hZ, _ => simp at hZ; subst hZ; exact Or.inl rfl
  | [x1, x2], hZ, _ =>
    simp at hZ
    rcases hZ with h | h
    · subst h; exact Or.inr (Or.inl ⟨x2, rfl⟩)
    · subst h; exact Or.inr (Or.inr ⟨x1, rfl⟩)
  | _ :: _ :: _ :: _, _, hl => simp at hl

theorem rk_var2 : rk (var 2) = 2 := by unfold rk; simp [occN]

theorem ia_step (L1 : List T) (t : Nat) (a b c : T) (R : List T) (ha : head a = S)
    (hrun : run t L1 = some (a :: b :: c :: R))
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (h2' : (Preg (args a ++ c :: app b c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hc2 : IC2 (a :: b :: c :: R))
    (hc1' : IC1 (args a ++ c :: app b c :: R))
    (hia : IA L1 t (a :: b :: c :: R)) : IA L1 (t + 1) (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hna : noKZ a := hc2 a (by simp)
  have hoa : ordT a := hseg.2 a (by simp)
  have mono : ∀ Z, rsg L1 t Z → rsg L1 (t + 1) Z := rsg_mono L1 t (t + 1) (by omega)
  intro Z hZ hcase
  rcases hcase with ⟨hZin, hY⟩ | ⟨e, he, hsub⟩
  · rw [Preg_append] at hZin
    unfold Ytop at hY
    rw [Yl_append] at hY
    rcases rk_cases c with hc | hc | hc
    · have ha0 : rk a = 0 := by omega
      have hb0 : rk b = 0 := by omega
      have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
      rw [Preg_args_closed a ha0] at hZin
      rw [Yl_args_le1 a (by omega)] at hY
      simp only [Preg_cons, Yl_cons, hc, hbc0] at hZin hY
      simp at hZin hY
      apply mono; apply hia Z hZ; left
      refine ⟨by simp only [Preg_cons, ha0, hb0, hc]; simpa using hZin, ?_⟩
      unfold Ytop; simp only [Yl_cons, ha0, hb0, hc]; simpa using hY
    · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
      have ha0 : rk a = 0 := by
        rcases rk_cases a with h | h | h
        · exact h
        · exfalso
          have hb1 : rk b = 1 := by omega
          simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
        · omega
      rw [Preg_args_closed a ha0] at hZin
      rw [Yl_args_le1 a (by omega)] at hY
      have hc2' : rk c ≠ 2 := by omega
      have hbc2 : rk (app b c) ≠ 2 := by omega
      simp only [Preg_cons, Yl_cons, hc, hbc1, hc2', hbc2, if_true, if_false, List.nil_append] at hZin hY
      simp at hY
      have hYL : Ytop (a :: b :: c :: R) = some (var 2) := by
        unfold Ytop; simp only [Yl_cons]
        have ha2 : rk a ≠ 2 := by omega
        have hb2 : rk b ≠ 2 := by omega
        simp [ha2, hb2, hc2', hY]
      simp at hZin
      rcases hZin with hZc | hZbc | hZR
      · subst hZc
        apply mono; apply hia Z hZ; left
        refine ⟨?_, hYL⟩
        simp only [Preg_cons, ha0, hc]
        by_cases hb1 : rk b = 1 <;> simp [hb1]
      · subst hZbc
        obtain ⟨hb1, _⟩ := hZ
        intro _
        have hR : Preg R = [] := by
          have h2'' := h2
          simp [Preg_cons, ha0, hb1, hc] at h2''
          first | exact h2'' | exact List.eq_nil_of_length_eq_zero (by omega)
        have hR2 : ∀ x ∈ R, rk x = 2 := by
          intro x hx
          have := hcR x hx
          rcases rk_cases x with h | h | h
          · omega
          · exfalso
            have : x ∈ Preg R := by unfold Preg; simp [hx, h]
            rw [hR] at this; simp at this
          · exact h
        have hYR : Yl R = R := by
          unfold Yl; rw [List.filter_eq_self]; intro x hx; simp [hR2 x hx]
        rw [hYR] at hY
        obtain ⟨R', hR'⟩ : ∃ R', R = var 2 :: R' := by
          match R, hY with
          | x :: R', hY => simp at hY; exact ⟨R', by rw [hY]⟩
        refine ⟨⟨t, by omega, a, R', by rw [hrun, hR']⟩, ?_⟩
        by_cases h2c : twoP c
        · apply mono; apply hia c h2c; left
          exact ⟨by simp only [Preg_cons, ha0, hb1, hc]; simp, hYL⟩
        · exact rsg_of_not2P L1 (t + 1) c h2c
      · apply mono; apply hia Z hZ; left
        refine ⟨?_, hYL⟩
        simp only [Preg_cons, ha0, hc]
        by_cases hb1 : rk b = 1 <;> simp [hb1, hZR]
    · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
      have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
      have hPL' : Preg (args a ++ c :: app b c :: R) = Preg (args a) := by
        rw [Preg_append]; simp only [Preg_cons, hc, hbc2, hR]; simp
      simp only [Preg_cons, hc, hbc2, hR] at hZin
      simp at hZin
      have hlen : (Preg (args a)).length ≤ 2 := by rw [← hPL']; exact h2'
      rcases rk_cases a with ha' | ha' | ha'
      · rw [Preg_args_closed a ha'] at hZin; simp at hZin
      · -- P-front
        rw [Yl_args_le1 a (by omega)] at hY
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        rcases mem_short _ Z hZin hlen with hP | ⟨V', hP⟩ | ⟨V', hP⟩
        · exact absurd hZ (hc1' Z (by rw [hPL', hP]))
        · exact absurd hZ (first_P_arg_not2P a ha hoa hna Z [V'] hP)
        · obtain ⟨M', hM'1, haM, _⟩ := pair_prefix a ha hoa V' Z hP
          have haeq : a = app M' Z := haM (Yl_args_le1 a (by omega))
          have hZ1 : rk Z = 1 := twoP_rk Z hZ
          have h2a : twoP a := by rw [haeq]; exact ⟨hM'1, hZ1⟩
          have hb1 : rk b = 1 := by
            rcases rk_cases b with h | h | h
            · omega
            · exact h
            · exfalso
              apply hc1 a _ h2a
              have hb2 : rk b ≠ 1 := by omega
              have hc2' : rk c ≠ 1 := by omega
              simp only [Preg_cons, ha', hb2, hc2', hR]; simp
          have hYL : Ytop (a :: b :: c :: R) = some (var 2) := by
            rw [Ytop_third a b c R (by omega) (by omega) hc, hY]
          have := hia a h2a (Or.inl ⟨by simp only [Preg_cons, ha']; simp, hYL⟩)
          rw [haeq] at this
          exact mono Z (this ⟨hM'1, hZ1⟩).2
      · -- Y-front
        obtain ⟨y', Y', hYa⟩ : ∃ y' Y', Yl (args a) = y' :: Y' := by
          have hne := Yl_args_ne_nil a ha ha'
          cases h : Yl (args a) with
          | nil => exact absurd h hne
          | cons y' Y' => exact ⟨y', Y', rfl⟩
        rw [hYa] at hY
        simp at hY
        subst hY
        rcases mem_short _ Z hZin hlen with hP | ⟨V', hP⟩ | ⟨V', hP⟩
        · exact absurd hZ (hc1' Z (by rw [hPL', hP]))
        · exact absurd hZ (first_P_arg_not2P a ha hoa hna Z [V'] hP)
        · obtain ⟨M', hM'1, _, hsubA⟩ := pair_prefix a ha hoa V' Z hP
          have h2M : twoP (app M' Z) := ⟨hM'1, twoP_rk Z hZ⟩
          have := hia (app M' Z) h2M (Or.inr ⟨a, by simp, hsubA _ _ hYa⟩)
          exact mono Z (this h2M).2
  · simp at he
    rcases he with he | he | he | he
    · exact mono Z (hia Z hZ (Or.inr ⟨a, by simp, sub_trans _ _ _ hsub (sub_of_args a e he)⟩))
    · rw [he] at hsub; exact mono Z (hia Z hZ (Or.inr ⟨c, by simp, hsub⟩))
    · rw [he] at hsub
      rcases hsub with h | h | h
      · injection h with hZb hyc
        subst hZb; subst hyc
        have hb1 : rk Z = 1 := twoP_rk Z hZ
        apply mono; apply hia Z hZ; left
        refine ⟨?_, Ytop_third a Z (var 2) R (by omega) (by omega) rk_var2⟩
        simp only [Preg_cons, hb1]
        by_cases ha1 : rk a = 1 <;> simp [ha1]
      · exact mono Z (hia Z hZ (Or.inr ⟨b, by simp, h⟩))
      · exact mono Z (hia Z hZ (Or.inr ⟨c, by simp, h⟩))
    · exact mono Z (hia Z hZ (Or.inr ⟨e, by simp [he], hsub⟩))

/-! ## S1 Part 7: FI-B, the main induction and the structural theorem (S1) -/

theorem spine_eq : ∀ (m1 m2 : T), head m1 = S → head m2 = S → args m1 = args m2 → m1 = m2
  | S, S, _, _, _ => rfl
  | S, var _, _, h2, _ => by simp [head] at h2
  | S, app f x, _, _, he => by simp [args] at he
  | var _, _, h1, _, _ => by simp [head] at h1
  | app f x, S, _, _, he => by simp [args] at he
  | app f x, var _, _, h2, _ => by simp [head] at h2
  | app f x, app g z, h1, h2, he => by
    simp only [args] at he
    have := List.append_inj' he rfl
    simp at this
    rw [spine_eq f g (by simpa [head] using h1) (by simpa [head] using h2) this.1, this.2]

/-- (S1) has occurred by time t: some list args(c0) ++ [w, y | B] -/
def S1occ (L1 : List T) (t : Nat) (c0 w : T) : Prop :=
  ∃ s, s ≤ t ∧ ∃ B, run s L1 = some (args c0 ++ w :: var 2 :: B)

def IB (L1 : List T) (w c0 : T) (t : Nat) (L : List T) : Prop :=
  ∀ U, Preg L = [U, w] → inX c0 U → U ≠ c0 → Ytop L = some (var 2) → S1occ L1 t c0 w

theorem run_succ_of (L1 : List T) (t : Nat) (L L' : List T) (h : run t L1 = some L) (hs : step L = some L') :
    run (t + 1) L1 = some L' := by
  rw [run_add t 1, h]; simp [run, hs]

theorem run_succ_split (L1 : List T) (t : Nat) (L' : List T) (h : run (t + 1) L1 = some L') :
    ∃ L, run t L1 = some L ∧ step L = some L' := by
  rw [run_add t 1] at h
  cases hr : run t L1 with
  | none => rw [hr] at h; simp at h
  | some L =>
    rw [hr] at h
    simp only [Option.bind_some, run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L2 =>
      rw [hs] at h
      simp at h
      exact ⟨L, rfl, by rw [hs, h]⟩

/-- at a GOOD time the P-region is the pair [M, w] over the bare y -/
theorem good_pair (k M w : T) (R : List T) (hS : Seg (k :: M :: w :: var 2 :: R))
    (h2 : (Preg (k :: M :: w :: var 2 :: R)).length ≤ 2) (hM : rk M = 1) (hw : rk w = 1) :
    Preg (k :: M :: w :: var 2 :: R) = [M, w] ∧ Ytop (k :: M :: w :: var 2 :: R) = some (var 2) := by
  have hkM := srt_tail_ge k _ hS.1 M (by simp)
  have hyR := srt_tail_ge (var 2) R (srt_tail w _ (srt_tail M _ (srt_tail k _ hS.1)))
  rw [rk_var2] at hyR
  have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hyR e he; omega)
  have hk0 : rk k = 0 := by
    rcases rk_cases k with h | h | h
    · exact h
    · exfalso; simp only [Preg_cons, h, hM, hw, if_true, List.length_cons] at h2; omega
    · omega
  have hk2 : rk k ≠ 2 := by omega
  have hM2 : rk M ≠ 2 := by omega
  have hw2 : rk w ≠ 2 := by omega
  refine ⟨?_, ?_⟩
  · simp only [Preg_cons, hk0, hM, hw, rk_var2, hR]; simp
  · unfold Ytop; simp only [Yl_cons, hk2, hM2, hw2, rk_var2]; simp

theorem ib_step (L1 : List T) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1) (t : Nat)
    (a b c : T) (R : List T) (ha : head a = S) (hrun : run t L1 = some (a :: b :: c :: R))
    (hseg : Seg (a :: b :: c :: R)) (h2 : (Preg (a :: b :: c :: R)).length ≤ 2)
    (hc1 : IC1 (a :: b :: c :: R)) (hiw : IW w c0 (a :: b :: c :: R)) (hia : IA L1 t (a :: b :: c :: R))
    (hist : ∀ s Ls, s ≤ t → run s L1 = some Ls → IB L1 w c0 s Ls)
    (hbound : ∀ s Ls, s ≤ t → run s L1 = some Ls → (Preg Ls).length ≤ 2)
    (hsegs : ∀ s Ls, run s L1 = some Ls → Seg Ls) :
    IB L1 w c0 (t + 1) (args a ++ c :: app b c :: R) := by
  obtain ⟨hab, hbc, hcR⟩ := srt3 a b c R hseg.1
  have hrbc : rk (app b c) = max (rk b) (rk c) := rk_app b c
  have hoa : ordT a := hseg.2 a (by simp)
  have hwa : wsubOK w c0 a := hiw.1 a (by simp)
  have hstep : step (a :: b :: c :: R) = some (args a ++ c :: app b c :: R) := by simp [step, ha]
  have hrun' := run_succ_of L1 t _ _ hrun hstep
  have mono : S1occ L1 t c0 w → S1occ L1 (t + 1) c0 w := by
    rintro ⟨s, hs, B, hB⟩; exact ⟨s, by omega, B, hB⟩
  have monoS : ∀ s, s ≤ t → S1occ L1 s c0 w → S1occ L1 (t + 1) c0 w := by
    rintro s hst ⟨s', hs', B, hB⟩; exact ⟨s', by omega, B, hB⟩
  -- from a GOOD pair [M, w] at an earlier time to (S1)
  have fromGood : ∀ M, rk M = 1 → inX c0 M → M ≠ c0 → Good L1 t M w → S1occ L1 (t + 1) c0 w := by
    rintro M hM1 hXM hMc ⟨s, hs, k, R', hks⟩
    have hSs := hsegs s _ hks
    obtain ⟨hPs, hYs⟩ := good_pair k M w R' hSs (hbound s _ hs hks) hM1 hwr
    exact monoS s hs (hist s _ hs hks M hPs hXM hMc hYs)
  intro U hU hX hne hY
  have hU0 := hU
  rw [Preg_append] at hU
  rcases rk_cases c with hc | hc | hc
  · have ha0 : rk a = 0 := by omega
    have hb0 : rk b = 0 := by omega
    have hbc0 : rk (app b c) = 0 := by rw [hrbc]; omega
    rw [Preg_args_closed a ha0] at hU
    simp only [Preg_cons, hc, hbc0] at hU
    apply mono
    apply hist t _ (Nat.le_refl t) hrun U _ hX hne
    · unfold Ytop at hY ⊢
      rw [Yl_append, Yl_args_le1 a (by omega)] at hY
      simp only [Yl_cons, ha0, hb0, hc, hbc0] at hY ⊢
      simpa using hY
    · simp only [Preg_cons, ha0, hb0, hc]; simpa using hU
  · have hbc1 : rk (app b c) = 1 := by rw [hrbc]; omega
    have ha0 : rk a = 0 := by
      rcases rk_cases a with h | h | h
      · exact h
      · exfalso
        have hb1 : rk b = 1 := by omega
        simp only [Preg_cons, h, hb1, hc, if_true, List.length_cons] at h2; omega
      · omega
    rw [Preg_args_closed a ha0] at hU
    simp only [Preg_cons, hc, hbc1, if_true, List.nil_append] at hU
    have h1 := List.cons.inj hU
    have h2' := List.cons.inj h1.2
    have hbcw : app b c = w := h2'.1
    rw [hw] at hbcw
    injection hbcw with _ hcc
    exact absurd (by rw [← h1.1, hcc]) hne
  · have hbc2 : rk (app b c) = 2 := by rw [hrbc]; omega
    have hR : Preg R = [] := Preg_nil_of R (fun e he => by have := hcR e he; omega)
    simp only [Preg_cons, hc, hbc2, hR] at hU
    simp at hU
    obtain ⟨M, hMS, hM1, hMU, hsub, C, Y, hargs, hMA, hC, hYY⟩ := release_pair a ha hoa U w hU
    have hXM : inX c0 M := (wsubOK_sub w c0 _ a hwa hsub).2.2 rfl hM1
    have hU1 : rk U = 1 := by
      have : U ∈ Preg (args a) := by rw [hU]; simp
      unfold Preg at this; simp at this; exact this.2
    have hYa : Yl (args a) = Y := by
      rw [hargs]
      have := Yl_split C [U, w] Y hC (by simp [hU1, hwr]) hYY
      simpa using this
    by_cases hMc : M = c0
    · -- the front has prefix c0.w: (S1) right now
      subst hMc
      refine ⟨t + 1, Nat.le_refl _, ?_⟩
      have hL' : args a ++ c :: app b c :: R = args M ++ w :: (Y ++ c :: app b c :: R) := by
        rw [hargs, hMA]; simp
      unfold Ytop at hY
      rw [Yl_append, hYa] at hY
      cases Y with
      | nil =>
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        subst hY
        exact ⟨app b (var 2) :: R, by rw [hrun', hL']; simp⟩
      | cons y' Y' =>
        simp at hY
        subst hY
        exact ⟨Y' ++ c :: app b c :: R, by rw [hrun', hL']; simp⟩
    · rcases rk_cases a with ha' | ha' | ha'
      · rw [Preg_args_closed a ha'] at hU; simp at hU
      · -- P-front a = M.w over the bare y
        have hY0 : Y = [] := by rw [← hYa]; exact Yl_args_le1 a (by omega)
        subst hY0
        obtain ⟨M2, hM2S, hM2A, haeq⟩ := spine_last a ha (C ++ [U]) w (by rw [hargs]; simp)
        have hM2 : M2 = M := spine_eq M2 M hM2S hMS (by rw [hM2A, hMA])
        rw [hM2] at haeq
        have h2a : twoP a := by rw [haeq]; exact ⟨hM1, hwr⟩
        have hb1 : rk b = 1 := by
          rcases rk_cases b with h | h | h
          · omega
          · exact h
          · exfalso
            apply hc1 a _ h2a
            have hb2 : rk b ≠ 1 := by omega
            have hc2' : rk c ≠ 1 := by omega
            simp only [Preg_cons, ha', hb2, hc2', hR]; simp
        unfold Ytop at hY
        rw [Yl_append, hYa] at hY
        simp only [Yl_cons, hc, hbc2, if_true, List.nil_append] at hY
        simp at hY
        have hYL : Ytop (a :: b :: c :: R) = some (var 2) := by
          rw [Ytop_third a b c R (by omega) (by omega) hc, hY]
        have hr := hia a h2a (Or.inl ⟨by simp only [Preg_cons, ha']; simp, hYL⟩)
        rw [haeq] at hr
        exact fromGood M hM1 hXM hMc (hr ⟨hM1, hwr⟩).1
      · -- Y-front (M.w).y ...
        unfold Ytop at hY
        rw [Yl_append, hYa] at hY
        cases Y with
        | nil => exact absurd hYa (Yl_args_ne_nil a ha ha')
        | cons y' Y' =>
          simp at hY
          subst hY
          obtain ⟨M2, hM2S, hM2A, hsub2⟩ := spine_prefix a ha (C ++ [U, w]) Y' (var 2) (by rw [hargs]; simp)
          obtain ⟨M3, hM3S, hM3A, hM2e⟩ := spine_last M2 hM2S (C ++ [U]) w (by rw [hM2A]; simp)
          have hM3 : M3 = M := spine_eq M3 M hM3S hMS (by rw [hM3A, hMA])
          rw [hM2e, hM3] at hsub2
          have h2M : twoP (app M w) := ⟨hM1, hwr⟩
          have hr := hia (app M w) h2M (Or.inr ⟨a, by simp, hsub2⟩)
          exact fromGood M hM1 hXM hMc (hr h2M).1

/-! base case: a start list with at most one occurrence of p in total -/

theorem occN0_of_rk1 (t : T) (h : rk t = 1) : 1 ≤ occN 0 t := by
  have := (rk_eq1 t).1 h; omega

theorem twoP_occ (Z : T) (h : twoP Z) : 2 ≤ occN 0 Z := by
  match Z, h with
  | app U V, h =>
    have := occN0_of_rk1 U h.1; have := occN0_of_rk1 V h.2
    simp only [occN]; omega

theorem noKZ_of_le1 : ∀ e : T, occN 0 e ≤ 1 → noKZ e
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    simp only [occN] at h
    refine ⟨noKZ_of_le1 f (by omega), noKZ_of_le1 x (by omega), ?_⟩
    rintro ⟨_, hx⟩
    have := twoP_occ x hx; omega

theorem wsubOK_of_le1 (w c0 : T) (hwr : rk w = 1) : ∀ e : T, occN 0 e ≤ 1 → wsubOK w c0 e
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    simp only [occN] at h
    refine ⟨wsubOK_of_le1 w c0 hwr f (by omega), wsubOK_of_le1 w c0 hwr x (by omega), ?_⟩
    intro hxw hf
    subst hxw
    have := occN0_of_rk1 f hf; have := occN0_of_rk1 x hwr; omega

theorem Preg_len_le_occ : ∀ L : List T, (Preg L).length ≤ (L.map (occN 0)).sum
  | [] => by simp [Preg]
  | e :: L => by
    rw [Preg_cons]
    have := Preg_len_le_occ L
    by_cases h : rk e = 1
    · have := occN0_of_rk1 e h; simp [h]; omega
    · simp [h]; omega

theorem mem_occ_le (L : List T) (e : T) (he : e ∈ L) : occN 0 e ≤ (L.map (occN 0)).sum := by
  induction L with
  | nil => simp at he
  | cons x L ih =>
    simp at he
    rcases he with he | he
    · subst he; simp
    · have := ih he; simp; omega

theorem s1_base (L1 : List T) (w c0 : T) (hwr : rk w = 1) (hp : (L1.map (occN 0)).sum ≤ 1) :
    IC1 L1 ∧ IC2 L1 ∧ IW w c0 L1 ∧ IA L1 0 L1 ∧ IB L1 w c0 0 L1 := by
  have hel : ∀ e ∈ L1, occN 0 e ≤ 1 := fun e he => by have := mem_occ_le L1 e he; omega
  have hlen : (Preg L1).length ≤ 1 := by have := Preg_len_le_occ L1; omega
  refine ⟨?_, fun e he => noKZ_of_le1 e (hel e he), ⟨fun e he => wsubOK_of_le1 w c0 hwr e (hel e he), ?_⟩, ?_, ?_⟩
  · intro Z hZ h2Z
    have hZm : Z ∈ L1 := by
      have : Z ∈ Preg L1 := by rw [hZ]; simp
      unfold Preg at this; simp at this; exact this.1
    have := hel Z hZm; have := twoP_occ Z h2Z; omega
  · intro U hU; rw [hU] at hlen; simp at hlen
  · intro Z h2Z hcase
    exfalso
    rcases hcase with ⟨hZm, _⟩ | ⟨e, he, hsub⟩
    · have : Z ∈ L1 := by unfold Preg at hZm; simp at hZm; exact hZm.1
      have := hel Z this; have := twoP_occ Z h2Z; omega
    · have h1 := occN_sub_le 0 _ _ hsub
      have := hel e he; have := twoP_occ Z h2Z
      simp only [occN] at h1; omega
  · intro U hU; rw [hU] at hlen; simp at hlen

/-- the invariants hold at every time up to tmax -/
theorem s1_inv (L1 : List T) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1)
    (hS : Seg L1) (hp : (L1.map (occN 0)).sum ≤ 1) (tmax : Nat)
    (hbound : ∀ s Ls, s ≤ tmax → run s L1 = some Ls → (Preg Ls).length ≤ 2) :
    ∀ t, t ≤ tmax → ∀ s Ls, s ≤ t → run s L1 = some Ls →
      IC1 Ls ∧ IC2 Ls ∧ IW w c0 Ls ∧ IA L1 s Ls ∧ IB L1 w c0 s Ls := by
  have hsegs : ∀ s Ls, run s L1 = some Ls → Seg Ls := fun s Ls h => seg_run s L1 Ls hS h
  intro t
  induction t with
  | zero =>
    intro _ s Ls hs hr
    have : s = 0 := by omega
    subst this
    simp [run] at hr
    rw [← hr]
    exact s1_base L1 w c0 hwr hp
  | succ t ih =>
    intro ht s Ls hs hr
    rcases Nat.lt_or_ge s (t + 1) with hst | hst
    · exact ih (by omega) s Ls (by omega) hr
    · have hs1 : s = t + 1 := by omega
      subst hs1
      obtain ⟨L, hL, hstep⟩ := run_succ_split L1 t Ls hr
      obtain ⟨a, b, c, R, rfl, ha, rfl⟩ := step_some L _ hstep
      obtain ⟨hc1, hc2, hiw, hia, _⟩ := ih (by omega) t _ (Nat.le_refl t) hL
      have hseg := hsegs t _ hL
      have h2 := hbound t _ (by omega) hL
      have h2' := hbound (t + 1) _ ht hr
      obtain ⟨hc1', hc2'⟩ := ic_step a b c R ha hseg h2 h2' hc1 hc2
      refine ⟨hc1', hc2', iw_step w b0 c0 hw hwr a b c R ha hseg h2 hiw,
        ia_step L1 t a b c R ha hL hseg h2 h2' hc1 hc2 hc1' hia, ?_⟩
      exact ib_step L1 w b0 c0 hw hwr t a b c R ha hL hseg h2 hc1 hiw hia
        (fun s' Ls' hs' hr' => (ih (by omega) s' Ls' hs' hr').2.2.2.2)
        (fun s' Ls' hs' hr' => hbound s' Ls' (by omega) hr') hsegs

/-- **THEOREM S1 (structural claim, generic form).**  Let a run start from a list L1 that is rank-sorted with
    hereditarily sorted spines (Seg) and contains at most ONE occurrence of p in total, and let it reach, at time T',
    a list whose third element contains x, y or r (e.g. a proper transfer).  If at a time tg <= T' the run passes
    through a glue list a1 :: w :: y :: R0 with w = b0.c0 a P-term and a1 a P-term different from c0, then at some
    time s <= tg the run passes through args(c0) ++ w :: y :: B ('c0 runs on (w, y)'). -/
theorem s1_core (L1 : List T) (w b0 c0 : T) (hw : w = app b0 c0) (hwr : rk w = 1)
    (hS : Seg L1) (hp : (L1.map (occN 0)).sum ≤ 1)
    (T' : Nat) (f b d : T) (R : List T) (hT : run T' L1 = some (f :: b :: d :: R)) (hd : rk d = 2)
    (tg : Nat) (htg : tg ≤ T') (a1 : T) (R0 : List T) (hg : run tg L1 = some (a1 :: w :: var 2 :: R0))
    (ha1 : rk a1 = 1) (hne : a1 ≠ c0) :
    ∃ s, s ≤ tg ∧ ∃ B, run s L1 = some (args c0 ++ w :: var 2 :: B) := by
  have hbound : ∀ s Ls, s ≤ T' → run s L1 = some Ls → (Preg Ls).length ≤ 2 :=
    fun s Ls hs hr => ab3_bound L1 hS T' f b d R hT hd s Ls hs hr
  obtain ⟨_, _, hiw, _, hib⟩ := s1_inv L1 w b0 c0 hw hwr hS hp T' hbound tg htg tg _ (Nat.le_refl _) hg
  have hSg := seg_run tg L1 _ hS hg
  have hyR := srt_tail_ge (var 2) R0 (srt_tail w _ (srt_tail a1 _ hSg.1))
  rw [rk_var2] at hyR
  have hR0 : Preg R0 = [] := Preg_nil_of R0 (fun e he => by have := hyR e he; omega)
  have hP : Preg (a1 :: w :: var 2 :: R0) = [a1, w] := by
    simp only [Preg_cons, ha1, hwr, rk_var2, hR0]; simp
  have hY : Ytop (a1 :: w :: var 2 :: R0) = some (var 2) := by
    have h1 : rk a1 ≠ 2 := by omega
    have h2 : rk w ≠ 2 := by omega
    unfold Ytop; simp only [Yl_cons, h1, h2, rk_var2]; simp
  exact hib a1 hP (hiw.2 a1 hP) hne hY

#print axioms s1_core
#print axioms s1_inv
#print axioms ab3_bound
