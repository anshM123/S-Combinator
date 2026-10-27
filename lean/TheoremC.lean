/-
  Theorem C (an S-term with a non-regular Böhm tree) — machine-checked (main agent, 2026-10-27). Plain Lean 4 core.
  Nests N_0 = S, N_{j+1} = S N_j; K = S S N_3 N_1 (8 leaves); W_0 = K, W_{m+1} = S S W_m. The head machine on lists
  [a, b, c] ++ R => args a ++ [c, b·c] ++ R; a Böhm-tree node is a term, its children are the components of its head
  normal form.
  * `bts_W`: the Böhm tree of W_m is finite with 9 + 2m leaves.
  * `cycle`: for r >= 1, the Böhm tree of K·W_r contains the node K·W_{r+1} and the node W_{r+1}.
  * `theoremC`: for every r >= 1 the Böhm tree of K·W_1 (18 leaves) has a node whose subtree is finite with exactly
    11 + 2r leaves. A node's subtree is unique (the machine is deterministic), so BT(K·W_1) has infinitely many
    distinct subtrees: Böhm trees of S-terms are not regular in general.
-/

inductive Tm where
  | S : Tm
  | app : Tm → Tm → Tm
deriving DecidableEq, Repr

open Tm

def args : Tm → List Tm
  | S => []
  | app f x => args f ++ [x]

def step : List Tm → Option (List Tm)
  | a :: b :: c :: R => some (args a ++ c :: app b c :: R)
  | _ => none

def run : Nat → List Tm → Option (List Tm)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

theorem run_succ (k : Nat) (L L' : List Tm) (h : step L = some L') : run (k + 1) L = run k L' := by
  simp [run, h]

/-- the Böhm tree of the node with argument list L is finite with n leaves -/
inductive BTS : List Tm → Nat → Prop
  | leaf (L : List Tm) (k : Nat) : run k L = some [] → BTS L 1
  | one (L : List Tm) (k : Nat) (x : Tm) (n : Nat) : run k L = some [x] → BTS (args x) n → BTS L (n + 1)
  | two (L : List Tm) (k : Nat) (x y : Tm) (n m : Nat) : run k L = some [x, y] → BTS (args x) n → BTS (args y) m →
      BTS L (n + m + 1)

/-- u is a node of the Böhm tree of the node with argument list L -/
inductive BTR : List Tm → Tm → Prop
  | first (L : List Tm) (k : Nat) (x : Tm) (rest : List Tm) : run k L = some (x :: rest) → (x :: rest).length ≤ 2 →
      BTR L x
  | second (L : List Tm) (k : Nat) (x y : Tm) : run k L = some [x, y] → BTR L y
  | trans (L : List Tm) (u v : Tm) : BTR L u → BTR (args u) v → BTR L v

def N : Nat → Tm
  | 0 => S
  | j + 1 => app S (N j)

def K : Tm := app (app (app S S) (N 3)) (N 1)

def W : Nat → Tm
  | 0 => K
  | m + 1 => app (app S S) (W m)

/-- the nests are normal forms: BT(N_j) has j + 1 leaves -/
theorem bts_N : ∀ j, BTS (args (N j)) (j + 1)
  | 0 => BTS.leaf _ 0 rfl
  | j + 1 => BTS.one _ 0 (N j) (j + 1) rfl (bts_N j)

theorem bts_K : BTS (args K) 9 := by
  -- [S, N3, N1] -> [N1, N3 N1]
  have h : run 1 (args K) = some [N 1, app (N 3) (N 1)] := rfl
  have h2 : BTS (args (app (N 3) (N 1))) 6 := by
    -- args (N3 N1) = [N2, N1]: already a head normal form
    exact BTS.two _ 0 (N 2) (N 1) 3 2 rfl (bts_N 2) (bts_N 1)
  exact BTS.two _ 1 (N 1) (app (N 3) (N 1)) 2 6 h (bts_N 1) h2

/-- BT(W_m) is finite with 9 + 2m leaves -/
theorem bts_W : ∀ m, BTS (args (W m)) (9 + 2 * m)
  | 0 => bts_K
  | m + 1 => by
    have := BTS.two (args (W (m + 1))) 0 S (W m) 1 (9 + 2 * m) rfl (BTS.leaf _ 0 rfl) (bts_W m)
    rw [show 9 + 2 * (m + 1) = 1 + (9 + 2 * m) + 1 by omega]
    exact this

/-- N_1 · W_r = W_{r+1} syntactically -/
theorem N1_W (r : Nat) : app (N 1) (W r) = W (r + 1) := rfl

/-- (i): K Z ->3 S P (Z P) with P = N3 N1 Z -/
theorem run_KZ (Z : Tm) :
    run 3 (args (app K Z)) = some [app (app (N 3) (N 1)) Z, app Z (app (app (N 3) (N 1)) Z)] := rfl

/-- (ii): N3 N1 Z ->3 S (Z (N1 Z)) ((N1 Z) (Z (N1 Z))) -/
theorem run_P (Z : Tm) :
    run 3 (args (app (app (N 3) (N 1)) Z)) =
      some [app Z (app (N 1) Z), app (app (N 1) Z) (app Z (app (N 1) Z))] := rfl

/-- (iii): W_{m+1} Y ->1 S Y (W_m Y) -/
theorem run_WY (m : Nat) (Y : Tm) : run 1 (args (app (W (m + 1)) Y)) = some [Y, app (W m) Y] := rfl

/-- descending the second components: W_m · Y reaches K · Y -/
theorem down : ∀ (m : Nat) (Y : Tm), m ≥ 1 → BTR (args (app (W m) Y)) (app K Y)
  | 0, _, h => absurd h (by decide)
  | 1, Y, _ => BTR.second _ 1 Y (app K Y) (run_WY 0 Y)
  | m + 2, Y, _ =>
    BTR.trans _ (app (W (m + 1)) Y) _ (BTR.second _ 1 Y _ (run_WY (m + 1) Y)) (down (m + 1) Y (by omega))

/-- **The cycle.** For r >= 1 the Böhm tree of K·W_r contains W_{r+1} and K·W_{r+1}. -/
theorem cycle (r : Nat) (hr : r ≥ 1) :
    BTR (args (app K (W r))) (W (r + 1)) ∧ BTR (args (app K (W r))) (app K (W (r + 1))) := by
  -- K W_r ->1 P_r = N3 N1 W_r
  have e1 : BTR (args (app K (W r))) (app (app (N 3) (N 1)) (W r)) := BTR.first _ 3 _ _ (run_KZ (W r)) (by simp)
  -- P_r ->1 W_r (N1 W_r) = W_r W_{r+1}
  have e2 : BTR (args (app (app (N 3) (N 1)) (W r))) (app (W r) (W (r + 1))) := by
    have := BTR.first _ 3 _ _ (run_P (W r)) (by simp)
    rwa [N1_W] at this
  have e12 := BTR.trans _ _ _ e1 e2
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  -- W_{m+1} W_{m+2}: first component W_{m+2}, second W_m W_{m+2} -> ... -> K W_{m+2}
  have e3 : BTR (args (app (W (m + 1)) (W (m + 1 + 1)))) (W (m + 1 + 1)) :=
    BTR.first _ 1 _ _ (run_WY m (W (m + 1 + 1))) (by simp)
  refine ⟨BTR.trans _ _ _ e12 e3, ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- W_1 W_2 ->2 W_0 W_2 = K W_2
    exact BTR.trans _ _ _ e12 (BTR.second _ 1 _ _ (run_WY 0 (W 2)))
  · exact BTR.trans _ _ _ e12
      (BTR.trans _ _ _ (BTR.second _ 1 _ _ (run_WY m (W (m + 1 + 1)))) (down m (W (m + 1 + 1)) hm))

theorem cycle_iter : ∀ (j : Nat), BTR (args (app K (W 1))) (app K (W (j + 2)))
  | 0 => (cycle 1 (by decide)).2
  | j + 1 => BTR.trans _ _ _ (cycle_iter j) (cycle (j + 2) (by omega)).2

/-- **Theorem C.** For every r >= 1 the Böhm tree of K·W_1 (18 leaves) has a node whose subtree is finite with exactly
    11 + 2r leaves. -/
theorem theoremC (r : Nat) (hr : r ≥ 1) : ∃ u, BTR (args (app K (W 1))) u ∧ BTS (args u) (11 + 2 * r) := by
  refine ⟨W (r + 1), ?_, ?_⟩
  · rcases Nat.lt_or_ge r 2 with h | h
    · obtain rfl : r = 1 := by omega
      exact (cycle 1 (by decide)).1
    · obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
      exact BTR.trans _ _ _ (cycle_iter j) (cycle (j + 2) (by omega)).1
  · have := bts_W (r + 1)
    rw [show 9 + 2 * (r + 1) = 11 + 2 * r by omega] at this
    exact this

#print axioms theoremC

/-! ## Subtree sizes are unique, so the subtrees found above are pairwise distinct -/

theorem run_add : ∀ (m n : Nat) (L L' : List Tm), run m L = some L' → run (m + n) L = run n L'
  | 0, n, L, L', h => by simp [run] at h; subst h; simp
  | m + 1, n, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [run, hs]; exact run_add m n L1 L' h

theorem step_short (L : List Tm) (h : L.length ≤ 2) : step L = none := by
  match L, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl

theorem run_short : ∀ (n : Nat) (L : List Tm), L.length ≤ 2 → run (n + 1) L = none := by
  intro n L h; simp [run, step_short L h]

/-- the head normal form of a node is unique -/
theorem hnf_unique (L L1 L2 : List Tm) (k1 k2 : Nat) (h1 : run k1 L = some L1) (h2 : run k2 L = some L2)
    (s1 : L1.length ≤ 2) (s2 : L2.length ≤ 2) : L1 = L2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, k2 = k1 + (d + 1) := ⟨k2 - k1 - 1, by omega⟩
    rw [run_add k1 (d + 1) L L1 h1, run_short d L1 s1] at h2
    simp at h2
  · subst h; rw [h1] at h2; simpa using h2
  · obtain ⟨d, rfl⟩ : ∃ d, k1 = k2 + (d + 1) := ⟨k1 - k2 - 1, by omega⟩
    rw [run_add k2 (d + 1) L L2 h2, run_short d L2 s2] at h1
    simp at h1

/-- the size of a finite Böhm tree is unique -/
theorem bts_unique : ∀ {L : List Tm} {n n' : Nat}, BTS L n → BTS L n' → n = n' := by
  intro L n n' h1 h2
  induction h1 generalizing n' with
  | leaf L k hk =>
    cases h2 with
    | leaf => rfl
    | one _ k' x _ hk' _ => have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp); simp at this
    | two _ k' x y _ _ hk' _ _ => have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp); simp at this
  | one L k x n hk _ ih =>
    cases h2 with
    | leaf _ k' hk' => have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp); simp at this
    | one _ k' x' n2 hk' hb' =>
      have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp)
      simp only [List.cons.injEq, and_true] at this
      subst this
      rw [ih hb']
    | two _ k' x' y' _ _ hk' _ _ => have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp); simp at this
  | two L k x y n m hk _ _ ihx ihy =>
    cases h2 with
    | leaf _ k' hk' => have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp); simp at this
    | one _ k' x' _ hk' _ => have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp); simp at this
    | two _ k' x' y' n2 m2 hk' hx' hy' =>
      have := hnf_unique _ _ _ _ _ hk hk' (by simp) (by simp)
      simp only [List.cons.injEq, and_true] at this
      obtain ⟨rfl, rfl⟩ := this
      rw [ihx hx', ihy hy']

/-- **Theorem C (distinct subtrees).** For r ≠ r' (both >= 1) the nodes W_{r+1} and W_{r'+1} of BT(K·W_1) have finite
    subtrees of different sizes; with `theoremC`, BT(K·W_1) has infinitely many pairwise distinct subtrees. -/
theorem distinct_subtrees (r r' : Nat) (h : r ≠ r') (n : Nat) (h1 : BTS (args (W (r + 1))) n)
    (h2 : BTS (args (W (r' + 1))) n) : False := by
  have e1 := bts_unique h1 (bts_W (r + 1))
  have e2 := bts_unique h2 (bts_W (r' + 1))
  omega

#print axioms distinct_subtrees
