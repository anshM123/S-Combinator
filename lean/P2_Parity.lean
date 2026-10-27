/-
  Theorem P2 in Lean (main agent, 2026-10-27), built on Theorem A (bignum-table M35): the 35-class head-normalisation model M35 (data/model35_hn.txt,
  isomorphic to BEKW's Fig. 14 automaton) is an S-model, so its class is invariant along head runs; every head
  normal form has a class in F. Hence a term whose class is not in F has no head normal form.
  Table generated mechanically from the data file by the main agent.
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

/-- the 35×35 product table as one natural number in base 35: entry (a, b) is digit 35·a + b -/
def TAB : Nat := 29538562191222620684320081899232842754670124900736763521668000729659287016484259335777889864422233901003611783465599855032323383667755269420523759846519407854326214244162200860261196204000983879465662862832812775281344614718350186660573389708754516866372087215350870174000213278538077694110585211888178172706056721317482125610032683220213626728259322667353060652718214409224115522991113186537593708345029105242327648458214379292939798631848921310119363597816348469279020180791198610003744392392901307059015429206808428354540786935115615555061783711294488670470326231511218015678171818108176776943925270929866538499919971789818934443981551320637978833001705049973587030890054513712659855835716452940024406619597766549226623935781543408038004226553639607523884562123333550690589702291805396433048256791960158474157557365988870480690494748230588715975753321649585450152853881788364956380281134208407796440733142308667468718098111196350610373242444622816547151418208095524161062588592677666257332809567134410314084977008085233188236718777234280745084495384213545038942153947465549217993168372871271532948861225719492399369040255731624612720899661474300527210494970976593169841460465756385570205955652957906827453723671819872918761939099295683061463436555090746110169410912891406358250922428953318536926493793823622782846021366858806738075492721479046397598310460940246273842607026519842627223866954999276883472332251139319203658014930738531082985299529881001571362642615441576854794458396830031814694899369128396346637595812026675343631597149506625133631298743193719461115279095950536034727357272892666353045584141367514524685946919355026384905978555932774652568711436145597909898990598687846064663905630806526514253443258246434921630690124204508490850547161589236504794240645475217674535395073940646302304849950070696700364764388501843967855393986215504971523726643875387395129321038634680311846

def mul (a b : Nat) : Nat := (TAB / 35 ^ (35 * a + b)) % 35

/-- the F classes as a bit mask -/
def FMASK : Nat := 25769803775
def isF (k : Nat) : Bool := (FMASK / 2 ^ k) % 2 == 1

def cls : Tm → Nat
  | S => 0
  | app f x => mul (cls f) (cls x)

/-- class of the term S·L1·L2·… -/
def clsL (L : List Tm) : Nat := L.foldl (fun acc t => mul acc (cls t)) 0

/-- (F1) the S-identity, as one Boolean check over all 35³ class triples -/
def checkS : Bool := (List.range 35).all fun x => (List.range 35).all fun y => (List.range 35).all fun z =>
  mul (mul (mul 0 x) y) z == mul (mul x z) (mul y z)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem checkS_true : checkS = true := by decide +kernel

/-- every product is a class index below 35 -/
def checkRange : Bool := (List.range 35).all fun x => (List.range 35).all fun y => mul x y < 35

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem checkRange_true : checkRange = true := by decide +kernel

theorem s_identity (x y z : Nat) (hx : x < 35) (hy : y < 35) (hz : z < 35) :
    mul (mul (mul 0 x) y) z = mul (mul x z) (mul y z) := by
  have h := checkS_true
  simp only [checkS, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h x hx y hy z hz

/-- (F1') hnf shapes S, S x, S x y land in F -/
def checkH : Bool := isF 0 && (List.range 35).all (fun x => isF (mul 0 x)) &&
  (List.range 35).all fun x => (List.range 35).all fun y => isF (mul (mul 0 x) y)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem checkH_true : checkH = true := by decide +kernel

theorem cls_lt : ∀ t : Tm, cls t < 35
  | S => by simp [cls]
  | app f x => by
    have h := checkRange_true
    simp only [checkRange, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h _ (cls_lt f) _ (cls_lt x)

theorem foldl_lt (L : List Tm) (acc : Nat) (h : acc < 35) : L.foldl (fun acc t => mul acc (cls t)) acc < 35 := by
  induction L generalizing acc with
  | nil => simpa using h
  | cons t L ih =>
    simp only [List.foldl]
    apply ih
    have hr := checkRange_true
    simp only [checkRange, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hr
    exact hr _ h _ (cls_lt t)

theorem clsL_lt (L : List Tm) : clsL L < 35 := foldl_lt L 0 (by decide)

/-- the class of a term is the class of S applied to its argument list -/
theorem cls_args : ∀ t : Tm, cls t = clsL (args t)
  | S => by simp [cls, clsL, args]
  | app f x => by
    simp only [cls, clsL, args, List.foldl_append, List.foldl]
    rw [cls_args f]; rfl

/-- (Lemma 3) the class is invariant along a head step -/
theorem clsL_step (L L' : List Tm) (h : step L = some L') : clsL L = clsL L' := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step, Option.some.injEq] at h
    subst h
    simp only [clsL, List.foldl_append, List.foldl]
    have e : (args a).foldl (fun acc t => mul acc (cls t)) 0 = cls a := (cls_args a).symm
    rw [e, s_identity (cls a) (cls b) (cls c) (cls_lt a) (cls_lt b) (cls_lt c)]
    rfl

theorem clsL_run : ∀ (n : Nat) (L L' : List Tm), run n L = some L' → clsL L = clsL L'
  | 0, L, L', h => by simp [run] at h; subst h; rfl
  | n + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 => rw [hs] at h; exact (clsL_step L L1 hs).trans (clsL_run n L1 L' h)

/-- every head normal form (a list of length <= 2) has its class in F -/
theorem hnf_inF (L : List Tm) (h : L.length ≤ 2) : isF (clsL L) = true := by
  have hh := checkH_true
  simp only [checkH, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hh
  obtain ⟨⟨h0, h1⟩, h2⟩ := hh
  match L, h with
  | [], _ => simpa [clsL] using h0
  | [x], _ => simpa [clsL] using h1 (cls x) (cls_lt x)
  | [x, y], _ => simpa [clsL] using h2 (cls x) (cls_lt x) (cls y) (cls_lt y)

/-- **Theorem A.** If the class of S·L is not in F, the head run from L never reaches a head normal form. -/
theorem theoremA (L : List Tm) (hF : isF (clsL L) = false) :
    ∀ n L', run n L = some L' → 3 ≤ L'.length := by
  intro n L' hr
  rcases Nat.lt_or_ge L'.length 3 with hlt | hge
  · exfalso
    have h2 : L'.length ≤ 2 := by omega
    have := hnf_inF L' h2
    rw [← clsL_run n L L' hr, hF] at this
    exact Bool.false_ne_true this
  · exact hge


/-! ## Theorem P2: Böhm-tree finiteness of S^{k+3}(SSS)(SS) counts modulo 2 -/

/-- the term S·L1·L2·… -/
def ofList (L : List Tm) : Tm := L.foldl app S

theorem args_ofList_aux : ∀ (L : List Tm) (t : Tm), args (L.foldl app t) = args t ++ L
  | [], t => by simp
  | x :: L, t => by simp only [List.foldl]; rw [args_ofList_aux L (app t x)]; simp [args]

theorem args_ofList (L : List Tm) : args (ofList L) = L := by simp [ofList, args_ofList_aux, args]

def X : Tm := app (app S S) S
def Y : Tm := app S S
/-- T j = S S^{×j} X Y, the head S with spine arguments [S, …, S, X, Y] -/
def T (j : Nat) : Tm := ofList (List.replicate j S ++ [X, Y])
/-- V 0 = T 1, V (r+1) = S Y (V r) -/
def V : Nat → Tm
  | 0 => T 1
  | r + 1 => app (app S Y) (V r)
/-- b·S·…·S (k times) -/
def iterR (b : Tm) : Nat → Tm
  | 0 => b
  | k + 1 => iterR (app b S) k

/-- Böhm-tree finiteness, over the deterministic head machine: a ⊥ leaf (no hnf) or an hnf whose components are finite -/
inductive BTFin : List Tm → Prop
  | bot (L : List Tm) : (∀ n L', run n L = some L' → 3 ≤ L'.length) → BTFin L
  | node (L : List Tm) (n : Nat) (L' : List Tm) : run n L = some L' → L'.length ≤ 2 →
      (∀ x ∈ L', BTFin (args x)) → BTFin L

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

theorem run_short : ∀ (k : Nat) (L : List Tm), L.length ≤ 2 → run (k + 1) L = none := by
  intro k L h; simp [run, step_short L h]

/-- the head normal form reached by the head machine is unique -/
theorem hnf_unique (L L1 L2 : List Tm) (n m : Nat) (h1 : run n L = some L1) (h2 : run m L = some L2)
    (hs1 : L1.length ≤ 2) (hs2 : L2.length ≤ 2) : L1 = L2 := by
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · have := run_add n (m - n - 1 + 1) L L1 h1
    rw [show n + (m - n - 1 + 1) = m by omega, h2, run_short _ L1 hs1] at this
    simp at this
  · subst heq; rw [h1] at h2; simpa using h2
  · have := run_add m (n - m - 1 + 1) L L2 h2
    rw [show m + (n - m - 1 + 1) = n by omega, h1, run_short _ L2 hs2] at this
    simp at this

/-- if the head machine reaches the hnf L1, Böhm-tree finiteness is finiteness of all its components -/
theorem btfin_hnf (L L1 : List Tm) (n : Nat) (h : run n L = some L1) (hs : L1.length ≤ 2) :
    BTFin L ↔ ∀ x ∈ L1, BTFin (args x) := by
  constructor
  · intro hb
    cases hb with
    | bot _ hn => have := hn n L1 h; omega
    | node _ m L' hm hs' hc => rw [hnf_unique L L1 L' n m h hm hs hs']; exact hc
  · intro hc; exact BTFin.node L n L1 h hs hc

/-- run lemma: [S, b, S^{×k}, c] ++ R ⇒^k [S, b·S^k, c] ++ R -/
theorem run_spine : ∀ (k : Nat) (b c : Tm) (R : List Tm),
    run k (S :: b :: (List.replicate k S ++ c :: R)) = some (S :: iterR b k :: c :: R)
  | 0, b, c, R => by simp [run, iterR]
  | k + 1, b, c, R => by
    have hs : step (S :: b :: (List.replicate (k + 1) S ++ c :: R)) = some (S :: app b S :: (List.replicate k S ++ c :: R)) := by
      simp [step, args, List.replicate_succ]
    simp only [run, hs]
    rw [run_spine k (app b S) c R]; rfl

theorem iterR_ofList : ∀ (k : Nat) (L : List Tm), iterR (ofList L) k = ofList (L ++ List.replicate k S)
  | 0, L => by simp [iterR]
  | k + 1, L => by
    simp only [iterR]
    have : app (ofList L) S = ofList (L ++ [S]) := by simp [ofList, List.foldl_append]
    rw [this, iterR_ofList k (L ++ [S])]
    simp [List.replicate_succ, List.append_assoc]

/-- head-run lemma: for j ≥ 2, T j reaches the hnf S (S Y T_{j-2}) (T_{j-2} (S Y T_{j-2})) in j + 3 steps -/
theorem head_run_T (i : Nat) :
    run (i + 5) (args (T (i + 2))) =
      some [app (app S Y) (T i), app (T i) (app (app S Y) (T i))] := by
  have hargs : args (T (i + 2)) = S :: S :: (List.replicate i S ++ X :: [Y]) := by
    simp [T, args_ofList, List.replicate_succ]
  rw [hargs]
  have h1 := run_spine i S X [Y]
  rw [show i + 5 = i + 5 from rfl]
  have h2 := run_add i 5 _ _ h1
  rw [h2]
  have hB : app (app (iterR S i) X) Y = T i := by
    have : iterR S i = ofList (List.replicate i S) := by
      have := iterR_ofList i []; simpa [ofList] using this
    rw [this]; simp [T, ofList, List.foldl_append]
  simp [run, step, args, X, Y]
  exact hB

/-! ### classes: the second component W j = T j (S Y (T j)) has no hnf for j = 0 and j ≥ 2 -/

def W (j : Nat) : Tm := app (T j) (app (app S Y) (T j))

theorem cls_ofList (L : List Tm) : cls (ofList L) = clsL L := by rw [cls_args, args_ofList]

/-- class of S·S^{×j} -/
def pre (j : Nat) : Nat := clsL (List.replicate j S)

theorem pre_succ (j : Nat) : pre (j + 1) = mul (pre j) 0 := by
  simp only [pre, clsL, List.replicate_succ', List.foldl_append, List.foldl]; rfl

theorem pre_fix : ∀ j, pre (j + 4) = pre 4
  | 0 => rfl
  | j + 1 => by
    rw [show j + 1 + 4 = (j + 4) + 1 by omega, pre_succ, pre_fix j]
    decide +kernel

theorem cls_T (j : Nat) : cls (T j) = mul (mul (pre j) (cls X)) (cls Y) := by
  simp only [T, cls_ofList, clsL, List.foldl_append, List.foldl]; rfl

theorem cls_W (j : Nat) : cls (W j) = mul (cls (T j)) (mul (mul 0 (cls Y)) (cls (T j))) := rfl

set_option maxRecDepth 100000 in
theorem W_notF_small : isF (cls (W 0)) = false ∧ isF (cls (W 2)) = false ∧ isF (cls (W 3)) = false ∧
    isF (cls (W 4)) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem W_notF (j : Nat) (hj : j = 0 ∨ 2 ≤ j) : isF (cls (W j)) = false := by
  rcases hj with rfl | hj
  · exact W_notF_small.1
  · rcases (show j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | h4
    · exact W_notF_small.2.1
    · exact W_notF_small.2.2.1
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
      have : cls (W (k + 4)) = cls (W 4) := by rw [cls_W, cls_W, cls_T, cls_T, pre_fix]
      rw [this]; exact W_notF_small.2.2.2

theorem W_bt (j : Nat) (hj : j = 0 ∨ 2 ≤ j) : BTFin (args (W j)) := by
  apply BTFin.bot
  apply theoremA
  rw [← cls_args]; exact W_notF j hj

/-! ### small finite trees -/

theorem bt_nil : BTFin [] := BTFin.node [] 0 [] rfl (by simp) (by simp)

theorem bt_S : BTFin (args S) := by simpa [args] using bt_nil

theorem bt_Y : BTFin (args Y) := BTFin.node _ 0 _ rfl (by simp [Y, args]) (by
  intro x hx; simp [Y, args] at hx; subst hx; exact bt_S)

theorem bt_X : BTFin (args X) := BTFin.node _ 0 _ rfl (by simp [X, args]) (by
  intro x hx; simp [X, args] at hx; rcases hx with rfl | rfl <;> exact bt_S)

theorem bt_SY : BTFin (args (app S Y)) := BTFin.node _ 0 _ rfl (by simp [args]) (by
  intro x hx; simp [args] at hx; subst hx; exact bt_Y)

theorem bt_T0 : BTFin (args (T 0)) := by
  refine BTFin.node _ 0 _ rfl (by simp [T, args_ofList]) ?_
  intro x hx; simp [T, args_ofList] at hx; rcases hx with rfl | rfl
  · exact bt_X
  · exact bt_Y

theorem bt_T1 : BTFin (args (T 1)) := by
  refine BTFin.node _ 1 [Y, app X Y] (by simp [T, args_ofList, run, step, args]) (by simp) ?_
  intro x hx; simp at hx; rcases hx with rfl | rfl
  · exact bt_Y
  · refine BTFin.node _ 1 [Y, app S Y] (by simp [X, Y, run, step, args]) (by simp) ?_
    intro z hz; simp at hz; rcases hz with rfl | rfl
    · exact bt_Y
    · exact bt_SY

/-! ### the odd seed: T 1 (S Y (T 1)) has an infinite Böhm-tree path -/

theorem run_T1V (v : Tm) : run 3 (args (app (T 1) v)) = some [app (app X Y) v, app v (app (app X Y) v)] := by
  simp [T, args_ofList, args, run, step, X, Y]

theorem run_XYV (v : Tm) : run 3 (args (app (app X Y) v)) = some [app (app S Y) v, app v (app (app S Y) v)] := by
  simp [args, run, step, X, Y]

theorem run_Vi (i : Nat) (w : Tm) : run 2 (args (app (V (i + 1)) w)) = some [app (V i) w, app w (app (V i) w)] := by
  simp [V, args, run, step, Y]

/-- the nodes of the infinite path -/
def Qn (L : List Tm) : Prop :=
  (∃ r, 1 ≤ r ∧ L = args (app (T 1) (V r))) ∨ (∃ r, 1 ≤ r ∧ L = args (app (app X Y) (V r))) ∨
  (∃ i r, 1 ≤ i ∧ i ≤ r ∧ L = args (app (V i) (V (r + 1))))

theorem not_bt_path : ∀ L, BTFin L → Qn L → False := by
  intro L hb
  induction hb with
  | bot L hn =>
    intro hq
    rcases hq with ⟨r, _, rfl⟩ | ⟨r, _, rfl⟩ | ⟨i, r, hi, _, rfl⟩
    · have := hn 3 _ (run_T1V (V r)); simp at this
    · have := hn 3 _ (run_XYV (V r)); simp at this
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have := hn 2 _ (run_Vi i' (V (r + 1))); simp at this
  | node L n L' hrun hs hc ih =>
    intro hq
    rcases hq with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨i, r, hi, hir, rfl⟩
    · have e := hnf_unique _ _ _ n 3 hrun (run_T1V (V r)) hs (by simp)
      subst e
      exact ih (app (app X Y) (V r)) (by simp) (Or.inr (Or.inl ⟨r, hr, rfl⟩))
    · have e := hnf_unique _ _ _ n 3 hrun (run_XYV (V r)) hs (by simp)
      subst e
      exact ih (app (V r) (app (app S Y) (V r))) (by simp)
        (Or.inr (Or.inr ⟨r, r, hr, Nat.le_refl r, by simp [V]⟩))
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have e := hnf_unique _ _ _ n 2 hrun (run_Vi i' (V (r + 1))) hs (by simp)
      subst e
      rcases Nat.eq_zero_or_pos i' with h0 | hpos
      · subst h0
        exact ih (app (V 0) (V (r + 1))) (by simp) (Or.inl ⟨r + 1, by omega, by simp [V]⟩)
      · exact ih (app (V i') (V (r + 1))) (by simp) (Or.inr (Or.inr ⟨i', r, hpos, by omega, rfl⟩))

theorem not_bt_W1 : ¬ BTFin (args (W 1)) := by
  intro h
  exact not_bt_path _ h (Or.inl ⟨1, Nat.le_refl 1, by simp [W, V]⟩)

/-! ### the induction -/

theorem bt_step (i : Nat) : BTFin (args (T (i + 2))) ↔ BTFin (args (T i)) ∧ BTFin (args (W i)) := by
  rw [btfin_hnf _ _ (i + 5) (head_run_T i) (by simp)]
  constructor
  · intro h
    have h1 := h (app (app S Y) (T i)) (by simp)
    have h2 := h (app (T i) (app (app S Y) (T i))) (by simp)
    rw [btfin_hnf _ _ 0 rfl (by simp [args])] at h1
    exact ⟨h1 _ (by simp [args]), h2⟩
  · rintro ⟨h1, h2⟩ x hx
    simp at hx; rcases hx with rfl | rfl
    · rw [btfin_hnf _ _ 0 rfl (by simp [args])]
      intro z hz; simp [args] at hz; rcases hz with rfl | rfl
      · exact bt_Y
      · exact h1
    · exact h2

/-- **Theorem P2.** The Böhm tree of T j = S S^{×j} (SSS) (SS) is finite iff j is even or j = 1. -/
theorem P2 : ∀ j, BTFin (args (T j)) ↔ (j % 2 = 0 ∨ j = 1)
  | 0 => by simp [bt_T0]
  | 1 => by simp [bt_T1]
  | i + 2 => by
    rw [bt_step i, P2 i]
    rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with h0 | hpos
    · subst h0; simp [W_bt 0 (Or.inl rfl)]
    · rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | h2
      · simp [not_bt_W1]
      · simp only [W_bt i (Or.inr h2), and_true]
        omega

#print axioms P2
