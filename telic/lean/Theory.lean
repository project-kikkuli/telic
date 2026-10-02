/-
  telic theory lemmas, machine-checked.

  telic hands Z3 a few facts about its built-in list functions (`seqsum`,
  `seqcount`) that need induction to prove. Z3 cannot prove them itself, so
  they are proved here, once, against the exact definitions telic uses
  (see `telic/logic.py`: seqsum_def, seqcount_def, theory_lemmas). The test
  suite checks this file with Lean on every run.
-/
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace TelicTheory

/-- `seqsum a lo hi = a lo + ... + a (hi - 1)`, as telic defines it. -/
def seqsum (a : Int → Int) (lo hi : Int) : Int :=
  if h : hi ≤ lo then 0 else seqsum a lo (hi - 1) + a (hi - 1)
termination_by (hi - lo).toNat
decreasing_by omega

/-- The same over rationals (telic's model of floats / JS numbers). -/
def seqsumR (a : Int → Rat) (lo hi : Int) : Rat :=
  if h : hi ≤ lo then 0 else seqsumR a lo (hi - 1) + a (hi - 1)
termination_by (hi - lo).toNat
decreasing_by omega

/-- Occurrences of `v` in `a lo .. a (hi - 1)`. -/
def seqcount {α : Type} [DecidableEq α] (a : Int → α) (lo hi : Int) (v : α) : Int :=
  if h : hi ≤ lo then 0 else seqcount a lo (hi - 1) v + (if a (hi - 1) = v then 1 else 0)
termination_by (hi - lo).toNat
decreasing_by omega

def upd {α : Type} (a : Int → α) (i : Int) (v : α) : Int → α := fun j => if j = i then v else a j

/-- A left fold over an integer-indexed array, used by checked state induction. -/
def seqfold {α β : Type} (step : α → β → α) (a : Int → β) (init : α) (lo hi : Int) : α :=
  if hi ≤ lo then init else step (seqfold step a init lo (hi - 1)) (a (hi - 1))
termination_by (hi - lo).toNat
decreasing_by omega

/-- Induction over the exact decreasing measure used by recursive array folds. -/
theorem seqfold_invariant {α β : Type} (step : α → β → α) (a : Int → β) (init : α)
    (P : α → Prop) (A : β → Prop) (lo hi : Int)
    (hbase : P init)
    (hstep : ∀ s x, P s → A x → P (step s x))
    (hitems : ∀ i, lo ≤ i → i < hi → A (a i)) :
    P (seqfold step a init lo hi) := by
  by_cases h : hi ≤ lo
  · simp [seqfold, h, hbase]
  · have hlo : lo < hi := by omega
    rw [seqfold, if_neg h]
    apply hstep
    · exact seqfold_invariant step a init P A lo (hi - 1) hbase hstep
        (fun i h1 h2 => hitems i h1 (by omega))
    · exact hitems (hi - 1) (by omega) (by omega)
termination_by (hi - lo).toNat
decreasing_by omega

-- ---------------------------------------------------------------------------
-- Integer sums

theorem seqsum_empty (a : Int → Int) (lo hi : Int) (h : hi ≤ lo) : seqsum a lo hi = 0 := by
  rw [seqsum]; simp [h]

theorem seqsum_last (a : Int → Int) (lo hi : Int) (h : lo < hi) :
    seqsum a lo hi = seqsum a lo (hi - 1) + a (hi - 1) := by
  rw [seqsum]; simp [show ¬ hi ≤ lo by omega]

theorem seqsum_front_aux (a : Int → Int) (lo : Int) (k : Nat) :
    seqsum a lo (lo + 1 + k) = a lo + seqsum a (lo + 1) (lo + 1 + k) := by
  induction k with
  | zero =>
    rw [seqsum_last a lo (lo + 1 + ((0 : Nat) : Int)) (by omega)]
    rw [seqsum_empty a lo (lo + 1 + ((0 : Nat) : Int) - 1) (by omega)]
    rw [seqsum_empty a (lo + 1) (lo + 1 + ((0 : Nat) : Int)) (by omega)]
    have : lo + 1 + ((0 : Nat) : Int) - 1 = lo := by omega
    rw [this]; omega
  | succ k ih =>
    rw [seqsum_last a lo _ (by omega), seqsum_last a (lo + 1) _ (by omega)]
    have e : lo + 1 + ((k + 1 : Nat) : Int) - 1 = lo + 1 + k := by omega
    rw [e, ih]; omega

/-- `seqsum_front`: a sum peels off its first element. -/
theorem seqsum_front (a : Int → Int) (lo hi : Int) (h : lo < hi) :
    seqsum a lo hi = a lo + seqsum a (lo + 1) hi := by
  have := seqsum_front_aux a lo (hi - lo - 1).toNat
  have e : lo + 1 + ((hi - lo - 1).toNat : Int) = hi := by omega
  rwa [e] at this

theorem seqsum_nonneg_aux (a : Int → Int) (lo : Int) (k : Nat)
    (h : ∀ i, lo ≤ i → i < lo + k → 0 ≤ a i) : 0 ≤ seqsum a lo (lo + k) := by
  induction k with
  | zero => rw [seqsum_empty a lo _ (by omega)]; omega
  | succ k ih =>
    rw [seqsum_last a lo _ (by omega)]
    have e : lo + ((k + 1 : Nat) : Int) - 1 = lo + k := by omega
    rw [e]
    have h1 := ih (fun i hi1 hi2 => h i hi1 (by omega))
    have h2 := h (lo + k) (by omega) (by omega)
    omega

/-- `seqsum_nonneg`: a sum of non-negatives is non-negative. -/
theorem seqsum_nonneg (a : Int → Int) (lo hi : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → 0 ≤ a i) : 0 ≤ seqsum a lo hi := by
  by_cases hl : hi ≤ lo
  · rw [seqsum_empty a lo hi hl]; omega
  · have := seqsum_nonneg_aux a lo (hi - lo).toNat (fun i h1 h2 => h i ⟨h1, by omega⟩)
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

theorem seqsum_nonpos_aux (a : Int → Int) (lo : Int) (k : Nat)
    (h : ∀ i, lo ≤ i → i < lo + k → a i ≤ 0) : seqsum a lo (lo + k) ≤ 0 := by
  induction k with
  | zero => rw [seqsum_empty a lo _ (by omega)]; omega
  | succ k ih =>
    rw [seqsum_last a lo _ (by omega)]
    have e : lo + ((k + 1 : Nat) : Int) - 1 = lo + k := by omega
    rw [e]
    have h1 := ih (fun i hi1 hi2 => h i hi1 (by omega))
    have h2 := h (lo + k) (by omega) (by omega)
    omega

/-- `seqsum_nonpos`: a sum of non-positives is non-positive. -/
theorem seqsum_nonpos (a : Int → Int) (lo hi : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → a i ≤ 0) : seqsum a lo hi ≤ 0 := by
  by_cases hl : hi ≤ lo
  · rw [seqsum_empty a lo hi hl]; omega
  · have := seqsum_nonpos_aux a lo (hi - lo).toNat (fun i h1 h2 => h i ⟨h1, by omega⟩)
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

theorem seqsum_store_aux (a : Int → Int) (lo k v : Int) (n : Nat) :
    seqsum (upd a k v) lo (lo + n) = seqsum a lo (lo + n) + (if lo ≤ k ∧ k < lo + n then v - a k else 0) := by
  induction n with
  | zero =>
    rw [seqsum_empty _ lo _ (by omega), seqsum_empty _ lo _ (by omega)]
    simp; omega
  | succ n ih =>
    rw [seqsum_last (upd a k v) lo _ (by omega), seqsum_last a lo _ (by omega)]
    have e : lo + ((n + 1 : Nat) : Int) - 1 = lo + n := by omega
    rw [e, ih]
    simp only [upd]
    by_cases hk : k = lo + (n : Int)
    · subst hk; split <;> split <;> split <;> omega
    · split <;> split <;> split <;> omega

/-- `seqsum_store`: updating one element changes the sum by the difference. -/
theorem seqsum_store (a : Int → Int) (lo hi k v : Int) :
    seqsum (upd a k v) lo hi = seqsum a lo hi + (if lo ≤ k ∧ k < hi then v - a k else 0) := by
  by_cases hl : hi ≤ lo
  · rw [seqsum_empty _ lo hi hl, seqsum_empty _ lo hi hl]
    have : ¬ (lo ≤ k ∧ k < hi) := by omega
    simp [this]
  · have := seqsum_store_aux a lo k v (hi - lo).toNat
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

theorem seqsum_split_aux (a : Int → Int) (lo mid : Int) (h : lo ≤ mid) (n : Nat) :
    seqsum a lo (mid + n) = seqsum a lo mid + seqsum a mid (mid + n) := by
  induction n with
  | zero => rw [seqsum_empty a mid _ (by omega)]; simp
  | succ n ih =>
    rw [seqsum_last a lo _ (by omega), seqsum_last a mid _ (by omega)]
    have e : mid + ((n + 1 : Nat) : Int) - 1 = mid + n := by omega
    rw [e, ih]; omega

/-- `seqsum_split`: a sum splits at any midpoint. -/
theorem seqsum_split (a : Int → Int) (lo mid hi : Int) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    seqsum a lo hi = seqsum a lo mid + seqsum a mid hi := by
  have := seqsum_split_aux a lo mid h1 (hi - mid).toNat
  have e : mid + ((hi - mid).toNat : Int) = hi := by omega
  rwa [e] at this

theorem seqsum_ext_aux (a b : Int → Int) (lo : Int) (n : Nat)
    (h : ∀ i, lo ≤ i → i < lo + n → a i = b i) : seqsum a lo (lo + n) = seqsum b lo (lo + n) := by
  induction n with
  | zero => rw [seqsum_empty a lo _ (by omega), seqsum_empty b lo _ (by omega)]
  | succ n ih =>
    rw [seqsum_last a lo _ (by omega), seqsum_last b lo _ (by omega)]
    have e : lo + ((n + 1 : Nat) : Int) - 1 = lo + n := by omega
    rw [e, ih (fun i h1 h2 => h i h1 (by omega)), h (lo + n) (by omega) (by omega)]

/-- `seqsum_ext`: sums of lists that agree on the range are equal. -/
theorem seqsum_ext (a b : Int → Int) (lo hi : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → a i = b i) : seqsum a lo hi = seqsum b lo hi := by
  by_cases hl : hi ≤ lo
  · rw [seqsum_empty a lo hi hl, seqsum_empty b lo hi hl]
  · have := seqsum_ext_aux a b lo (hi - lo).toNat (fun i h1 h2 => h i ⟨h1, by omega⟩)
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

/-- `seqsum_elem_le`: each of non-negatives is at most their sum. -/
theorem seqsum_elem_le (a : Int → Int) (lo hi k : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → 0 ≤ a i) (hk : lo ≤ k ∧ k < hi) : a k ≤ seqsum a lo hi := by
  rw [seqsum_split a lo k hi (by omega) (by omega), seqsum_front a k hi (by omega)]
  have h1 := seqsum_nonneg a lo k (fun i hi' => h i ⟨hi'.1, by omega⟩)
  have h2 := seqsum_nonneg a (k + 1) hi (fun i hi' => h i ⟨by omega, hi'.2⟩)
  omega

/-- `seqsum_elem_ge`: each of non-positives is at least their sum. -/
theorem seqsum_elem_ge (a : Int → Int) (lo hi k : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → a i ≤ 0) (hk : lo ≤ k ∧ k < hi) : seqsum a lo hi ≤ a k := by
  rw [seqsum_split a lo k hi (by omega) (by omega), seqsum_front a k hi (by omega)]
  have h1 := seqsum_nonpos a lo k (fun i hi' => h i ⟨hi'.1, by omega⟩)
  have h2 := seqsum_nonpos a (k + 1) hi (fun i hi' => h i ⟨by omega, hi'.2⟩)
  omega

-- ---------------------------------------------------------------------------
-- Counts

theorem seqcount_bounds_aux {α : Type} [DecidableEq α] (a : Int → α) (lo : Int) (v : α) (n : Nat) :
    0 ≤ seqcount a lo (lo + n) v ∧ seqcount a lo (lo + n) v ≤ n := by
  induction n with
  | zero => rw [seqcount]; simp
  | succ n ih =>
    rw [seqcount]
    have : ¬ (lo + ((n + 1 : Nat) : Int) ≤ lo) := by omega
    simp only [this, dite_false]
    have e : lo + ((n + 1 : Nat) : Int) - 1 = lo + n := by omega
    rw [e]
    split <;> omega

/-- `seqcount_bounds`: a count lies between 0 and the length. -/
theorem seqcount_bounds {α : Type} [DecidableEq α] (a : Int → α) (lo hi : Int) (v : α) :
    0 ≤ seqcount a lo hi v ∧ seqcount a lo hi v ≤ max (hi - lo) 0 := by
  by_cases hl : hi ≤ lo
  · rw [seqcount]; simp [hl]; omega
  · have := seqcount_bounds_aux a lo v (hi - lo).toNat
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rw [e] at this
    omega

theorem seqcount_front_aux {α : Type} [DecidableEq α] (a : Int → α) (lo : Int) (v : α) (k : Nat) :
    seqcount a lo (lo + 1 + k) v = (if a lo = v then 1 else 0) + seqcount a (lo + 1) (lo + 1 + k) v := by
  induction k with
  | zero =>
    have e1 : lo + 1 + ((0 : Nat) : Int) = lo + 1 := by omega
    have z : seqcount a (lo + 1) (lo + 1) v = 0 := by rw [seqcount]; simp
    have z2 : seqcount a lo lo v = 0 := by rw [seqcount]; simp
    rw [e1, z, seqcount]
    simp only [show ¬ (lo + 1 ≤ lo) by omega, dite_false]
    have e2 : lo + 1 - 1 = lo := by omega
    rw [e2, z2]; simp
  | succ k ih =>
    have e : lo + 1 + ((k + 1 : Nat) : Int) - 1 = lo + 1 + k := by omega
    have l1 : seqcount a lo (lo + 1 + ((k + 1 : Nat) : Int)) v
        = seqcount a lo (lo + 1 + k) v + (if a (lo + 1 + k) = v then 1 else 0) := by
      rw [seqcount]; simp only [show ¬ (lo + 1 + ((k + 1 : Nat) : Int) ≤ lo) by omega, dite_false]; rw [e]
    have l2 : seqcount a (lo + 1) (lo + 1 + ((k + 1 : Nat) : Int)) v
        = seqcount a (lo + 1) (lo + 1 + k) v + (if a (lo + 1 + k) = v then 1 else 0) := by
      rw [seqcount]; simp only [show ¬ (lo + 1 + ((k + 1 : Nat) : Int) ≤ lo + 1) by omega, dite_false]; rw [e]
    rw [l1, l2, ih]; omega

/-- `seqcount_front`: a count peels off its first element. -/
theorem seqcount_front {α : Type} [DecidableEq α] (a : Int → α) (lo hi : Int) (v : α) (h : lo < hi) :
    seqcount a lo hi v = (if a lo = v then 1 else 0) + seqcount a (lo + 1) hi v := by
  have := seqcount_front_aux a lo v (hi - lo - 1).toNat
  have e : lo + 1 + ((hi - lo - 1).toNat : Int) = hi := by omega
  rwa [e] at this


-- ---------------------------------------------------------------------------
-- Rational sums (floats / JS numbers are modelled as exact rationals)

theorem seqsumR_empty (a : Int → Rat) (lo hi : Int) (h : hi ≤ lo) : seqsumR a lo hi = 0 := by
  rw [seqsumR]; simp [h]

theorem seqsumR_last (a : Int → Rat) (lo hi : Int) (h : lo < hi) :
    seqsumR a lo hi = seqsumR a lo (hi - 1) + a (hi - 1) := by
  rw [seqsumR]; simp [show ¬ hi ≤ lo by omega]

theorem seqsumR_front_aux (a : Int → Rat) (lo : Int) (k : Nat) :
    seqsumR a lo (lo + 1 + k) = a lo + seqsumR a (lo + 1) (lo + 1 + k) := by
  induction k with
  | zero =>
    have e1 : lo + 1 + ((0 : Nat) : Int) = lo + 1 := by omega
    rw [e1, seqsumR_last a lo (lo + 1) (by omega), seqsumR_empty a (lo + 1) (lo + 1) (by omega)]
    have e2 : lo + 1 - 1 = lo := by omega
    rw [e2, seqsumR_empty a lo lo (by omega)]
    grind
  | succ k ih =>
    rw [seqsumR_last a lo _ (by omega), seqsumR_last a (lo + 1) _ (by omega)]
    have e : lo + 1 + ((k + 1 : Nat) : Int) - 1 = lo + 1 + k := by omega
    rw [e, ih]; grind

theorem seqsumR_front (a : Int → Rat) (lo hi : Int) (h : lo < hi) :
    seqsumR a lo hi = a lo + seqsumR a (lo + 1) hi := by
  have := seqsumR_front_aux a lo (hi - lo - 1).toNat
  have e : lo + 1 + ((hi - lo - 1).toNat : Int) = hi := by omega
  rwa [e] at this

theorem seqsumR_nonneg_aux (a : Int → Rat) (lo : Int) (k : Nat)
    (h : ∀ i, lo ≤ i → i < lo + k → 0 ≤ a i) : 0 ≤ seqsumR a lo (lo + k) := by
  induction k with
  | zero => rw [seqsumR_empty a lo _ (by omega)]; grind
  | succ k ih =>
    rw [seqsumR_last a lo _ (by omega)]
    have e : lo + ((k + 1 : Nat) : Int) - 1 = lo + k := by omega
    rw [e]
    have h1 := ih (fun i hi1 hi2 => h i hi1 (by omega))
    have h2 := h (lo + k) (by omega) (by omega)
    grind

theorem seqsumR_nonneg (a : Int → Rat) (lo hi : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → 0 ≤ a i) : 0 ≤ seqsumR a lo hi := by
  by_cases hl : hi ≤ lo
  · rw [seqsumR_empty a lo hi hl]; grind
  · have := seqsumR_nonneg_aux a lo (hi - lo).toNat (fun i h1 h2 => h i ⟨h1, by omega⟩)
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

theorem seqsumR_nonpos_aux (a : Int → Rat) (lo : Int) (k : Nat)
    (h : ∀ i, lo ≤ i → i < lo + k → a i ≤ 0) : seqsumR a lo (lo + k) ≤ 0 := by
  induction k with
  | zero => rw [seqsumR_empty a lo _ (by omega)]; grind
  | succ k ih =>
    rw [seqsumR_last a lo _ (by omega)]
    have e : lo + ((k + 1 : Nat) : Int) - 1 = lo + k := by omega
    rw [e]
    have h1 := ih (fun i hi1 hi2 => h i hi1 (by omega))
    have h2 := h (lo + k) (by omega) (by omega)
    grind

/-- `seqsumR_nonpos`: a sum of non-positives is non-positive. -/
theorem seqsumR_nonpos (a : Int → Rat) (lo hi : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → a i ≤ 0) : seqsumR a lo hi ≤ 0 := by
  by_cases hl : hi ≤ lo
  · rw [seqsumR_empty a lo hi hl]; grind
  · have := seqsumR_nonpos_aux a lo (hi - lo).toNat (fun i h1 h2 => h i ⟨h1, by omega⟩)
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

theorem seqsumR_store_aux (a : Int → Rat) (lo k : Int) (v : Rat) (n : Nat) :
    seqsumR (upd a k v) lo (lo + n) = seqsumR a lo (lo + n) + (if lo ≤ k ∧ k < lo + n then v - a k else 0) := by
  induction n with
  | zero =>
    rw [seqsumR_empty _ lo _ (by omega), seqsumR_empty _ lo _ (by omega)]
    split <;> grind
  | succ n ih =>
    rw [seqsumR_last (upd a k v) lo _ (by omega), seqsumR_last a lo _ (by omega)]
    have e : lo + ((n + 1 : Nat) : Int) - 1 = lo + n := by omega
    rw [e, ih]
    simp only [upd]
    by_cases hk : k = lo + (n : Int)
    · subst hk
      have c1 : ¬ (lo ≤ lo + (n : Int) ∧ lo + (n : Int) < lo + n) := by omega
      have c2 : lo ≤ lo + (n : Int) ∧ lo + (n : Int) < lo + ((n + 1 : Nat) : Int) := by omega
      rw [if_neg c1, if_pos c2]; simp; grind
    · have c0 : ¬ (k = lo + (n : Int)) := hk
      by_cases hr : lo ≤ k ∧ k < lo + (n : Int)
      · have c2 : lo ≤ k ∧ k < lo + ((n + 1 : Nat) : Int) := by omega
        rw [if_pos hr, if_pos c2]; simp [show ¬ (lo + (n : Int) = k) by omega]; grind
      · have c2 : ¬ (lo ≤ k ∧ k < lo + ((n + 1 : Nat) : Int)) := by omega
        rw [if_neg hr, if_neg c2]; simp [show ¬ (lo + (n : Int) = k) by omega] <;> grind

theorem seqsumR_store (a : Int → Rat) (lo hi k : Int) (v : Rat) :
    seqsumR (upd a k v) lo hi = seqsumR a lo hi + (if lo ≤ k ∧ k < hi then v - a k else 0) := by
  by_cases hl : hi ≤ lo
  · rw [seqsumR_empty _ lo hi hl, seqsumR_empty _ lo hi hl]
    have : ¬ (lo ≤ k ∧ k < hi) := by omega
    simp [this] <;> grind
  · have := seqsumR_store_aux a lo k v (hi - lo).toNat
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

theorem seqsumR_split_aux (a : Int → Rat) (lo mid : Int) (h : lo ≤ mid) (n : Nat) :
    seqsumR a lo (mid + n) = seqsumR a lo mid + seqsumR a mid (mid + n) := by
  induction n with
  | zero => rw [seqsumR_empty a mid _ (by omega)]; grind
  | succ n ih =>
    rw [seqsumR_last a lo _ (by omega), seqsumR_last a mid _ (by omega)]
    have e : mid + ((n + 1 : Nat) : Int) - 1 = mid + n := by omega
    rw [e, ih]; grind

theorem seqsumR_split (a : Int → Rat) (lo mid hi : Int) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    seqsumR a lo hi = seqsumR a lo mid + seqsumR a mid hi := by
  have := seqsumR_split_aux a lo mid h1 (hi - mid).toNat
  have e : mid + ((hi - mid).toNat : Int) = hi := by omega
  rwa [e] at this

theorem seqsumR_ext_aux (a b : Int → Rat) (lo : Int) (n : Nat)
    (h : ∀ i, lo ≤ i → i < lo + n → a i = b i) : seqsumR a lo (lo + n) = seqsumR b lo (lo + n) := by
  induction n with
  | zero => rw [seqsumR_empty a lo _ (by omega), seqsumR_empty b lo _ (by omega)]
  | succ n ih =>
    rw [seqsumR_last a lo _ (by omega), seqsumR_last b lo _ (by omega)]
    have e : lo + ((n + 1 : Nat) : Int) - 1 = lo + n := by omega
    rw [e, ih (fun i h1 h2 => h i h1 (by omega)), h (lo + n) (by omega) (by omega)]

theorem seqsumR_ext (a b : Int → Rat) (lo hi : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → a i = b i) : seqsumR a lo hi = seqsumR b lo hi := by
  by_cases hl : hi ≤ lo
  · rw [seqsumR_empty a lo hi hl, seqsumR_empty b lo hi hl]
  · have := seqsumR_ext_aux a b lo (hi - lo).toNat (fun i h1 h2 => h i ⟨h1, by omega⟩)
    have e : lo + ((hi - lo).toNat : Int) = hi := by omega
    rwa [e] at this

theorem seqsumR_elem_le (a : Int → Rat) (lo hi k : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → 0 ≤ a i) (hk : lo ≤ k ∧ k < hi) : a k ≤ seqsumR a lo hi := by
  rw [seqsumR_split a lo k hi (by omega) (by omega), seqsumR_front a k hi (by omega)]
  have h1 := seqsumR_nonneg a lo k (fun i hi' => h i ⟨hi'.1, by omega⟩)
  have h2 := seqsumR_nonneg a (k + 1) hi (fun i hi' => h i ⟨by omega, hi'.2⟩)
  grind

theorem seqsumR_elem_ge (a : Int → Rat) (lo hi k : Int)
    (h : ∀ i, lo ≤ i ∧ i < hi → a i ≤ 0) (hk : lo ≤ k ∧ k < hi) : seqsumR a lo hi ≤ a k := by
  rw [seqsumR_split a lo k hi (by omega) (by omega), seqsumR_front a k hi (by omega)]
  have h1 := seqsumR_nonpos a lo k (fun i hi' => h i ⟨hi'.1, by omega⟩)
  have h2 := seqsumR_nonpos a (k + 1) hi (fun i hi' => h i ⟨by omega, hi'.2⟩)
  grind

end TelicTheory
