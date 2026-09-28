-- Lean proofs for server/referrals.py, checked by telic.
-- Each block proves one obligation. telic regenerates the statements from the
-- code on every run; edit only the tactic proofs. A block whose statement no
-- longer matches the code is reported as stale and ignored.

-- telic: chained_bonus_is_product/ensures@18>19 statement=2f5ca002b5bd
theorem vc_chained_bonus_is_product_ensures_18_19
    (a : Int)
    (b : Int)
    (level_bonus_spec : ∀ (depth : Int), 0 ≤ depth → 1 ≤ level_bonus depth)
    (h1 : 0 ≤ a ∧ 0 ≤ b)
    (h2 : 1 ≤ level_bonus (a + b))
    (h3 : 1 ≤ level_bonus a)
    (h4 : 1 ≤ level_bonus b) :
    level_bonus (a + b) = level_bonus a * level_bonus b := by
  have hb := h1.2
  have key : ∀ k : Nat, level_bonus ((k:Int) + b) = level_bonus (k:Int) * level_bonus b := by
    intro k
    induction k with
    | zero =>
      have h0 : level_bonus 0 = 1 := by
        rw [level_bonus_def 0 (by omega)]; simp
      simp [h0]
    | succ n ih =>
      have e1 := level_bonus_def (((n+1:Nat):Int) + b) (by omega)
      have e2 := level_bonus_def ((n+1:Nat):Int) (by omega)
      have c1 : (((n+1:Nat):Int) + b) - 1 = (n:Int) + b := by omega
      have c2 : ((n+1:Nat):Int) - 1 = (n:Int) := by omega
      have n1 : ¬ (((n+1:Nat):Int) + b = 0) := by omega
      have n2 : ¬ (((n+1:Nat):Int) = 0) := by omega
      rw [if_neg n1, c1] at e1
      rw [if_neg n2, c2] at e2
      rw [e1, e2, ih, Int.mul_assoc]
  have := key a.toNat
  rwa [Int.toNat_of_nonneg h1.1] at this
