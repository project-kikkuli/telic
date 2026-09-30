-- Lean proofs for server/split.py, checked by telic.
-- Each block proves one obligation. telic regenerates the statements from the
-- code on every run; edit only the tactic proofs. A block whose statement no
-- longer matches the code is reported as stale and ignored.

-- telic: split_equal/inv.step@24>22 statement=f264a83b768e
theorem vc_split_equal_inv_step_24_22
    (amount : Int)
    (i_k_4 : Int)
    (parts : Int)
    (shares_5_arr : (Int → Int))
    (shares_5_len : Int)
    (seqsum_front : ∀ (a : (Int → Int)) (lo : Int) (hi : Int), lo < hi → seqsum a lo hi = a lo + seqsum a (lo + 1) hi)
    (seqsum_nonneg : ∀ (a : (Int → Int)) (lo : Int) (hi : Int), (∀ (i : Int), lo ≤ i ∧ i < hi → 0 ≤ a i) → 0 ≤ seqsum a lo hi)
    (seqsum_nonpos : ∀ (a : (Int → Int)) (lo : Int) (hi : Int), (∀ (i : Int), lo ≤ i ∧ i < hi → a i ≤ 0) → seqsum a lo hi ≤ 0)
    (seqsum_store : ∀ (a : (Int → Int)) (lo : Int) (hi : Int) (k : Int) (v : Int), seqsum (Telic.upd a k v) lo hi = seqsum a lo hi + (if lo ≤ k ∧ k < hi then v - a k else 0))
    (seqsum_split : ∀ (a : (Int → Int)) (lo : Int) (mid : Int) (hi : Int), lo ≤ mid ∧ mid ≤ hi → seqsum a lo hi = seqsum a lo mid + seqsum a mid hi)
    (share_of_spec : ∀ (amount : Int) (parts : Int) (index : Int), 0 ≤ amount ∧ 1 ≤ parts ∧ 0 ≤ index ∧ index < parts → 0 ≤ share_of amount parts index)
    (h1 : 0 ≤ amount)
    (h2 : 1 ≤ parts)
    (h3 : ¬parts = 0)
    (h4 : ¬parts = 0)
    (h5 : 0 ≤ shares_5_len)
    (h6 : 0 ≤ i_k_4)
    (h7 : i_k_4 ≤ (if 0 ≤ parts then parts else 0))
    (h8 : shares_5_len = i_k_4)
    (h9 : seqsum shares_5_arr 0 shares_5_len = (if 0 < parts then amount / parts else -amount / -parts) * i_k_4 + (if i_k_4 ≤ amount - parts * (if 0 < parts then amount / parts else -amount / -parts) then i_k_4 else amount - parts * (if 0 < parts then amount / parts else -amount / -parts)))
    (h10 : ∀ (s_6 : Int), 0 ≤ s_6 ∧ s_6 < shares_5_len → (if 0 < parts then amount / parts else -amount / -parts) ≤ shares_5_arr s_6 ∧ shares_5_arr s_6 ≤ (if 0 < parts then amount / parts else -amount / -parts) + 1)
    (h11 : ∀ (k_7 : Int), 0 ≤ k_7 ∧ k_7 < i_k_4 → shares_5_arr (if k_7 < 0 then k_7 + shares_5_len else k_7) = share_of amount parts k_7)
    (h12 : i_k_4 < parts)
    (h13 : i_k_4 < amount - parts * (if 0 < parts then amount / parts else -amount / -parts) ∨ ¬i_k_4 < amount - parts * (if 0 < parts then amount / parts else -amount / -parts)) :
    seqsum (if i_k_4 < amount - parts * (if 0 < parts then amount / parts else -amount / -parts) then Telic.upd shares_5_arr shares_5_len ((if 0 < parts then amount / parts else -amount / -parts) + 1) else Telic.upd shares_5_arr shares_5_len (if 0 < parts then amount / parts else -amount / -parts)) 0 (shares_5_len + 1) = (if 0 < parts then amount / parts else -amount / -parts) * (i_k_4 + 1) + (if i_k_4 + 1 ≤ amount - parts * (if 0 < parts then amount / parts else -amount / -parts) then i_k_4 + 1 else amount - parts * (if 0 < parts then amount / parts else -amount / -parts)) := by
  have hp : 0 < parts := by omega
  have hs : seqsum shares_5_arr 0 (shares_5_len + 1) = seqsum shares_5_arr 0 shares_5_len + shares_5_arr shares_5_len := by
    rw [seqsum_split shares_5_arr 0 shares_5_len (shares_5_len + 1) (by omega), seqsum_front shares_5_arr shares_5_len (shares_5_len + 1) (by omega)]
    have h0 : seqsum shares_5_arr (shares_5_len + 1) (shares_5_len + 1) = 0 := by
      first | (rw [seqsum]; simp) | (unfold seqsum; simp)
    rw [h0]
    omega
  simp only [if_pos hp] at h9 ⊢
  generalize amount - parts * (amount / parts) = e at h9 ⊢
  generalize amount / parts = b at h9 ⊢
  have hc : (0 ≤ shares_5_len ∧ shares_5_len < shares_5_len + 1) := by omega
  have hm : b * (i_k_4 + 1) = b * i_k_4 + b := by rw [Int.mul_add, Int.mul_one]
  rw [hm]
  by_cases hlt : i_k_4 < e
  · rw [if_pos hlt, seqsum_store, hs, if_pos hc]
    split at h9 <;> split <;> omega
  · rw [if_neg hlt, seqsum_store, hs, if_pos hc]
    split at h9 <;> split <;> omega
