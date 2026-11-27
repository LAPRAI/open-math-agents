import OMAStatements.S_oeis_a151341

open OMA.S_oeis_a151341 in
theorem OMA.solution : type_of% @OMA.S_oeis_a151341.main := by
  have hc : ∀ k : ℕ, ((k : ℚ) + 2) * (catalan (k + 1) : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (catalan k : ℚ) := by
    intro k
    have h1 : (((k + 1 + 1 : ℕ) : ℚ)) * (catalan (k + 1) : ℚ)
        = ((Nat.centralBinom (k + 1) : ℕ) : ℚ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom (k + 1)
    have h2 : (((k + 1 : ℕ) : ℚ)) * (catalan k : ℚ) = ((Nat.centralBinom k : ℕ) : ℚ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom k
    have h3 : (((k + 1 : ℕ) : ℚ)) * ((Nat.centralBinom (k + 1) : ℕ) : ℚ)
        = 2 * (2 * (k : ℚ) + 1) * ((Nat.centralBinom k : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    push_cast at h1 h2 h3
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    linear_combination ((k : ℚ) + 1) * h1 + h3 - 2 * (2 * (k : ℚ) + 1) * h2
  have hm : ∀ k : ℕ, ((k : ℚ) + 4) * motzkin (k + 2)
      = (2 * (k : ℚ) + 5) * motzkin (k + 1) + 3 * ((k : ℚ) + 1) * motzkin k := by
    intro k
    have hk : ((k : ℚ) + 4) ≠ 0 := by positivity
    have e : motzkin (k + 2) = ((2 * (k : ℚ) + 5) * motzkin (k + 1)
        + 3 * ((k : ℚ) + 1) * motzkin k) / (k + 4 : ℚ) := by
      first | rfl | rw [motzkin] | simp [motzkin]
    rw [e]
    field_simp
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  rw [e1, e2]
  simp only [a]
  have hA : (((k + 1 : ℕ) : ℚ) + 2) * (catalan (k + 2) : ℚ)
      = 2 * (2 * ((k + 1 : ℕ) : ℚ) + 1) * (catalan (k + 1) : ℚ) := hc (k + 1)
  have hB := hc k
  have hM := hm k
  push_cast at hA ⊢
  linear_combination
    ((k : ℚ) + 2) * ((k : ℚ) + 3) * (catalan (k + 2) : ℚ) * hM
    + ((k : ℚ) + 2) * ((2 * (k : ℚ) + 5) * motzkin (k + 1) + 3 * ((k : ℚ) + 1) * motzkin k) * hA
    + 6 * ((k : ℚ) + 1) * (2 * (k : ℚ) + 3) * motzkin k * hB
