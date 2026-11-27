import OMAStatements.S_oeis_a141353

open OMA.S_oeis_a141353 in
theorem OMA.solution : type_of% @OMA.S_oeis_a141353.main := by
  have hc : ∀ j : ℕ, ((j : ℤ) + 2) * (catalan (j + 1) : ℤ)
      = 2 * (2 * (j : ℤ) + 1) * (catalan j : ℤ) := by
    intro j
    have h1 : (((j + 1 + 1 : ℕ) : ℤ)) * (catalan (j + 1) : ℤ)
        = ((Nat.centralBinom (j + 1) : ℕ) : ℤ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom (j + 1)
    have h2 : (((j + 1 : ℕ) : ℤ)) * (catalan j : ℤ) = ((Nat.centralBinom j : ℕ) : ℤ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom j
    have h3 : (((j + 1 : ℕ) : ℤ)) * ((Nat.centralBinom (j + 1) : ℕ) : ℤ)
        = 2 * (2 * (j : ℤ) + 1) * ((Nat.centralBinom j : ℕ) : ℤ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ j
    push_cast at h1 h2 h3
    have hj : ((j : ℤ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hj
    linear_combination ((j : ℤ) + 1) * h1 + h3 - 2 * (2 * (j : ℤ) + 1) * h2
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  rw [e1, e2, e3]
  simp only [a]
  rw [zero_pow (by omega : k + 4 ≠ 0), zero_pow (by omega : k + 3 ≠ 0),
    zero_pow (by omega : k + 2 ≠ 0), zero_pow (by omega : k + 1 ≠ 0)]
  have h3 : (((k + 3 : ℕ) : ℤ) + 2) * (catalan (k + 4) : ℤ)
      = 2 * (2 * ((k + 3 : ℕ) : ℤ) + 1) * (catalan (k + 3) : ℤ) := hc (k + 3)
  have h2 : (((k + 2 : ℕ) : ℤ) + 2) * (catalan (k + 3) : ℤ)
      = 2 * (2 * ((k + 2 : ℕ) : ℤ) + 1) * (catalan (k + 2) : ℤ) := hc (k + 2)
  have h1 : (((k + 1 : ℕ) : ℤ) + 2) * (catalan (k + 2) : ℤ)
      = 2 * (2 * ((k + 1 : ℕ) : ℤ) + 1) * (catalan (k + 1) : ℤ) := hc (k + 1)
  push_cast at h1 h2 h3 ⊢
  linear_combination h3 - 4 * h2 + 4 * h1
