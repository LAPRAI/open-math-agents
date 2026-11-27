import OMAStatements.S_oeis_a157713

open OMA.S_oeis_a157713 in
theorem OMA.solution : type_of% @OMA.S_oeis_a157713.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  unfold a
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by ring, show 2 * (m + 2) - 2 = 2 * m + 2 by omega,
    show m + 2 - 1 = m + 1 by omega, show 2 * (m + 1) + 1 = 2 * m + 3 by ring,
    show 2 * (m + 1) - 2 = 2 * m by omega, show m + 1 - 1 = m by omega]
  have e1 : (2 * m + 5).factorial = (2 * m + 5) * (2 * m + 4) * (2 * m + 3).factorial := by
    rw [show 2 * m + 5 = 2 * m + 3 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    ring
  have e2 : (2 * m + 2).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
    rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, Nat.factorial_succ (2 * m + 1),
      Nat.factorial_succ (2 * m), Nat.mul_assoc]
  have e4 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have e3 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
  rw [e1, e2, e4, e3]
  have h0 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h1 : ((2 * m).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : ((2 * m + 3).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h4 : ((m : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
