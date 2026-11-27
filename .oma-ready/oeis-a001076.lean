import OMAStatements.S_oeis_a001076

open OMA.S_oeis_a001076 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001076.main := by
  have key : ∀ n : ℕ,
      ((2 : ℤ) * (A001076 (n + 1) : ℤ) = (A001076 (n + 2) : ℤ) - (A001077 (n + 1) : ℤ)) ∧
      ((2 : ℤ) * (A001076 (n + 2) : ℤ) = (A001076 (n + 3) : ℤ) - (A001077 (n + 2) : ℤ)) := by
    intro n
    induction n with
    | zero => exact ⟨by decide, by decide⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e3 : A001076 (k + 3) = 4 * A001076 (k + 2) + A001076 (k + 1) := rfl
      have e4 : A001076 (k + 4) = 4 * A001076 (k + 3) + A001076 (k + 2) := rfl
      have f3 : A001077 (k + 3) = 4 * A001077 (k + 2) + A001077 (k + 1) := rfl
      have e3' : (A001076 (k + 3) : ℤ) = 4 * A001076 (k + 2) + A001076 (k + 1) := by
        exact_mod_cast e3
      have e4' : (A001076 (k + 4) : ℤ) = 4 * A001076 (k + 3) + A001076 (k + 2) := by
        exact_mod_cast e4
      have f3' : (A001077 (k + 3) : ℤ) = 4 * A001077 (k + 2) + A001077 (k + 1) := by
        exact_mod_cast f3
      show (2 : ℤ) * (A001076 (k + 3) : ℤ) = (A001076 (k + 4) : ℤ) - (A001077 (k + 3) : ℤ)
      linear_combination 4 * ih.2 + ih.1 - e4' + 2 * e3' + f3'
  exact fun n => (key n).1
