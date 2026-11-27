import OMAStatements.S_oeis_a071011

theorem OMA.solution : type_of% @OMA.S_oeis_a071011.main := by
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm ⟨0, 0, by simp⟩
  rw [Nat.eq_sq_add_sq_iff] at hm
  push_neg at hm
  obtain ⟨q, hqm, hq3, hodd⟩ := hm
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨j, hj⟩ := hodd
  have hfac : padicValNat q m = m.factorization q := (Nat.factorization_def m hq).symm
  have he : m.factorization q = 2 * j + 1 := by rw [← hfac]; exact hj
  have hsplit : m = q ^ m.factorization q * (m / q ^ m.factorization q) :=
    (Nat.ordProj_mul_ordCompl_eq_self m q).symm
  have hcop : Nat.Coprime (q ^ m.factorization q) (m / q ^ m.factorization q) :=
    (Nat.coprime_ordCompl hq hm0).pow_left _
  have key : ∀ i : ℕ, 4 ∣ ∑ k ∈ Finset.range (2 * i + 2), q ^ k := by
    intro i
    induction i with
    | zero =>
      rw [show 2 * 0 + 2 = 0 + 1 + 1 by rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      simp only [pow_zero, zero_add, pow_one]
      omega
    | succ i ih =>
      rw [show 2 * (i + 1) + 2 = 2 * i + 2 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, pow_succ q (2 * i + 2)]
      have h4 : 4 ∣ q ^ (2 * i + 2) * (1 + q) := Dvd.dvd.mul_left (by omega) _
      have h5 := Nat.dvd_add ih h4
      have h6 : ∑ k ∈ Finset.range (2 * i + 2), q ^ k + q ^ (2 * i + 2) * (1 + q) =
          ∑ k ∈ Finset.range (2 * i + 2), q ^ k + q ^ (2 * i + 2) + q ^ (2 * i + 2) * q := by
        ring
      rw [← h6]
      exact h5
  have h4 : 4 ∣ ArithmeticFunction.sigma 1 m := by
    rw [hsplit, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_one_apply_prime_pow hq]
    apply Dvd.dvd.mul_right
    rw [he, show 2 * j + 1 + 1 = 2 * j + 2 by ring]
    exact key j
  omega
