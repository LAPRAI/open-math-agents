import OMAStatements.S_oeis_a088883

open OMA.S_oeis_a088883 in
theorem OMA.solution : type_of% @OMA.S_oeis_a088883.main := by
  intro p hp hN
  have h10 : ∀ L : List ℕ, Nat.ofDigits 10 L % 3 = L.sum % 3 := by
    intro L
    have := Nat.ofDigits_modEq 10 3 L
    rw [show 10 % 3 = 1 by norm_num, Nat.ofDigits_one] at this
    exact this
  have hr : rev p % 3 = p % 3 := by
    unfold rev
    rw [h10, List.sum_reverse, ← h10, Nat.ofDigits_digits]
  have hpow : 10 ^ (Nat.digits 10 p).length % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hmul : p * 10 ^ (Nat.digits 10 p).length % 3 = p % 3 := by
    rw [Nat.mul_mod, hpow, mul_one, Nat.mod_mod]
  have hge : p ≤ p * 10 ^ (Nat.digits 10 p).length :=
    Nat.le_mul_of_pos_right p (pow_pos (by norm_num) _)
  have h2 := hp.two_le
  by_cases h3 : p = 3
  · subst h3
    unfold rev at hN
    rw [Nat.digits_of_lt 10 3 (by norm_num) (by norm_num)] at hN
    norm_num [Nat.ofDigits] at hN
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  have hp2 : p % 3 ≠ 2 := by
    intro h
    have hd : 3 ∣ p * 10 ^ (Nat.digits 10 p).length + rev p + 2 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    have := hN.eq_one_or_self_of_dvd 3 hd
    omega
  have hodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with he | ho
    · have := hp.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.1 he)
      omega
    · exact Nat.odd_iff.1 ho
  omega
