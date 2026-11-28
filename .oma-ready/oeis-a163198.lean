import OMAStatements.S_oeis_a163198
import Mathlib

open OMA.S_oeis_a163198 in
theorem OMA.solution : type_of% @OMA.S_oeis_a163198.main := by
  have cas : ∀ n : ℕ, (Nat.fib (2 * n + 2) : ℚ) ^ 2
      - (Nat.fib (2 * n + 2) : ℚ) * (Nat.fib (2 * n + 1) : ℚ)
      - (Nat.fib (2 * n + 1) : ℚ) ^ 2 = -1 := by
    intro n
    induction n with
    | zero =>
      show (Nat.fib 2 : ℚ) ^ 2 - (Nat.fib 2 : ℚ) * (Nat.fib 1 : ℚ) - (Nat.fib 1 : ℚ) ^ 2 = -1
      rw [Nat.fib_two, Nat.fib_one]
      norm_num
    | succ k ih =>
      have h1 := @Nat.fib_add_two (2 * k + 1)
      rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 by ring] at h1
      have h2 := @Nat.fib_add_two (2 * k + 2)
      rw [show 2 * k + 2 + 2 = 2 * (k + 1) + 2 by ring,
        show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by ring] at h2
      have e1 : (Nat.fib (2 * (k + 1) + 1) : ℚ) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
        exact_mod_cast h1
      have e2 : (Nat.fib (2 * (k + 1) + 2) : ℚ)
          = Nat.fib (2 * k + 2) + Nat.fib (2 * (k + 1) + 1) := by
        exact_mod_cast h2
      rw [e2, e1]
      linear_combination ih
  intro n
  induction n with
  | zero =>
    have h0 : a 0 = 0 := by first | rfl | decide | simp [a]
    rw [h0]
    norm_num [Nat.fib_one]
  | succ k ih =>
    have hs : (a (k + 1) : ℚ) = a k + (Nat.fib (2 * k + 2) : ℚ) ^ 3 := by
      have h : a (k + 1) = a k + Nat.fib (2 * (k + 1)) ^ 3 := by
        unfold a
        rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega)]
      rw [h, show 2 * (k + 1) = 2 * k + 2 by ring, Nat.cast_add, Nat.cast_pow]
    have h1 := @Nat.fib_add_two (2 * k + 1)
    rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring] at h1
    have e : (Nat.fib (2 * (k + 1) + 1) : ℚ) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
      exact_mod_cast h1
    rw [hs, ih, e]
    linear_combination (3 * (Nat.fib (2 * k + 2) : ℚ) / 4) * cas k
