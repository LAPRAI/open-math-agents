import OMAStatements.S_oeis_a093387
import Mathlib

open OMA.S_oeis_a093387 in
theorem OMA.solution : type_of% @OMA.S_oeis_a093387.main := by
  have A : ∀ j : ℕ, (j + 1) * Nat.choose (2 * j + 1) j = (2 * j + 1) * Nat.choose (2 * j) j := by
    intro j
    have h := Nat.add_one_mul_choose_eq (2 * j) j
    rw [Nat.choose_symm_half] at h
    first | exact (mul_comm _ _).trans h.symm | linarith | nlinarith [h]
  have B : ∀ j : ℕ, Nat.choose (2 * j + 2) (j + 1) = 2 * Nat.choose (2 * j + 1) j := by
    intro j
    have h := Nat.choose_succ_succ' (2 * j + 1) j
    rw [Nat.choose_symm_half, show 2 * j + 1 + 1 = 2 * j + 2 by ring] at h
    first | omega | linarith
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have ha0 : a (2 * m + 4) = 2 ^ (2 * m + 3) - (Nat.choose (2 * (m + 1) + 2) (m + 1 + 1) : ℤ) := by
      rw [show 2 * m + 4 = 2 * (m + 1) + 2 by ring]
      simp only [a]
      rw [show 2 * (m + 1) + 2 - 1 = 2 * m + 3 by omega, show (2 * (m + 1) + 2) / 2 = m + 1 + 1 by omega]
    have ha1 : a (2 * m + 4 - 1) = 2 ^ (2 * m + 2) - (Nat.choose (2 * (m + 1) + 1) (m + 1) : ℤ) := by
      rw [show 2 * m + 4 - 1 = 2 * (m + 1) + 1 by omega]
      simp only [a]
      rw [show 2 * (m + 1) + 1 - 1 = 2 * m + 2 by omega, show (2 * (m + 1) + 1) / 2 = m + 1 by omega]
    have ha2 : a (2 * m + 4 - 2) = 2 ^ (2 * m + 1) - (Nat.choose (2 * m + 2) (m + 1) : ℤ) := by
      rw [show 2 * m + 4 - 2 = 2 * m + 2 by omega]
      simp only [a]
      rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega, show (2 * m + 2) / 2 = m + 1 by omega]
    have ha3 : a (2 * m + 4 - 3) = 2 ^ (2 * m) - (Nat.choose (2 * m + 1) m : ℤ) := by
      rw [show 2 * m + 4 - 3 = 2 * m + 1 by omega]
      simp only [a]
      rw [show 2 * m + 1 - 1 = 2 * m by omega, show (2 * m + 1) / 2 = m by omega]
    have r4 := congrArg (Nat.cast : ℕ → ℤ) (B (m + 1))
    have r2 := congrArg (Nat.cast : ℕ → ℤ) (B m)
    push_cast at r4 r2
    rw [ha0, ha1, ha2, ha3]
    push_cast
    linear_combination -(2 * (m : ℤ) + 5) * r4 + 8 * ((m : ℤ) + 1) * r2
  · have ha0 : a (2 * m + 1 + 4) = 2 ^ (2 * m + 4) - (Nat.choose (2 * (m + 2) + 1) (m + 2) : ℤ) := by
      rw [show 2 * m + 1 + 4 = 2 * (m + 2) + 1 by ring]
      simp only [a]
      rw [show 2 * (m + 2) + 1 - 1 = 2 * m + 4 by omega, show (2 * (m + 2) + 1) / 2 = m + 2 by omega]
    have ha1 : a (2 * m + 1 + 4 - 1) = 2 ^ (2 * m + 3) - (Nat.choose (2 * (m + 2)) (m + 2) : ℤ) := by
      rw [show 2 * m + 1 + 4 - 1 = 2 * (m + 2) by omega]
      simp only [a]
      rw [show 2 * (m + 2) - 1 = 2 * m + 3 by omega, show 2 * (m + 2) / 2 = m + 2 by omega]
    have ha2 : a (2 * m + 1 + 4 - 2) = 2 ^ (2 * m + 2) - (Nat.choose (2 * (m + 1) + 1) (m + 1) : ℤ) := by
      rw [show 2 * m + 1 + 4 - 2 = 2 * (m + 1) + 1 by omega]
      simp only [a]
      rw [show 2 * (m + 1) + 1 - 1 = 2 * m + 2 by omega, show (2 * (m + 1) + 1) / 2 = m + 1 by omega]
    have ha3 : a (2 * m + 1 + 4 - 3) = 2 ^ (2 * m + 1) - (Nat.choose (2 * (m + 1)) (m + 1) : ℤ) := by
      rw [show 2 * m + 1 + 4 - 3 = 2 * (m + 1) by omega]
      simp only [a]
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) / 2 = m + 1 by omega]
    have br : Nat.choose (2 * (m + 2)) (m + 2) = Nat.choose (2 * (m + 1) + 2) (m + 1 + 1) :=
      congrArg₂ Nat.choose (by ring) rfl
    have s2 := congrArg (Nat.cast : ℕ → ℤ) (A (m + 2))
    have s1 := congrArg (Nat.cast : ℕ → ℤ) (A (m + 1))
    have p := congrArg (Nat.cast : ℕ → ℤ) (B (m + 1))
    have br' := congrArg (Nat.cast : ℕ → ℤ) br
    push_cast at s2 s1 p br'
    rw [ha0, ha1, ha2, ha3]
    push_cast
    linear_combination -2 * s2 + 2 * p + 2 * br' + 8 * s1
