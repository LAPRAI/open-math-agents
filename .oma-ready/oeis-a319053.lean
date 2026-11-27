import OMAStatements.S_oeis_a319053

namespace OMA.P_oeis_a319053

open OMA.S_oeis_a319053

lemma fib_par (n : ℕ) :
    Nat.fib (3 * n) % 2 = 0 ∧ Nat.fib (3 * n + 1) % 2 = 1 ∧ Nat.fib (3 * n + 2) % 2 = 1 := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> decide
  | succ n ih =>
    have h1 : Nat.fib (3 * n + 3) = Nat.fib (3 * n + 1) + Nat.fib (3 * n + 2) :=
      Nat.fib_add_two (n := 3 * n + 1)
    have h2 : Nat.fib (3 * n + 4) = Nat.fib (3 * n + 2) + Nat.fib (3 * n + 3) :=
      Nat.fib_add_two (n := 3 * n + 2)
    have h3 : Nat.fib (3 * n + 5) = Nat.fib (3 * n + 3) + Nat.fib (3 * n + 4) :=
      Nat.fib_add_two (n := 3 * n + 3)
    rw [show 3 * (n + 1) = 3 * n + 3 by ring, show 3 * (n + 1) + 1 = 3 * n + 4 by ring,
      show 3 * (n + 1) + 2 = 3 * n + 5 by ring]
    omega

lemma odd_fib (n : ℕ) (h : ¬ 3 ∣ n) : Nat.fib n % 2 = 1 := by
  rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with h1 | h1
  · have := (fib_par (n / 3)).2.1
    rwa [show 3 * (n / 3) + 1 = n by omega] at this
  · have := (fib_par (n / 3)).2.2
    rwa [show 3 * (n / 3) + 2 = n by omega] at this

lemma v2 (k : ℕ) (x : ℤ) (hx : ¬ (2 : ℤ) ∣ x) : padicValInt 2 (2 ^ k * x) = k := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (dvd_zero _)
  rw [padicValInt.mul (pow_ne_zero _ two_ne_zero) hx0,
    padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hx), add_zero]
  simp [padicValInt, Int.natAbs_pow, padicValNat.prime_pow]

lemma pow_form (n : ℕ) : M ^ (n + 1) =
    !![2 ^ n * (3 * (Nat.fib (n + 1) : ℤ) + 2 * Nat.fib n), 2 ^ n * (Nat.fib (n + 1) : ℤ);
      2 ^ n * (Nat.fib (n + 1) : ℤ), 2 ^ n * (2 * (Nat.fib n : ℤ) - Nat.fib (n + 1))] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M]
  | succ n ih =>
    rw [pow_succ, ih]
    have hf : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two
    have hf' : (Nat.fib (n + 1 + 1) : ℤ) = Nat.fib n + Nat.fib (n + 1) := hf
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, pow_succ, hf, hf'] <;> ring

end OMA.P_oeis_a319053

open OMA.S_oeis_a319053 OMA.P_oeis_a319053 in
theorem OMA.solution : type_of% @OMA.S_oeis_a319053.main := by
  intro n hn h3
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd := odd_fib (m + 1) h3
  have hall : ∀ ij : Fin 2 × Fin 2, padicValInt 2 ((M ^ (m + 1)) ij.1 ij.2) = m := by
    rintro ⟨i, j⟩
    rw [pow_form]
    fin_cases i <;> fin_cases j <;>
      first
      | exact v2 m _ (by omega)
      | (simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Fin.zero_eta, Fin.mk_one, Fin.isValue]
         exact v2 m _ (by omega))
  show Finset.univ.sup (fun ij : Fin 2 × Fin 2 => padicValInt 2 ((M ^ (m + 1)) ij.1 ij.2)) =
    m + 1 - 1
  rw [show (fun ij : Fin 2 × Fin 2 => padicValInt 2 ((M ^ (m + 1)) ij.1 ij.2)) = fun _ => m
    from funext hall, Finset.sup_const Finset.univ_nonempty]
  omega
