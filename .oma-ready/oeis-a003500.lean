import OMAStatements.S_oeis_a003500

namespace OMA.P_oeis_a003500

open OMA.S_oeis_a003500

lemma even_a : ∀ n : ℕ, 2 ∣ a n ∧ 2 ∣ a (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨⟨1, by norm_num [a]⟩, ⟨2, by norm_num [a]⟩⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show 2 ∣ 4 * a (n + 1) - a n
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := ih
    exact ⟨2 * y - x, by rw [hx, hy]; ring⟩

lemma mono_a : ∀ n : ℕ, 2 ≤ a n ∧ a n < a (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨le_rfl, by show (2 : ℤ) < 4; norm_num⟩
  | succ n ih =>
    refine ⟨by linarith [ih.1, ih.2], ?_⟩
    show a (n + 1) < 4 * a (n + 1) - a n
    linarith [ih.1, ih.2]

end OMA.P_oeis_a003500

open OMA.S_oeis_a003500 OMA.P_oeis_a003500 in
theorem OMA.solution : type_of% @OMA.S_oeis_a003500.main := by
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have h1 := mono_a q
  have h2 : 2 < a (q + 1) := by linarith [h1.1, h1.2]
  refine ⟨by linarith, fun hpr => ?_⟩
  obtain ⟨k, hk⟩ := (even_a (q + 1)).1
  rw [Int.prime_iff_natAbs_prime] at hpr
  have hdvd : 2 ∣ (a (q + 1)).natAbs := ⟨k.natAbs, by rw [hk, Int.natAbs_mul]; rfl⟩
  have h3 : 2 < (a (q + 1)).natAbs := by
    have := Int.natAbs_of_nonneg (by linarith : (0 : ℤ) ≤ a (q + 1))
    omega
  rcases hpr.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
