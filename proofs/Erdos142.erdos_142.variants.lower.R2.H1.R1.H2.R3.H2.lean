import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R3
-- Credit: @LAPRAI
-- Cauchy condensation (summable_condensed_iff_of_nonneg) and comparison with 1/(m+1)^2.

open Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.H2 := by
  intro f hf0 hmono hev
  rw [← summable_condensed_iff_of_nonneg hf0 (fun m n _ hmn => hmono hmn)]
  have hg : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [hev] with m hm
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hf0 _))]
  exact hm

