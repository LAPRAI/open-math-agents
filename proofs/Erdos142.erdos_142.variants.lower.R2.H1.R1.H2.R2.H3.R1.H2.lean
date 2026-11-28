import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R1
-- Credit: @LAPRAI
-- Eventually c (log log 2^m)^(1+η) ≥ 2 log m, so the terms are at most m^(-2).

open Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1.H2 := by
  intro c η hc hη
  have hl2 := Real.log_two_gt_d9
  have hL : Tendsto (fun m : ℕ => Real.log ((2 : ℝ) ^ m)) atTop atTop := by
    simp_rw [Real.log_pow]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two)
  have hl : Tendsto (fun m : ℕ => Real.log (Real.log ((2 : ℝ) ^ m))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hp : Tendsto (fun m : ℕ => Real.log (Real.log ((2 : ℝ) ^ m)) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hl
  refine Summable.of_norm_bounded_eventually_nat (Real.summable_nat_pow_inv.mpr one_lt_two) ?_
  filter_upwards [hl.eventually_gt_atTop 0, hp.eventually_ge_atTop (4 / c),
    eventually_ge_atTop 3] with m hl0 hpw hm3
  have hm : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hlogpow : Real.log ((2 : ℝ) ^ m) = m * Real.log 2 := Real.log_pow m 2
  set ℓ := Real.log (Real.log ((2 : ℝ) ^ m)) with hℓ
  have hkey : 2 * Real.log m ≤ 4 * ℓ := by
    have hpos : 0 < (m : ℝ) * Real.log 2 := by positivity
    have hsq : (m : ℝ) ≤ ((m : ℝ) * Real.log 2) ^ 2 := by
      have hL2 : (0.47 : ℝ) < Real.log 2 ^ 2 := by nlinarith
      have hmL : 1 ≤ (m : ℝ) * Real.log 2 ^ 2 := by nlinarith
      calc (m : ℝ) = m * 1 := by ring
        _ ≤ m * (m * Real.log 2 ^ 2) := by gcongr
        _ = ((m : ℝ) * Real.log 2) ^ 2 := by ring
    have h1 : Real.log m ≤ Real.log (((m : ℝ) * Real.log 2) ^ 2) :=
      Real.log_le_log (by positivity) hsq
    rw [Real.log_pow] at h1
    rw [hℓ, hlogpow]
    push_cast at h1
    linarith
  have hbig : 4 * ℓ ≤ c * ℓ ^ (1 + η) := by
    rw [Real.rpow_add hl0, Real.rpow_one]
    have h4 : 4 ≤ c * ℓ ^ η := by rw [div_le_iff₀ hc] at hpw; linarith
    nlinarith
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hm0 : (0 : ℝ) < m := by linarith
  calc Real.exp (-c * ℓ ^ (1 + η)) ≤ Real.exp (-(2 * Real.log m)) :=
        Real.exp_le_exp.mpr (by linarith [neg_mul c (ℓ ^ (1 + η))])
    _ = ((m : ℝ) ^ 2)⁻¹ := by
        rw [Real.exp_neg, show 2 * Real.log m = Real.log ((m : ℝ) ^ 2) by
          rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]

