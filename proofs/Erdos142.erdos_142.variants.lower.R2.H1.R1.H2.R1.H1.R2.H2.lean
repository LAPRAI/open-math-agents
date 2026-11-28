import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R2.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R2
-- Credit: @LAPRAI
-- Lift the progression: consecutive second differences vanish mod p and lie in (-p, p).

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.H2 := by
  classical
  intro k N p hk hNp S hS hex
  obtain ⟨a, d, hd, hall⟩ := hex
  haveI : NeZero p := ⟨by omega⟩
  have hSp : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.mp (hS hx)
  set x : ℕ → ℕ := fun i => (a + (i : ZMod p) * d).val with hxdef
  have hmem : ∀ i < k, x i ∈ S := by
    intro i hi
    obtain ⟨s, hs, hs'⟩ := Finset.mem_image.mp (hall i hi)
    have : x i = s := by
      simp only [hxdef]
      rw [← hs', ZMod.val_natCast, Nat.mod_eq_of_lt (by have := hSp s hs; omega)]
    exact this ▸ hs
  have hcast : ∀ i, ((x i : ℕ) : ZMod p) = a + (i : ZMod p) * d := fun i => by
    simp only [hxdef, ZMod.natCast_zmod_val]
  have hrec : ∀ i, i + 2 < k → x (i + 2) + x i = 2 * x (i + 1) := by
    intro i hi
    have h0 := hSp _ (hmem i (by omega))
    have h1 := hSp _ (hmem (i + 1) (by omega))
    have h2 := hSp _ (hmem (i + 2) (by omega))
    have hz : ((x (i + 2) + x i : ℕ) : ZMod p) = ((2 * x (i + 1) : ℕ) : ZMod p) := by
      push_cast [hcast]; ring
    have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hz
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hlin : ∀ i, i < k → (x i : ℤ) = x 0 + i * ((x 1 : ℤ) - x 0) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      match i, ih with
      | 0, _ => simp
      | 1, _ => simp
      | j + 2, ih =>
        have e := hrec j hi
        have e0 := ih j (by omega) (by omega)
        have e1 := ih (j + 1) (by omega) (by omega)
        have e' : (x (j + 2) : ℤ) = 2 * x (j + 1) - x j := by omega
        rw [e', e0, e1]; push_cast; ring
  rcases lt_trichotomy (x 0) (x 1) with h | h | h
  · refine ⟨x 0, x 1 - x 0, by omega, fun i hi => ?_⟩
    have := hlin i hi
    have e : x 0 + i * (x 1 - x 0) = x i := by
      zify [h.le]; linear_combination -this
    rw [e]; exact hmem i hi
  · exfalso; apply hd
    have := hcast 0; have h1 := hcast 1
    rw [h] at this; rw [this] at h1
    simpa using h1
  · refine ⟨x (k - 1), x 0 - x 1, by omega, fun i hi => ?_⟩
    have h1 := hlin (k - 1) (by omega)
    have h2 := hlin (k - 1 - i) (by omega)
    have e : x (k - 1) + i * (x 0 - x 1) = x (k - 1 - i) := by
      have hc1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have hc2 : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - i := by omega
      rw [hc1] at h1; rw [hc2] at h2
      zify [h.le]
      linear_combination h1 - h2
    rw [e]; exact hmem _ (by omega)

