import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R1
-- Credit: @LAPRAI
-- A union of q progression-free pieces of [1, N] has at most q r_3(N) elements.
-- The bound card_le_maxCard is from reduction R2 of Erdős 142.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := by
  classical
  intro N q S B hS hB
  calc S.card ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hS
    _ ≤ ∑ i, (B i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, Erdos142.r 3 N := Finset.sum_le_sum fun i _ =>
        OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard (hB i).1 (hB i).2
    _ = q * Erdos142.r 3 N := by simp

