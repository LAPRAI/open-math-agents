import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R3.H1: hypothesis H1 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R3
-- Credit: @LAPRAI
-- Subadditivity of the extremal function (maxCard_add_le, from reduction R2 of Erdős 142) on four blocks.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H1 := by
  intro k _ N
  have h1 : Erdos142.r k (N + (N + (N + N))) ≤ Erdos142.r k N + Erdos142.r k (N + (N + N)) :=
    OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k _ _
  have h2 : Erdos142.r k (N + (N + N)) ≤ Erdos142.r k N + Erdos142.r k (N + N) :=
    OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k _ _
  have h3 : Erdos142.r k (N + N) ≤ Erdos142.r k N + Erdos142.r k N :=
    OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k _ _
  have e : 4 * N = N + (N + (N + N)) := by ring
  rw [e]
  omega

