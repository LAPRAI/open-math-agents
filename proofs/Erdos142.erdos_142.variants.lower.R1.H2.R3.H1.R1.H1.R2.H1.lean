import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R2.H1: hypothesis H1 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R2
-- Credit: @LAPRAI
-- Turán / Caro–Wei by the greedy argument: remove a vertex of minimum degree δ together with its
-- neighbours; the integer identity X Z - (Y - n s)^2 = s^2 (X b - n'^2) closes the induction.

namespace OMA.CaroWei37670

lemma arith (n' δ D b : ℤ) (hδ : 0 ≤ δ) (hn' : 0 ≤ n') (hb : 0 ≤ b)
    (hD : δ * (n' + (δ + 1)) ≤ D) (hX0 : 0 ≤ n' + D - (δ + 1) * δ)
    (hX : n' ^ 2 ≤ (n' + D - (δ + 1) * δ) * b) :
    (n' + (δ + 1)) ^ 2 ≤ (n' + (δ + 1) + D) * (b + 1) := by
  rcases hX0.eq_or_lt with h0 | hpos
  · have hn0 : n' = 0 := le_antisymm (by nlinarith) hn'
    subst hn0
    have hY : (δ + 1) ^ 2 ≤ 0 + (δ + 1) + D := by nlinarith
    nlinarith [mul_nonneg hb (show (0 : ℤ) ≤ 0 + (δ + 1) + D by nlinarith)]
  · have key : (n' + D - (δ + 1) * δ) *
        ((δ + 1) ^ 2 * b + (n' + (δ + 1) + D) + (δ + 1) ^ 2 - 2 * (n' + (δ + 1)) * (δ + 1)) -
        ((n' + (δ + 1) + D) - (n' + (δ + 1)) * (δ + 1)) ^ 2 =
        (δ + 1) ^ 2 * ((n' + D - (δ + 1) * δ) * b - n' ^ 2) := by ring
    have hXZ : 0 ≤ (n' + D - (δ + 1) * δ) *
        ((δ + 1) ^ 2 * b + (n' + (δ + 1) + D) + (δ + 1) ^ 2 - 2 * (n' + (δ + 1)) * (δ + 1)) := by
      nlinarith [sq_nonneg ((n' + (δ + 1) + D) - (n' + (δ + 1)) * (δ + 1)),
        mul_nonneg (sq_nonneg (δ + 1)) (sub_nonneg.mpr hX)]
    have hZ : 0 ≤ (δ + 1) ^ 2 * b + (n' + (δ + 1) + D) + (δ + 1) ^ 2 -
        2 * (n' + (δ + 1)) * (δ + 1) := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_pos hpos (neg_pos.mpr hneg)]
    have e : (n' + (δ + 1) + D) * (b + 1) - (n' + (δ + 1)) ^ 2 =
        ((n' + D - (δ + 1) * δ) * b - n' ^ 2) +
        ((δ + 1) ^ 2 * b + (n' + (δ + 1) + D) + (δ + 1) ^ 2 - 2 * (n' + (δ + 1)) * (δ + 1)) := by
      ring
    nlinarith [e, hZ, hX]

/-- Caro–Wei / Turán for a symmetric irreflexive relation, with the degree sum. -/
lemma cw {V : Type*} [DecidableEq V] (R : V → V → Prop) [DecidableRel R]
    (hsymm : ∀ v w, R v w → R w v) (hirr : ∀ v, ¬ R v v) (A : Finset V) :
    ∃ B ⊆ A, (∀ v ∈ B, ∀ w ∈ B, ¬ R v w) ∧
      A.card ^ 2 ≤ (A.card + ∑ v ∈ A, (A.filter (R v)).card) * B.card := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    rcases A.eq_empty_or_nonempty with hA | hne
    · subst hA
      exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    obtain ⟨v, hvA, hmin⟩ := A.exists_min_image (fun u => (A.filter (R u)).card) hne
    have hvN : v ∉ A.filter (R v) := by simp [hirr]
    have hNA : insert v (A.filter (R v)) ⊆ A :=
      Finset.insert_subset hvA (Finset.filter_subset _ _)
    have hNcard : (insert v (A.filter (R v))).card = (A.filter (R v)).card + 1 :=
      Finset.card_insert_of_notMem hvN
    have hvnot : v ∉ A \ insert v (A.filter (R v)) := fun h =>
      (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
    have hsub : A \ insert v (A.filter (R v)) ⊂ A :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => hvnot (h ▸ hvA)⟩
    obtain ⟨B', hB'A', hB'ind, hB'⟩ := ih _ hsub
    have hvB' : v ∉ B' := fun h => hvnot (hB'A' h)
    refine ⟨insert v B', Finset.insert_subset hvA (hB'A'.trans Finset.sdiff_subset), ?_, ?_⟩
    · have hfar : ∀ w ∈ B', ¬ R v w := by
        intro w hw hR
        have hw' := Finset.mem_sdiff.mp (hB'A' hw)
        exact hw'.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hw'.1, hR⟩))
      intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact hirr _
      · exact hfar y hy
      · exact fun h => hfar x hx (hsymm _ _ h)
      · exact hB'ind x hx y hy
    · rw [Finset.card_insert_of_notMem hvB']
      set N := insert v (A.filter (R v)) with hN
      set A' := A \ N with hA'
      set δ := (A.filter (R v)).card with hδ
      set f : V → ℕ := fun u => (A.filter (R u)).card with hf
      have hn : A'.card + N.card = A.card := Finset.card_sdiff_add_card_eq_card hNA
      have hsplit : ∑ u ∈ A', f u + ∑ u ∈ N, f u = ∑ u ∈ A, f u := Finset.sum_sdiff hNA
      have hNf : N.card * δ ≤ ∑ u ∈ N, f u := by
        have := Finset.card_nsmul_le_sum N f δ (fun u hu => hmin u (hNA hu))
        simpa [smul_eq_mul] using this
      have hAf : A.card * δ ≤ ∑ u ∈ A, f u := by
        have := Finset.card_nsmul_le_sum A f δ (fun u hu => hmin u hu)
        simpa [smul_eq_mul] using this
      have hmono : ∑ u ∈ A', (A'.filter (R u)).card ≤ ∑ u ∈ A', f u :=
        Finset.sum_le_sum fun u _ =>
          Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
      set D := ∑ u ∈ A, f u with hD
      set D' := ∑ u ∈ A', (A'.filter (R u)).card with hD'
      have h1 : D' + (δ + 1) * δ ≤ D := by rw [hNcard] at hNf; linarith
      have hA : A.card = A'.card + (δ + 1) := by rw [hNcard] at hn; omega
      have hAf' : δ * (A'.card + (δ + 1)) ≤ D := by rw [← hA, mul_comm]; exact hAf
      have hIH : ((A'.card : ℤ)) ^ 2 ≤ ((A'.card : ℤ) + D') * B'.card := by exact_mod_cast hB'
      have h1' : (D' : ℤ) + (δ + 1) * δ ≤ D := by exact_mod_cast h1
      have hX : ((A'.card : ℤ)) ^ 2 ≤ ((A'.card : ℤ) + D - (δ + 1) * δ) * B'.card := by
        have hb0 : (0 : ℤ) ≤ B'.card := by positivity
        nlinarith [mul_le_mul_of_nonneg_right (show (A'.card : ℤ) + D' ≤
          (A'.card : ℤ) + D - (δ + 1) * δ by linarith) hb0]
      have hX0 : (0 : ℤ) ≤ (A'.card : ℤ) + D - (δ + 1) * δ := by
        have : (0 : ℤ) ≤ D' := by positivity
        linarith
      have hD'' : (δ : ℤ) * ((A'.card : ℤ) + (δ + 1)) ≤ D := by exact_mod_cast hAf'
      have := arith (A'.card : ℤ) δ D B'.card (by positivity) (by positivity) (by positivity)
        hD'' hX0 hX
      rw [hA]
      exact_mod_cast this

end OMA.CaroWei37670

open OMA.CaroWei37670 in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2.H1 := by
  classical
  intro V A E hE
  obtain ⟨B, hBA, hind, hcard⟩ := cw (fun v w => (v, w) ∈ E ∨ (w, v) ∈ E)
    (fun v w h => h.symm) (fun v h => by rcases h with h | h <;> exact hE _ h rfl) A
  refine ⟨B, hBA, ?_, fun e he h1 h2 => hind e.1 h1 e.2 h2 (Or.inl he)⟩
  have hconv : ∀ P : V × V → Prop, ∀ [DecidablePred P],
      ∑ v ∈ A, (A.filter (fun w => P (v, w))).card = ((A ×ˢ A).filter P).card := by
    intro P _
    rw [Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  have hE1 : ((A ×ˢ A).filter (fun q => q ∈ E)).card ≤ E.card :=
    Finset.card_le_card fun q hq => (Finset.mem_filter.mp hq).2
  have hcomm : ∑ v ∈ A, (A.filter (fun w => (w, v) ∈ E)).card =
      ∑ v ∈ A, (A.filter (fun w => (v, w) ∈ E)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hdeg : ∑ v ∈ A, (A.filter (fun w => (v, w) ∈ E ∨ (w, v) ∈ E)).card ≤ 2 * E.card := by
    calc ∑ v ∈ A, (A.filter (fun w => (v, w) ∈ E ∨ (w, v) ∈ E)).card
        ≤ ∑ v ∈ A, ((A.filter (fun w => (v, w) ∈ E)).card +
            (A.filter (fun w => (w, v) ∈ E)).card) := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [Finset.filter_or]
          exact Finset.card_union_le _ _
      _ = 2 * ∑ v ∈ A, (A.filter (fun w => (v, w) ∈ E)).card := by
          rw [Finset.sum_add_distrib, hcomm]; ring
      _ ≤ 2 * E.card := by
          have this : ∑ v ∈ A, (A.filter (fun w => (v, w) ∈ E)).card =
              ((A ×ˢ A).filter (fun q => q ∈ E)).card := hconv (fun q => q ∈ E)
          rw [this]
          exact Nat.mul_le_mul_left 2 hE1
  calc A.card ^ 2
      ≤ (A.card + ∑ v ∈ A, (A.filter (fun w => (v, w) ∈ E ∨ (w, v) ∈ E)).card) * B.card := hcard
    _ ≤ (A.card + 2 * E.card) * B.card := Nat.mul_le_mul_right _ (Nat.add_le_add_left hdeg _)

