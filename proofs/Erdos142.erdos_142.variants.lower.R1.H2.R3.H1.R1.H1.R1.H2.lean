import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R1
-- Credit: @LAPRAI
-- Varnavides averaging: average |A ∩ {x + j e : 1 ≤ j ≤ M}| over pairs (x, e) with e ≠ 0; a pair
-- with more than α M / 2 hits gives a progression of A, and each progression comes from at most
-- M^2 pairs (recover e = d / t and x = a - j e).

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1.H2 := by
  classical
  intro k M p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  show 2 ≤ k → 2 ≤ M → M < p → ∀ (α : ℝ) (A : Finset (ZMod p)), _
  intro hk hM hMp α A hα hA hS
  set Pairs : Finset (ZMod p × ZMod p) :=
    (Finset.univ : Finset (ZMod p)) ×ˢ (Finset.univ.erase 0) with hPairs
  set T : ZMod p × ZMod p → Finset ℕ := fun u =>
    (Finset.Icc 1 M).filter (fun j => u.1 + (j : ZMod p) * u.2 ∈ A) with hT
  set Good := Pairs.filter (fun u => (α / 2) * (M : ℝ) < ((T u).card : ℝ)) with hGood
  set APs := (Finset.univ.filter fun u : ZMod p × ZMod p =>
    u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) with hAPs
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hcardPairs : Pairs.card = p * (p - 1) := by
    rw [hPairs, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  have hTle : ∀ u, (T u).card ≤ M := fun u =>
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  -- total number of hits
  have htrans : ∀ c : ZMod p, ∑ x : ZMod p, (if x + c ∈ A then 1 else 0 : ℕ) = A.card := by
    intro c
    rw [Fintype.sum_equiv (Equiv.addRight c) (fun x => if x + c ∈ A then 1 else 0)
      (fun y => if y ∈ A then 1 else 0) (fun x => rfl)]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
  have hinner : ∀ e : ZMod p, ∑ x : ZMod p, ∑ j ∈ Finset.Icc 1 M,
      (if x + (j : ZMod p) * e ∈ A then 1 else 0 : ℕ) = M * A.card := by
    intro e
    rw [Finset.sum_comm]
    simp only [htrans, Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  have hsum : ∑ u ∈ Pairs, (T u).card = (p - 1) * (M * A.card) := by
    rw [hPairs, Finset.sum_product]
    simp only [hT, Finset.card_filter]
    rw [Finset.sum_comm]
    simp only [hinner, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, smul_eq_mul]
  -- upper bound by the good pairs
  have hup : (∑ u ∈ Pairs, ((T u).card : ℝ)) ≤
      (Good.card : ℝ) * M + (Pairs.card : ℝ) * ((α / 2) * M) := by
    have h0 : 0 ≤ (α / 2) * (M : ℝ) := by positivity
    have hpt : ∀ u ∈ Pairs, ((T u).card : ℝ) ≤
        (if (α / 2) * (M : ℝ) < ((T u).card : ℝ) then (M : ℝ) else 0) + (α / 2) * M := by
      intro u _
      split_ifs with h
      · have : ((T u).card : ℝ) ≤ M := by exact_mod_cast hTle u
        linarith
      · push_neg at h
        linarith
    calc (∑ u ∈ Pairs, ((T u).card : ℝ))
        ≤ ∑ u ∈ Pairs, ((if (α / 2) * (M : ℝ) < ((T u).card : ℝ) then (M : ℝ) else 0) +
            (α / 2) * M) := Finset.sum_le_sum hpt
      _ = (Good.card : ℝ) * M + (Pairs.card : ℝ) * ((α / 2) * M) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
  have hsumR : (∑ u ∈ Pairs, ((T u).card : ℝ)) = ((p : ℝ) - 1) * (M * A.card) := by
    rw [← Nat.cast_sum, hsum]
    push_cast [Nat.cast_sub hp1]
    ring
  have hgood : (α / 2) * p * ((p : ℝ) - 1) ≤ Good.card := by
    have hpc : (Pairs.card : ℝ) = p * ((p : ℝ) - 1) := by
      rw [hcardPairs]
      push_cast [Nat.cast_sub hp1]
      ring
    have hp1' : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      linarith
    have key : (M : ℝ) * ((α / 2) * p * ((p : ℝ) - 1)) ≤ (M : ℝ) * (Good.card : ℝ) := by
      have h1 := hup
      rw [hsumR, hpc] at h1
      have h2 : ((p : ℝ) - 1) * (M * (α * p)) ≤ ((p : ℝ) - 1) * (M * A.card) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hMpos.le) hp1'
      nlinarith
    exact le_of_mul_le_mul_left key hMpos
  -- each good pair yields a progression of A
  have hS' : ∀ u : ZMod p × ZMod p, (α / 2) * (M : ℝ) < ((T u).card : ℝ) →
      ∃ jt : ℕ × ℕ, 0 < jt.2 ∧ ∀ i < k, jt.1 + i * jt.2 ∈ T u := by
    intro u h
    obtain ⟨a, d, hd, h'⟩ := hS (T u) (Finset.filter_subset _ _) h
    exact ⟨(a, d), hd, h'⟩
  choose! JT hJT using hS'
  have hprops : ∀ u ∈ Good, 1 ≤ (JT u).1 ∧ (JT u).1 ≤ M ∧ 1 ≤ (JT u).2 ∧ (JT u).2 ≤ M ∧
      ∀ i < k, u.1 + (((JT u).1 + i * (JT u).2 : ℕ) : ZMod p) * u.2 ∈ A := by
    intro u hu
    have hg := (Finset.mem_filter.mp hu).2
    obtain ⟨ht, hmem⟩ := hJT u hg
    have h0 := Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (by omega))).1
    have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 1 (by omega))).1
    simp only [zero_mul, add_zero, one_mul] at h0 h1
    exact ⟨h0.1, h0.2, ht, by omega, fun i hi => (Finset.mem_filter.mp (hmem i hi)).2⟩
  have htnz : ∀ u ∈ Good, ((JT u).2 : ZMod p) ≠ 0 := by
    intro u hu h
    obtain ⟨_, _, h3, h4, _⟩ := hprops u hu
    have := (CharP.cast_eq_zero_iff (ZMod p) p _).mp h
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hene : ∀ u ∈ Good, u.2 ≠ 0 := by
    intro u hu
    have := (Finset.mem_filter.mp hu).1
    rw [hPairs, Finset.mem_product, Finset.mem_erase] at this
    exact this.2.1
  set ψ : ZMod p × ZMod p → (ZMod p × ZMod p) × (ℕ × ℕ) := fun u =>
    ((u.1 + ((JT u).1 : ZMod p) * u.2, ((JT u).2 : ZMod p) * u.2), JT u) with hψ
  have hmaps : ∀ u ∈ Good, ψ u ∈ APs ×ˢ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M) := by
    intro u hu
    obtain ⟨a1, a2, a3, a4, a5⟩ := hprops u hu
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨a1, a2⟩, Finset.mem_Icc.mpr ⟨a3, a4⟩⟩⟩
    rw [hAPs]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, mul_ne_zero (htnz u hu) (hene u hu),
      fun i => ?_⟩
    have e : u.1 + ((JT u).1 : ZMod p) * u.2 + (i.val : ZMod p) * (((JT u).2 : ZMod p) * u.2) =
        u.1 + (((JT u).1 + i.val * (JT u).2 : ℕ) : ZMod p) * u.2 := by
      push_cast; ring
    show u.1 + ((JT u).1 : ZMod p) * u.2 + (i.val : ZMod p) * (((JT u).2 : ZMod p) * u.2) ∈ A
    rw [e]
    exact a5 i.val i.isLt
  have hinj : Set.InjOn ψ Good := by
    intro u hu v hv huv
    simp only [hψ, Prod.mk.injEq] at huv
    obtain ⟨⟨h1, h2⟩, h3⟩ := huv
    rw [h3] at h1 h2
    have he : u.2 = v.2 := mul_left_cancel₀ (htnz v hv) h2
    have hx : u.1 = v.1 := by
      rw [he] at h1
      exact add_right_cancel h1
    exact Prod.ext hx he
  have hcardG := Finset.card_le_card_of_injOn ψ hmaps hinj
  rw [Finset.card_product, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel] at hcardG
  calc (α / 2) * (p : ℝ) * ((p : ℝ) - 1) ≤ (Good.card : ℝ) := hgood
    _ ≤ (APs.card : ℝ) * (M * M) := by exact_mod_cast hcardG
    _ = (M : ℝ) ^ 2 * (APs.card : ℝ) := by ring

