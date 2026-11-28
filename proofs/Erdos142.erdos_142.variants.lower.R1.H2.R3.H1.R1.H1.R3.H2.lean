import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R3
-- Credit: @LAPRAI
-- Caro–Wei on the graph joining the two ends of each nonconstant k-progression of A: an
-- independent set is progression-free, and the degree sum plus |A| is at most the count.

namespace OMA.CaroWei37679

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

end OMA.CaroWei37679

namespace OMA.CaroWei37679

/-- `v ~ w` when `v ≠ w` are the two ends of a nonconstant `k`-progression of `A`. -/
abbrev Rel (p k : ℕ) (A : Finset (ZMod p)) (v w : ZMod p) : Prop :=
  v ≠ w ∧ ∃ d : ZMod p, d ≠ 0 ∧ (∀ i : Fin k, v + (i.val : ZMod p) * d ∈ A) ∧
    w = v + ((k - 1 : ℕ) : ZMod p) * d

end OMA.CaroWei37679

open OMA.CaroWei37679 in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3.H2 := by
  classical
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  show ∀ k : ℕ, 2 ≤ k → ∀ A : Finset (ZMod p), _
  intro k hk A
  by_cases hAu : A = Finset.univ
  · subst hAu
    refine ⟨{0}, Finset.subset_univ _, ?_, ?_⟩
    · intro a d h
      have h0 : a + ((0 : ℕ) : ZMod p) * d ∈ ({0} : Finset (ZMod p)) := h ⟨0, by omega⟩
      have h1 : a + ((1 : ℕ) : ZMod p) * d ∈ ({0} : Finset (ZMod p)) := h ⟨1, by omega⟩
      simp only [Finset.mem_singleton, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
        add_zero] at h0 h1
      rw [h0, zero_add] at h1
      exact h1
    · simp [sq]
  -- a progression with (k - 1) d = 0 and d ≠ 0 covers ZMod p
  have hcover : ∀ a d : ZMod p, d ≠ 0 → ((k - 1 : ℕ) : ZMod p) * d = 0 →
      (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ A) → False := by
    intro a d hd h0 hall
    have hc : ((k - 1 : ℕ) : ZMod p) = 0 := (mul_eq_zero.mp h0).resolve_right hd
    have hdvd : p ∣ k - 1 := (CharP.cast_eq_zero_iff (ZMod p) p (k - 1)).mp hc
    have hpk : p ≤ k - 1 := Nat.le_of_dvd (by omega) hdvd
    apply hAu
    apply Finset.eq_univ_of_forall
    intro y
    have hlt := ZMod.val_lt ((y - a) / d)
    have e : a + ((((y - a) / d).val : ℕ) : ZMod p) * d = y := by
      rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hd]; ring
    have h' : a + ((((y - a) / d).val : ℕ) : ZMod p) * d ∈ A :=
      hall ⟨((y - a) / d).val, by omega⟩
    rwa [e] at h'
  have hsymm : ∀ v w, Rel p k A v w → Rel p k A w v := by
    rintro v w ⟨hvw, d, hd, hall, rfl⟩
    refine ⟨Ne.symm hvw, -d, neg_ne_zero.mpr hd, fun i => ?_, by ring⟩
    have hi := i.isLt
    have h' : v + ((k - 1 - i.val : ℕ) : ZMod p) * d ∈ A := hall ⟨k - 1 - i.val, by omega⟩
    have hc : ((k - 1 - i.val : ℕ) : ZMod p) = ((k - 1 : ℕ) : ZMod p) - (i.val : ZMod p) :=
      Nat.cast_sub (by omega)
    rw [hc] at h'
    convert h' using 1
    ring
  have hirr : ∀ v, ¬ Rel p k A v v := fun v h => h.1 rfl
  obtain ⟨B, hBA, hind, hcard⟩ := cw (Rel p k A) hsymm hirr A
  refine ⟨B, hBA, ?_, ?_⟩
  · intro a d hall
    by_contra hd
    have hB0 : a ∈ B := by simpa using hall ⟨0, by omega⟩
    have hBk : a + ((k - 1 : ℕ) : ZMod p) * d ∈ B := hall ⟨k - 1, by omega⟩
    by_cases hvw : a = a + ((k - 1 : ℕ) : ZMod p) * d
    · exact hcover a d hd (by linear_combination -hvw) fun i => hBA (hall i)
    · exact hind a hB0 _ hBk ⟨hvw, d, hd, fun i => hBA (hall i), rfl⟩
  set T := (Finset.univ.filter fun u : ZMod p × ZMod p =>
    ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) with hT
  set P := (A ×ˢ A).filter (fun q : ZMod p × ZMod p => Rel p k A q.1 q.2) with hP
  have hD : ∑ v ∈ A, (A.filter (Rel p k A v)).card = P.card := by
    rw [hP, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact Finset.card_filter _ _
  have hsplit : (T.filter (fun u => u.2 = 0)).card + (T.filter (fun u => ¬ u.2 = 0)).card =
      T.card := Finset.card_filter_add_card_filter_not _
  have hpart0 : A.card ≤ (T.filter (fun u => u.2 = 0)).card := by
    refine Finset.card_le_card_of_injOn (fun a => (a, (0 : ZMod p))) ?_ ?_
    · intro a ha
      have ha' : a ∈ A := by simpa using ha
      simp [hT, ha']
    · intro a _ b _ h
      exact congrArg Prod.fst h
  have hex : ∀ q : ZMod p × ZMod p, Rel p k A q.1 q.2 → ∃ d : ZMod p, d ≠ 0 ∧
      (∀ i : Fin k, q.1 + (i.val : ZMod p) * d ∈ A) ∧ q.2 = q.1 + ((k - 1 : ℕ) : ZMod p) * d := by
    intro q h
    obtain ⟨_, h2⟩ := h
    exact h2
  choose! dd hdd using hex
  have hRP : ∀ q, q ∈ (P : Set (ZMod p × ZMod p)) → Rel p k A q.1 q.2 := by
    intro q hq
    have hq' : q ∈ P := by simpa using hq
    rw [hP, Finset.mem_filter] at hq'
    exact hq'.2
  have hpart1 : P.card ≤ (T.filter (fun u => ¬ u.2 = 0)).card := by
    refine Finset.card_le_card_of_injOn (fun q => (q.1, dd q)) ?_ ?_
    · intro q hq
      obtain ⟨h1, h2, _⟩ := hdd q (hRP q hq)
      have hmem : (q.1, dd q) ∈ T := by
        rw [hT, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h2⟩
      have : (q.1, dd q) ∈ T.filter (fun u => ¬ u.2 = 0) := Finset.mem_filter.mpr ⟨hmem, h1⟩
      simpa using this
    · intro q hq q' hq' h
      have h1 : q.1 = q'.1 := congrArg Prod.fst h
      have h2 : dd q = dd q' := congrArg Prod.snd h
      have e := (hdd q (hRP q hq)).2.2
      have e' := (hdd q' (hRP q' hq')).2.2
      refine Prod.ext h1 ?_
      rw [e, e', h1, h2]
  calc A.card ^ 2 ≤ (A.card + ∑ v ∈ A, (A.filter (Rel p k A v)).card) * B.card := hcard
    _ ≤ T.card * B.card := Nat.mul_le_mul_right _ (by rw [hD]; omega)
    _ = B.card * T.card := Nat.mul_comm _ _

