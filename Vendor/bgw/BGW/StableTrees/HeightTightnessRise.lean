/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessCount
public import BGW.StableTrees.HeightTightnessInterpolation

/-!
# One-sided rise control from discrete regeneration

Integer forest heights increase by at most one in a step. A first crossing
therefore reaches its level without overshooting. The shifted-height identity
bounds every upward variation within a regenerated gap. A bounded number of
crossings and long gaps then give simultaneous one-sided control at all integer
times in the horizon, with an exceptional event of arbitrarily small probability
on a sufficiently short time scale, uniformly for all large scaling indices.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- The forest height can increase by at most one in a single discrete step. -/
theorem forestHeight_succ_le (ω : ℕ → ℕ) (k : ℕ) :
    forestHeight ω (k + 1) ≤ forestHeight ω k + 1 := by
  let S (r : ℕ) := (Finset.range r).filter
    (fun j => ∀ l, j ≤ l → l ≤ r → walk ω j ≤ walk ω l)
  have hs : S (k + 1) ⊆ insert k (S k) := by
    intro j hj
    obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    by_cases he : j = k
    · exact Finset.mem_insert.mpr (Or.inl he)
    · apply Finset.mem_insert.mpr
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        fun l hjl hlk => hr l hjl (by omega)⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- The shifted height controls every upward variation after the shift time. -/
theorem forestHeight_rise_le_shifted (ω : ℕ → ℕ) {a s t : ℕ} (has : a ≤ s)
    (hst : s ≤ t) :
    forestHeight ω t ≤ forestHeight ω s + forestHeight (shiftSeq a ω) (t - a) := by
  have hm : minHeight ω a (t - a) ≤ forestHeight ω s := by
    have he := Finset.inf'_le (fun i => forestHeight ω (a + i))
      (show s - a ∈ Finset.range (t - a + 1) by simp only [Finset.mem_range]; omega)
    simpa only [minHeight, Nat.add_sub_of_le has] using he
  have he := shiftedHeight_eq ω a (t - a)
  simp only [shiftedHeight, Nat.add_sub_of_le (has.trans hst)] at he
  omega

/-- Heights up to and including a first crossing are at most the crossing level. -/
theorem forestHeight_le_of_le_first_crossing {ω : ℕ → ℕ} {q K k : ℕ}
    (hK : heightUpcrossingStop q ω = K) (hk : k ≤ K) : forestHeight ω k ≤ q := by
  obtain ⟨_, hpre⟩ := (heightUpcrossingStop_eq_natCast_iff q K ω).mp hK
  by_cases hlt : k < K
  · exact (hpre k hlt).le
  · have he : k = K := by omega
    subst K
    cases k with
    | zero => simp [forestHeight]
    | succ k =>
      have hp := hpre k (by omega)
      have hs := forestHeight_succ_le ω k
      omega

/-- Within one regenerated gap, every upward variation is at most its crossing level. -/
theorem forestHeight_rise_le_in_regeneration_gap {ω : ℕ → ℕ} {q j a b s t : ℕ}
    (ha : heightRegenerationStop q j ω = a)
    (hb : heightRegenerationStop q (j + 1) ω = b)
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    forestHeight ω t ≤ forestHeight ω s + q := by
  have he : (a : ℕ∞) + heightUpcrossingStop q (shiftSeq a ω) = b := by
    simpa only [heightRegenerationStop, nextHeightUpcrossing, ha, ENat.toNat_natCast] using hb
  have hfin : heightUpcrossingStop q (shiftSeq a ω) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at he
    exact ENat.top_ne_natCast b he
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp hfin
  have hab : a + K = b := by
    rw [← hK, ← Nat.cast_add] at he
    exact ENat.natCast_inj.mp he
  have hr := forestHeight_rise_le_shifted ω has hst
  have hl := forestHeight_le_of_le_first_crossing hK.symm (show t - a ≤ K by omega)
  omega

/-- Long gaps up to a finite crossing beyond the horizon control all short rises of the height. -/
theorem forestHeight_short_rise_le_of_gap_bounds {ω : ℕ → ℕ} {q L M d : ℕ}
    (hfin : heightRegenerationStop q L ω ≠ ⊤)
    (hL : M < (heightRegenerationStop q L ω).toNat)
    (hgaps : ∀ j < L, d < heightRegenerationGap q j ω)
    {s t : ℕ} (hst : s ≤ t) (ht : t ≤ M) (hd : t - s ≤ d) :
    forestHeight ω t ≤ forestHeight ω s + 2 * q := by
  let r : ℕ → ℕ := fun j => (heightRegenerationStop q j ω).toNat
  have hfinite (j : ℕ) (hj : j ≤ L) : heightRegenerationStop q j ω ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (monotone_heightRegenerationStop q ω hj)
  apply short_rise_le_of_long_gaps (r := r) (by simp [r, heightRegenerationStop]) hL
    hgaps ?_ hst ht hd
  intro j hj u hju v huv hvnext
  exact forestHeight_rise_le_in_regeneration_gap
    (ENat.natCast_toNat (hfinite j hj.le)).symm
    (ENat.natCast_toNat (hfinite (j + 1) (by omega))).symm hju huv hvnext

/-- Uniform eventual control of all short upward variations on an integer horizon. -/
theorem exists_pos_eventually_short_rise_probability_small {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {η T ε : ℝ}
    (hη : 0 < η) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ x : ℝ, 0 < x ∧ ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure.real {ω | ∃ s t : ℕ,
        s ≤ t ∧ t ≤ ⌊(n : ℝ) * T⌋₊ ∧ t - s ≤ ⌊(n : ℝ) * x⌋₊ ∧
          forestHeight ω s + 2 * ⌊η * (n : ℝ) / B n⌋₊ < forestHeight ω t} ≤ ε := by
  obtain ⟨L, hcount⟩ := exists_eventually_heightRegenerationStop_probability_small h hη hT
    (show 0 < ε / 2 by positivity)
  obtain ⟨x, hx, hshort⟩ := exists_pos_eventually_short_gap_probability_small h hη
    (show 0 < ε / 2 by positivity) L
  refine ⟨x, hx, ?_⟩
  filter_upwards [hcount, hshort] with n hnC hnS
  let q := ⌊η * (n : ℝ) / B n⌋₊
  let M := ⌊(n : ℝ) * T⌋₊
  let d := ⌊(n : ℝ) * x⌋₊
  let C : Set (ℕ → ℕ) := {ω | heightRegenerationStop q L ω ≤ (M : ℕ∞)}
  let S : Set (ℕ → ℕ) := {ω | ∃ j < L, heightRegenerationGap q j ω ≤ d}
  have hsub : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
      ω ∈ {ω | ∃ s t : ℕ, s ≤ t ∧ t ≤ M ∧ t - s ≤ d ∧
        forestHeight ω s + 2 * q < forestHeight ω t} → ω ∈ C ∪ S := by
    filter_upwards [ae_heightRegenerationStop_ne_top μ h.critical h.nondegenerate q L]
      with ω hfin hh
    by_cases hC : ω ∈ C
    · exact Or.inl hC
    by_cases hS : ω ∈ S
    · exact Or.inr hS
    obtain ⟨s, t, hst, ht, hd, hheight⟩ := hh
    have hL : M < (heightRegenerationStop q L ω).toNat := by
      change ¬heightRegenerationStop q L ω ≤ (M : ℕ∞) at hC
      rw [← ENat.natCast_toNat hfin] at hC
      exact ENat.natCast_lt_natCast.mp (lt_of_not_ge hC)
    have hgaps (j : ℕ) (hj : j < L) : d < heightRegenerationGap q j ω := by
      by_contra hn
      exact hS ⟨j, hj, by omega⟩
    have hb := forestHeight_short_rise_le_of_gap_bounds hfin hL hgaps hst ht hd
    omega
  have hb := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact hb.trans ((measureReal_union_le C S).trans (by linarith))

end BGW.StableTrees.HeightTightness
