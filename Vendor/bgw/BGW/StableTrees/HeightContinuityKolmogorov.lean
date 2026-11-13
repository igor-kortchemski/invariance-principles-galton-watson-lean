/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightContinuityMoments
public import BGW.StableTrees.HeightContinuityMeasurable
public import Mathlib.Probability.Process.Kolmogorov
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber

/-!
# Kolmogorov regularity of stable heights

The moment estimate supplies the vendored Kolmogorov condition on nonnegative time.
A continuous modification agrees at every rational time on a common event, identifying
it with the deterministic universal-sequence reconstruction.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The increment moment estimate gives the Kolmogorov condition with dimension one. -/
theorem exists_height_isKolmogorovProcess {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ M : ℝ≥0, IsKolmogorovProcess (fun t f => height θ f t)
      (stableLocalLaw θ : Measure DLoc) p (p * (1 - 1 / θ)) M := by
  obtain ⟨C, hC, hbound⟩ := height_increment_moment_bound hθ hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hβ : 0 < 1 - 1 / θ := by
    have hθpos : 0 < θ := lt_trans zero_lt_one hθ.1
    exact sub_pos.mpr ((div_lt_one hθpos).mpr hθ.1)
  have hm := measurable_height_fixed θ
  refine ⟨C.toNNReal, ⟨fun s t => by
    rw [← BorelSpace.measurable_eq (α := ℝ × ℝ)]
    exact (hm s).prodMk (hm t), ?_, hp0, mul_pos hp0 hβ⟩⟩
  have hordered (s t : ℝ≥0) (hst : s ≤ t) :
      (∫⁻ f, edist (height θ f s) (height θ f t) ^ p
        ∂(stableLocalLaw θ : Measure DLoc)) ≤
          ENNReal.ofReal C * edist s t ^ (p * (1 - 1 / θ)) := by
    rcases eq_or_lt_of_le hst with rfl | hst'
    · simp [hp0]
    have hdiff : 0 < t - s := tsub_pos_iff_lt.mpr hst'
    obtain ⟨hi, hb⟩ := hbound s (t - s) hdiff
    rw [add_tsub_cancel_of_le hst] at hi hb
    have he (f : DLoc) : edist (height θ f s) (height θ f t) ^ p =
        ENNReal.ofReal (|height θ f t - height θ f s| ^ p) := by
      rw [edist_comm, edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
    simp_rw [he]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun f => Real.rpow_nonneg (abs_nonneg _) p)]
    have hd : edist s t = ENNReal.ofReal ((t : ℝ) - s) := by
      rw [edist_comm, edist_dist]
      change ENNReal.ofReal |(t : ℝ) - s| = _
      rw [abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))]
    have hts : 0 < (t : ℝ) - s := sub_pos.mpr hst'
    rw [hd, ENNReal.ofReal_rpow_of_pos hts]
    rw [← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    simpa only [NNReal.coe_sub hst] using hb
  intro s t
  change _ ≤ ENNReal.ofReal C * edist s t ^ (p * (1 - 1 / θ))
  rcases le_total s t with hst | hts
  · exact hordered s t hst
  · simpa only [edist_comm] using hordered t s hts

/-- A sufficiently high moment gives a continuous modification on nonnegative time. -/
theorem exists_height_continuous_modification {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ Y : ℝ≥0 → DLoc → ℝ, (∀ f, Continuous (fun t => Y t f)) ∧
      ∀ t, ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), Y t f = height θ f t := by
  let β : ℝ := 1 - 1 / θ
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ.1
  have hβ : 0 < β := sub_pos.mpr ((div_lt_one hθpos).mpr hθ.1)
  have hβ1 : β ≤ 1 := by
    dsimp only [β]
    linarith only [one_div_pos.mpr hθpos]
  let p : ℝ := 2 / β
  have hp : 1 ≤ p := (le_div_iff₀ hβ).mpr (by linarith only [hβ1])
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq : p * (1 - 1 / θ) = 2 := div_mul_cancel₀ 2 hβ.ne'
  obtain ⟨M, hX⟩ := exists_height_isKolmogorovProcess hθ hp
  obtain ⟨Y, _, hYeq, hYholder⟩ := exists_modification_holder'
    isCoverWithBoundedCoveringNumber_Ico_nnreal hX.IsAEKolmogorovProcess
    (fun n => by finiteness) zero_lt_one (by rw [hq]; norm_num)
  refine ⟨Y, ?_, hYeq⟩
  intro f
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨U, hU, hhold⟩ := hYholder f t
  let δ : ℝ≥0 := ⟨1 / (2 * p), by positivity⟩
  have hδ : 0 < δ := by
    change (0 : ℝ) < 1 / (2 * p)
    positivity
  have hδlt : (δ : ℝ) < (p * (1 - 1 / θ) - 1) / p := by
    rw [hq]
    change 1 / (2 * p) < (2 - 1) / p
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * p) hp0).mpr
    nlinarith only [hp0]
  obtain ⟨C, hC⟩ := hhold δ hδ hδlt
  exact (hC.continuousOn hδ).continuousAt hU

/-- A continuous modification is identified with rational reconstruction on one common event. -/
theorem ae_heightLoc_eq_modification {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (Y : ℝ≥0 → DLoc → ℝ) (hY : ∀ f, Continuous (fun t => Y t f))
    (hYeq : ∀ t, ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), Y t f = height θ f t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ t, heightLoc θ f t = Y t f) ∧
        ∀ t : ℝ≥0, IsRationalTime t → Y t f = heightUniv θ f t := by
  have hr : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ,
      Y (q : ℝ).toNNReal f = height θ f (q : ℝ).toNNReal :=
    ae_all_iff.mpr (fun q => hYeq _)
  filter_upwards [hr, ae_heightUniv_eq_height hθ] with f hf hu
  have hagree (t : ℝ≥0) (ht : IsRationalTime t) : Y t f = heightUniv θ f t := by
    obtain ⟨q, hqt⟩ := ht
    have hq : 0 ≤ q := by exact_mod_cast (hqt ▸ t.2 : 0 ≤ (q : ℝ))
    have he : (q : ℝ).toNNReal = t := by rw [hqt, Real.toNNReal_coe]
    simpa only [he] using (hf q).trans (hu q hq).symm
  exact ⟨fun t => congrFun (heightLoc_eq_of_rational_agreement θ f
    ⟨fun t => Y t f, hY f⟩ hagree) t, hagree⟩

/-- Almost surely the rational heights (read along `heightEps θ`) extend continuously. -/
theorem ae_exists_continuous_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0, IsRationalTime t → g t = heightUniv θ f t := by
  obtain ⟨Y, hY, hYeq⟩ := exists_height_continuous_modification hθ
  filter_upwards [ae_heightLoc_eq_modification hθ Y hY hYeq] with f hf
  exact ⟨⟨fun t => Y t f, hY f⟩, hf.2⟩

/-- **Modification**: for each fixed time, `heightLoc` agrees a.s. with H02's height. -/
theorem ae_heightLoc_eq_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), heightLoc θ f t = height θ f t := by
  obtain ⟨Y, hY, hYeq⟩ := exists_height_continuous_modification hθ
  filter_upwards [ae_heightLoc_eq_modification hθ Y hY hYeq, hYeq t] with f hf ht
  exact (hf.1 t).trans ht

end BGW.StableTrees
