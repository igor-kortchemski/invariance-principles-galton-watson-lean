/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightCancellation
public import BGW.StableTrees.ExcursionHeightCompensation
import BGW.StableTrees.StableExcursionSupport

/-!
# Occupation at a passage jump start

At a jump start the future infimum is the root level. Its small-depth occupation is confined
to the time between the passage of the preceding level and the left passage endpoint.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The pre-start approximation is bounded by a left passage difference quotient. -/
theorem heightApprox_passageTimeMinus_le (f : DLoc) (x : ℝ≥0)
    (hfin : ∀ y : ℝ≥0, firstPassageBelow y f = (passageTime y f : WithTop ℝ≥0))
    (hstart : f.1 (passageTimeMinus x f) = -(x : ℝ))
    (hgd : passageTimeMinus x f < passageTime x f)
    (hleft : ∀ y, passageTimeMinus y f ≤ passageTime y f)
    (hearlier : ∀ a b : ℝ≥0, a < b → passageTime a f ≤ passageTimeMinus b f)
    {ε : ℝ} (hε : 0 < ε) (hεx : ε < x) :
    0 ≤ heightApprox ε f (passageTimeMinus x f) ∧
      heightApprox ε f (passageTimeMinus x f) ≤
        ((passageTimeMinus x f : ℝ) - (passageTimeMinus (x - ε.toNNReal) f : ℝ)) / ε := by
  let g := passageTimeMinus x f
  let y := x - ε.toNNReal
  have hεle : ε.toNNReal ≤ x := Real.toNNReal_le_iff_le_coe.mpr hεx.le
  have hy : y < x := tsub_lt_self (hε.trans hεx) (Real.toNNReal_pos.mpr hε)
  have hTy : passageTime y f ≤ g := hearlier y x hy
  have hroot (v : ℝ≥0) (hv : v ≤ g) : -(x : ℝ) ≤ f.1 v := by
    apply le_eval_of_lt_strictPassageBelow
    change (v : WithTop ℝ≥0) < firstPassageBelow x f
    rw [hfin x]
    exact_mod_cast hv.trans_lt hgd
  have hinf (s : ℝ≥0) (hs : s ≤ g) : futureInf f g s = -(x : ℝ) := by
    apply le_antisymm
    · exact (futureInf_le_eval f g s g ⟨min_le_right _ _, le_rfl⟩).trans_eq hstart
    · let : Nonempty (Icc (min s g) g) := ⟨⟨g, min_le_right _ _, le_rfl⟩⟩
      exact le_ciInf fun v => hroot v v.2.2
  let A : Set ℝ := {s | 0 ≤ s ∧ s ≤ (g : ℝ) ∧
    f.1 s.toNNReal < futureInf f g s.toNNReal + ε}
  have hsub : A ⊆ Icc (passageTime y f : ℝ) (g : ℝ) := by
    intro s hs
    have hsg : s.toNNReal ≤ g := Real.toNNReal_le_iff_le_coe.mpr hs.2.1
    have hmargin := hs.2.2
    rw [hinf s.toNNReal hsg] at hmargin
    have hyval : (y : ℝ) = (x : ℝ) - ε := by
      rw [NNReal.coe_sub hεle, Real.coe_toNNReal _ hε.le]
    have hcross : f.1 s.toNNReal < -(y : ℝ) := by rw [hyval]; linarith only [hmargin]
    have hT := firstPassageBelow_le_of_eval_lt hcross
    rw [hfin y, WithTop.coe_le_coe] at hT
    refine ⟨?_, hs.2.1⟩
    have hTreal : (passageTime y f : ℝ) ≤ (s.toNNReal : ℝ) := hT
    rwa [Real.coe_toNNReal _ hs.1] at hTreal
  have hvol : (volume A).toReal ≤ (g : ℝ) - (passageTime y f : ℝ) := by
    have hv := ENNReal.toReal_mono
      (by simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true] :
        volume (Icc (passageTime y f : ℝ) (g : ℝ)) ≠ ⊤) (measure_mono hsub)
    rwa [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr (show
      (passageTime y f : ℝ) ≤ g from hTy))] at hv
  have hnorm : heightApprox ε f g = ε⁻¹ * (volume A).toReal := rfl
  rw [hnorm]
  refine ⟨mul_nonneg (inv_nonneg.mpr hε.le) ENNReal.toReal_nonneg, ?_⟩
  have hpre : (g : ℝ) - (passageTime y f : ℝ) ≤
      (g : ℝ) - (passageTimeMinus y f : ℝ) :=
    sub_le_sub_left (show (passageTimeMinus y f : ℝ) ≤ passageTime y f from hleft y) _
  calc
    _ ≤ ε⁻¹ * ((g : ℝ) - (passageTime y f : ℝ)) :=
      mul_le_mul_of_nonneg_left hvol (inv_nonneg.mpr hε.le)
    _ ≤ _ := by
      rw [div_eq_mul_inv, mul_comm _ ε⁻¹]
      exact mul_le_mul_of_nonneg_left hpre (inv_nonneg.mpr hε.le)

end BGW.StableTrees
