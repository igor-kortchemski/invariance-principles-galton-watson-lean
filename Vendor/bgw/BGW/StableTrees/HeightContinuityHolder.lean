/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightContinuityKolmogorov
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber

/-!
# Hölder regularity on all bounded horizons

For each exponent below the stable height exponent, choose a sufficiently high moment.
Horizon modifications agree with the common continuous reconstruction by indistinguishability.
A countable intersection then covers every real horizon.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Almost surely the continuous height is locally `γ`-Hölder for every `γ < 1 - 1/θ`. -/
theorem ae_heightLoc_locallyHolder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : γ < 1 - 1 / θ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0, ∃ C : ℝ, ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
      |heightLoc θ f s - heightLoc θ f t| ≤ C * |(s : ℝ) - t| ^ γ := by
  let β : ℝ := 1 - 1 / θ
  have hgap : 0 < β - γ := sub_pos.mpr hγ
  have hβ1 : β ≤ 1 := by
    dsimp only [β]
    have hθpos : 0 < θ := lt_trans zero_lt_one hθ.1
    linarith only [one_div_pos.mpr hθpos]
  let p : ℝ := 2 / (β - γ)
  have hp : 1 ≤ p := (le_div_iff₀ hgap).mpr (by linarith only [hβ1, hγ0])
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have he : p * (β - γ) = 2 := div_mul_cancel₀ 2 hgap.ne'
  have hq : 1 < p * (1 - 1 / θ) := by
    change 1 < p * β
    nlinarith only [he, hp0, hγ0]
  have hγlt : γ < (p * (1 - 1 / θ) - 1) / p := by
    apply (lt_div_iff₀ hp0).mpr
    change γ * p < p * β - 1
    nlinarith only [he]
  obtain ⟨M, hX⟩ := exists_height_isKolmogorovProcess hθ hp
  let U (n : ℕ) : Set ℝ≥0 := Ico 0 (n + 1)
  have hmod (n : ℕ) := exists_modification_holder
    (isCoverWithBoundedCoveringNumber_Ico_nnreal.hasBoundedCoveringNumber n)
    (isCoverWithBoundedCoveringNumber_Ico_nnreal.isOpen n)
    hX.IsAEKolmogorovProcess (by finiteness) zero_lt_one hq
  choose Y _ hYeq hYholder using hmod
  let r : ℝ≥0 := ⟨γ, hγ0.le⟩
  have hr : 0 < r := hγ0
  have hYcont (n : ℕ) (f : DLoc) : ContinuousOn (fun t => Y n t f) (U n) :=
    ((hYholder n r hr hγlt f).choose_spec).continuousOn hr
  have hae (n : ℕ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ t ∈ U n, heightLoc θ f t = Y n t f := by
    have hh := indistinguishable_of_edist_modification_on
      (P := (stableLocalLaw θ : Measure DLoc))
      (isCoverWithBoundedCoveringNumber_Ico_nnreal.isOpen n)
      (ae_of_all _ fun f => (continuous_heightLoc θ f).continuousOn)
      (ae_of_all _ (hYcont n)) (fun t ht => ?_)
    · exact hh.mono fun _ hf t ht => edist_eq_zero.mp (hf t ht)
    · filter_upwards [ae_heightLoc_eq_height hθ t, hYeq n t ht] with f hf hg
      rw [hf, hg, edist_self]
  filter_upwards [ae_all_iff.mpr hae] with f hf
  intro T
  obtain ⟨n, hn⟩ := exists_nat_gt (T : ℝ)
  have hTn : T < (n : ℝ≥0) + 1 := by
    exact_mod_cast (lt_trans hn (lt_add_one (n : ℝ)))
  obtain ⟨C, hC⟩ := hYholder n r hr hγlt f
  refine ⟨C, ?_⟩
  intro s t hs ht
  have hsU : s ∈ U n := ⟨zero_le, hs.trans_lt hTn⟩
  have htU : t ∈ U n := ⟨zero_le, ht.trans_lt hTn⟩
  rw [hf n s hsU, hf n t htU]
  have hd := hC.dist_le hsU htU
  change |Y n s f - Y n t f| ≤ (C : ℝ) * |(s : ℝ) - t| ^ γ at hd
  exact hd

end BGW.StableTrees
