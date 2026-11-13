/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.StableBridgeClosed
public import BGW.StableTrees.StableProcessBrownian
public import BGW.StableTrees.BridgePrefix
public import BGW.ContinuumTrees.BrownianD

/-! # The Gaussian stable bridge

At stability index `θ = 2`, the spectrally positive stable density is the centered Gaussian
density of variance `2`.  Its transition densities and bridge prefix weights therefore agree
with those of `√2` times standard Brownian motion.  Uniqueness of the bridge with prescribed
prefix laws and pinned endpoints identifies the stable bridge with `√2` times the Brownian
bridge.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace BGW.StableTrees.BrownianIdentification

open BGW.Skorokhod

/-- The `θ = 2` stable density is the centered Gaussian density of variance `2`. -/
theorem stableDensity_two (x : ℝ) : Scalar.stableDensity 2 x = gaussianPDFReal 0 2 x := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  have hμ : volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity 2 x)) =
      volume.withDensity (gaussianPDF 0 2) := by
    rw [← stableLaw_eq_withDensity hθ, stableLaw_two,
      gaussianReal_of_var_ne_zero 0 (by norm_num)]
  have haeENN : (fun x => ENNReal.ofReal (Scalar.stableDensity 2 x)) =ᵐ[volume]
      gaussianPDF 0 2 :=
    (withDensity_eq_iff_of_sigmaFinite
      (Scalar.continuous_stableDensity hθ).measurable.ennreal_ofReal.aemeasurable
      (measurable_gaussianPDF 0 2).aemeasurable).mp hμ
  have hae : Scalar.stableDensity 2 =ᵐ[volume] gaussianPDFReal 0 2 := by
    filter_upwards [haeENN] with y hy
    exact (ENNReal.ofReal_eq_ofReal_iff (stableDensity_nonneg hθ y)
      (gaussianPDFReal_nonneg 0 2 y)).mp hy
  have hd : Continuous (Scalar.stableDensity 2) := Scalar.continuous_stableDensity hθ
  have hg : Continuous (gaussianPDFReal 0 2) := by
    unfold gaussianPDFReal
    fun_prop
  exact congrFun ((hd.ae_eq_iff_eq volume hg).mp hae) x


/-- At time `t > 0`, the `θ = 2` stable density is the density of `√2 B_t`. -/
theorem stableDensityAt_two {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stableDensityAt 2 t x =
      gaussianPDFReal 0 (BGW.ContinuumTrees.BrownianD.variance (NNReal.sqrt 2) t) x := by
  let c : ℝ := t ^ (1 / 2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos ht _
  have hc_sq : c ^ 2 = t := by
    calc
      c ^ 2 = c ^ (2 : ℝ) := (Real.rpow_two c).symm
      _ = t ^ ((1 / 2 : ℝ) * 2) := by
        rw [← Real.rpow_mul ht.le]
      _ = t := by norm_num
  have hs : t ^ (-1 / (2 : ℝ)) = c⁻¹ := by
    rw [show -1 / (2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg ht.le]
  have hvar : NNReal.mk (c ^ 2) (sq_nonneg c) * (2 : ℝ≥0) =
      BGW.ContinuumTrees.BrownianD.variance (NNReal.sqrt 2) t := by
    apply NNReal.coe_injective
    simp [BGW.ContinuumTrees.BrownianD.variance, Real.coe_toNNReal _ ht.le, hc_sq]
    ring
  rw [stableDensityAt, hs, stableDensity_two, gaussianPDFReal_inv_mul hc.ne',
    abs_of_pos hc, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, hvar, mul_zero]

/-- The `θ = 2` bridge prefix weight is the Brownian bridge prefix density with `c = √2`. -/
theorem bridgePrefixWeight_two {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (f : D a ℝ) :
    bridgePrefixWeight 2 a ha f =
      BGW.ContinuumTrees.BrownianD.prefixDensity (NNReal.sqrt 2) a (f ⟨a, ha, le_rfl⟩) := by
  have hvar1 : BGW.ContinuumTrees.BrownianD.variance (NNReal.sqrt 2) 1 = 2 := by
    apply NNReal.coe_injective
    norm_num [BGW.ContinuumTrees.BrownianD.variance]
  unfold bridgePrefixWeight BGW.ContinuumTrees.BrownianD.prefixDensity
  rw [stableDensityAt_two (by linarith), stableDensity_two, hvar1]

/-- **K18a.**  The `θ = 2` stable bridge is `√2` times the standard Brownian bridge. -/
theorem stableBridgeLaw_two :
    stableBridgeLaw 2 = BGW.ContinuumTrees.BrownianD.bridgeD (NNReal.sqrt 2) := by
  symm
  apply stableBridgeLaw_unique_of_endpoints (by norm_num)
  · intro a ha ha1
    rw [BGW.ContinuumTrees.BrownianD.map_restrict_bridgeD_eq_withDensity
      (by positivity : NNReal.sqrt 2 ≠ 0) ha.le ha1, bridgePrefixLaw,
      coe_stableProcessLaw_two ha]
    apply withDensity_congr_ae
    filter_upwards [] with f
    exact congrArg ENNReal.ofReal (bridgePrefixWeight_two ha.le ha1 f).symm
  · filter_upwards [BGW.ContinuumTrees.BrownianD.ae_endpoints_bridgeD (NNReal.sqrt 2),
      BGW.ContinuumTrees.BrownianD.ae_mem_range_ofContinuous_bridgeD (NNReal.sqrt 2)] with f hf
      hrange
    obtain ⟨g, hg⟩ := hrange
    subst f
    have hl (t : Set.Icc (0 : ℝ) 1) : Function.leftLim (ofContinuous g) t = g t :=
      g.continuous.continuousAt.continuousWithinAt.leftLim_eq
    exact ⟨hf.2, by rw [hl]; exact hf.2⟩

end BGW.StableTrees.BrownianIdentification
