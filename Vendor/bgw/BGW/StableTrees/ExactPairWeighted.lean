/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPairBasic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Weighted convergence on the walk and height pair space

The walk marginal supplies lattice support and mass-one endpoint weights. Joint tail
convergence and the joint Gamma identity identify the weighted limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail BGW.StableTrees.TailPair
  BGW.StableTrees.ExactPrefix

/-- **Weighted tail convergence at horizon `a'`** (K07's generic helper on the pair space, J01's
joint Γ identity): bounded continuous tests of the tail pair on `[0,a']`, weighted by the sealed
walk weight, converge to the tests of the excursion/height prefix on `[0,a']`. -/
theorem tendsto_integral_mul_prefixWeightFn_tailPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a' : ℝ≥0) (ha' : a' ∈ Ioo (0 : ℝ≥0) 1)
    (F : BoundedContinuousFunction (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ)) ℝ) :
    Tendsto (fun k => ∫ z, F z * prefixWeightFn μ B (q k) a' z.1
        ∂(tailPairLaw μ B (q k) a' :
          Measure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ)))) atTop
      (𝓝 (∫ z, F z ∂((excLaw θ).map (restrictPair ha'.2.le) :
          Measure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ))))) := by
  let E := D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ)
  let P := fun k => tailPairLaw μ B (q k) a'
  let P₀ := tailExcLaw θ a'
  let w := fun k (z : E) => prefixWeightFn μ B (q k) a' z.1
  let w₀ := fun z : E => max (gammaA θ a' (DiscreteBridge.endValue a' z.1)) 0
  have hwm : Measurable w₀ :=
    (((measurable_gammaA θ).comp
      (measurable_const.prodMk (measurable_eval _))).comp measurable_fst).max measurable_const
  have hfst (k : ℕ) : (P k : Measure E).map Prod.fst =
      (tailWalkPrefixLaw μ B (q k) a' : Measure (D (a' : ℝ) ℝ)) :=
    congrArg ProbabilityMeasure.toMeasure (tailPairLaw_map_fst μ B (q k) a')
  have hfst₀ : (P₀ : Measure E).map Prod.fst =
      (tailPrefixLimit θ a' : Measure (D (a' : ℝ) ℝ)) :=
    congrArg ProbabilityMeasure.toMeasure (tailExcLaw_map_fst θ a')
  have hgood : ∀ᵐ z ∂(P₀ : Measure E),
      ContinuousAt z.1 ⟨(a' : ℝ), a'.coe_nonneg, le_rfl⟩ ∧
        0 < DiscreteBridge.endValue a' z.1 := by
    have hh := ae_tailPrefix_continuousAt_pos h.alpha_mem a' ha'
    rw [← hfst₀] at hh
    exact ae_of_ae_map measurable_fst.aemeasurable hh
  have hw₀eq : w₀ =ᵐ[(P₀ : Measure E)]
      fun z => gammaA θ a' (DiscreteBridge.endValue a' z.1) := by
    filter_upwards [hgood] with z hz
    exact max_eq_left (gammaA_nonneg h.alpha_mem ha'.2 hz.2)
  have hm₀ : ∫ z, w₀ z ∂(P₀ : Measure E) = 1 := by
    rw [integral_congr_ae hw₀eq]
    rw [← integral_map (μ := (P₀ : Measure E)) (φ := Prod.fst)
      (f := fun x => gammaA θ a' (DiscreteBridge.endValue a' x))
      measurable_fst.aemeasurable
      ((measurable_gammaA θ).comp
        (measurable_const.prodMk (measurable_eval _))).aestronglyMeasurable, hfst₀]
    exact (integral_gammaA_tail_eq_one h.alpha_mem a' ha').2
  have hm (k : ℕ) : ∫ z, w k z ∂(P k : Measure E) = 1 := by
    change (∫ z : E, prefixWeightFn μ B (q k) a' z.1 ∂(P k : Measure E)) = 1
    rw [← integral_map (μ := (P k : Measure E)) (φ := Prod.fst)
      (f := prefixWeightFn μ B (q k) a') measurable_fst.aemeasurable
        (measurable_prefixWeightFn μ B (q k) a').aestronglyMeasurable, hfst]
    exact (integral_prefixWeightFn_tail h (hq k) a' ha').2
  let S := fun k => {z : E | LatticeGood μ B (q k) a' z.1}
  let G := {z : E | ContinuousAt z.1 ⟨(a' : ℝ), a'.coe_nonneg, le_rfl⟩ ∧
    0 < DiscreteBridge.endValue a' z.1}
  have hS (k : ℕ) : (P k : Measure E) (S k)ᶜ = 0 := by
    apply ae_iff.mp
    have hh := ae_latticeGood_tailWalkPrefixLaw h (hq k) a' ha'
    rw [← hfst] at hh
    exact ae_of_ae_map measurable_fst.aemeasurable hh
  have ht := tendsto_integral_mul_weight ((tendsto_tailPairLaw h ha'.1).comp hqtop)
    (fun k => (measurable_prefixWeightFn μ B (q k) a').comp measurable_fst) hwm
    (fun k z => prefixWeightFn_nonneg μ B (q k) a' z.1) (fun _ => le_max_right _ _)
    hm hm₀ S hS G (ae_iff.mp hgood)
    (fun z hz y hy hyz => by
      have hc := tendsto_prefixWeightFn_continuousConv h hqtop hq a' ha' hz.1 hz.2 hy
        hyz.fst_nhds
      have he : w₀ z = gammaA θ a' (DiscreteBridge.endValue a' z.1) :=
        max_eq_left (gammaA_nonneg h.alpha_mem ha'.2 hz.2)
      exact he.symm ▸ hc) F
  have htarget : (∫ z, F z * w₀ z ∂(P₀ : Measure E)) =
      ∫ z, F z ∂((excLaw θ).map (restrictPair ha'.2.le) : Measure E) := by
    rw [integral_congr_ae (hw₀eq.mono fun z hz => by rw [hz])]
    have hg := (gamma_identity h.alpha_mem a' ha' F F.continuous.measurable
      ⟨‖F‖, fun z => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm z⟩).2.2
    calc
      _ = ∫ z, F (restrictPair ha'.2.le z) *
          gammaA θ a' (evalEnd a' (restrictPair ha'.2.le z).1)
            ∂(tailExcLaw θ 1).toMeasure := by
        have hproj := congrArg ProbabilityMeasure.toMeasure
          (tailExcLaw_map_restrictPair θ ha'.2.le)
        change (∫ z : E, F z * gammaA θ a' (DiscreteBridge.endValue a' z.1)
          ∂(tailExcLaw θ a').toMeasure) = _
        rw [← hproj]
        exact integral_map (measurable_restrictPair ha'.2.le).aemeasurable
          (F.continuous.measurable.mul
            (((measurable_gammaA θ).comp
              (measurable_const.prodMk (measurable_eval _))).comp
                measurable_fst)).aestronglyMeasurable
      _ = ∫ z, F (restrictPair ha'.2.le z) ∂(excLaw θ).toMeasure := hg.symm
      _ = _ := (integral_map (μ := (excLaw θ).toMeasure)
        (measurable_restrictPair ha'.2.le).aemeasurable
          F.continuous.aestronglyMeasurable).symm
  exact htarget ▸ ht

end BGW.StableTrees.ExactPair
