/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPrefixDiscrete
public import BGW.StableTrees.ExactPrefixLimit
public import BGW.StableTrees.ExactPrefixWeighted
import BGW.StableTrees.GammaIdentity

/-!
# Exact-size Łukasiewicz prefixes through tail conditioning

The finite prefix Radon–Nikodym identity and compact-uniform forest estimates transfer
convergence of tail-conditioned paths to the unit excursion prefix law. Mass one and
Scheffé's theorem control the weights at both ends of the positive half-line.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteBridge (endValue)
open BGW.StableTrees.PathTail (tailWalkPrefixLaw tailPrefixLimit)

namespace BGW.StableTrees.ExactPrefix

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-- The weight is nonnegative and has mean one under the tail walk prefix law
(K02 `lintegral_prefixDensity_tail`). -/
theorem integral_prefixWeightFn_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    (∀ x, 0 ≤ prefixWeightFn μ B n a x) ∧
      ∫ x, prefixWeightFn μ B n a x ∂(tailWalkPrefixLaw μ B n a : Measure (D (a : ℝ) ℝ)) = 1 :=
  by
    have hnn := prefixWeightFn_nonneg μ B n a
    have hm := congrArg (fun ν : Measure (D (a : ℝ) ℝ) => ν univ)
      (exactWalkPrefixLaw_eq_withDensity h hn a ha)
    rw [measure_univ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hm
    have hi : Integrable (prefixWeightFn μ B n a)
        (tailWalkPrefixLaw μ B n a : Measure (D (a : ℝ) ℝ)) :=
      (lintegral_ofReal_ne_top_iff_integrable
        (measurable_prefixWeightFn μ B n a).aestronglyMeasurable (ae_of_all _ hnn)).mp
        (by rw [← hm]; exact ENNReal.one_ne_top)
    refine ⟨hnn, ?_⟩
    have hh := congrArg ENNReal.toReal hm
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnn),
      ENNReal.toReal_ofReal (integral_nonneg hnn)] at hh
    exact hh.symm

/-- **Exact-size walk prefixes (K07 main theorem).**  Along an unbounded sequence of admissible
sizes the exact-size Łukasiewicz path on `[0,a]`, `a ∈ (0,1)`, scaled by `B (q k)`, converges
weakly to the prefix of the unit excursion law. -/
theorem tendsto_exactWalkLaw_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => exactWalkPrefixLaw μ B (q k) (hq k) a ha.2.le) atTop
      (𝓝 ((unitExcursionLaw θ).map (excursionRestrict a))) := by
  let P := fun k => tailWalkPrefixLaw μ B (q k) a
  let P₀ := tailPrefixLimit θ a
  let w := fun k => prefixWeightFn μ B (q k) a
  let w₀ := fun x : D (a : ℝ) ℝ => max (gammaA θ a (endValue a x)) 0
  have hwm : Measurable w₀ :=
    ((measurable_gammaA θ).comp
      (measurable_const.prodMk (measurable_eval _))).max measurable_const
  have hgood := ae_tailPrefix_continuousAt_pos h.alpha_mem a ha
  have hw₀eq : w₀ =ᵐ[(P₀ : Measure (D (a : ℝ) ℝ))]
      fun x => gammaA θ a (endValue a x) := by
    filter_upwards [hgood] with x hx
    exact max_eq_left (gammaA_nonneg h.alpha_mem ha.2 hx.2)
  have hm₀ : ∫ x, w₀ x ∂(P₀ : Measure (D (a : ℝ) ℝ)) = 1 := by
    rw [integral_congr_ae hw₀eq]
    exact (integral_gammaA_tail_eq_one h.alpha_mem a ha).2
  let S := fun k => {x : D (a : ℝ) ℝ | LatticeGood μ B (q k) a x}
  let G := {x : D (a : ℝ) ℝ |
    ContinuousAt x ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩ ∧ 0 < endValue a x}
  have hS (k : ℕ) : (P k : Measure (D (a : ℝ) ℝ)) (S k)ᶜ = 0 := by
    exact ae_iff.mp (ae_latticeGood_tailWalkPrefixLaw h (hq k) a ha)
  have hG : (P₀ : Measure (D (a : ℝ) ℝ)) Gᶜ = 0 := ae_iff.mp hgood
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  have ht := tendsto_integral_mul_weight (PathTail.tendsto_tailWalkPrefixLaw h hqtop a ha)
    (fun k => measurable_prefixWeightFn μ B (q k) a) hwm
    (fun k => prefixWeightFn_nonneg μ B (q k) a) (fun _ => le_max_right _ _)
    (fun k => (integral_prefixWeightFn_tail h (hq k) a ha).2) hm₀ S hS G hG
    (fun x hx y hy hyx => by
      have hc := tendsto_prefixWeightFn_continuousConv h hqtop hq a ha hx.1 hx.2 hy hyx
      have he : w₀ x = gammaA θ a (endValue a x) :=
        max_eq_left (gammaA_nonneg h.alpha_mem ha.2 hx.2)
      exact he.symm ▸ hc) F
  have hsource (k : ℕ) : (∫ x, F x ∂(exactWalkPrefixLaw μ B (q k) (hq k) a ha.2.le)) =
      ∫ x, F x * w k x ∂(P k : Measure (D (a : ℝ) ℝ)) := by
    rw [exactWalkPrefixLaw_eq_withDensity h (hq k) a ha,
      integral_withDensity_eq_integral_toReal_smul
        (f := fun x => ENNReal.ofReal (prefixWeightFn μ B (q k) a x))
        (ENNReal.measurable_ofReal.comp (measurable_prefixWeightFn μ B (q k) a))
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (ENNReal.ofReal (prefixWeightFn μ B (q k) a x)).toReal * F x =
        F x * prefixWeightFn μ B (q k) a x
      rw [ENNReal.toReal_ofReal (prefixWeightFn_nonneg μ B (q k) a x), mul_comm]
  have htarget : (∫ x, F x * w₀ x ∂(P₀ : Measure (D (a : ℝ) ℝ))) =
      ∫ x, F x ∂((unitExcursionLaw θ).map (excursionRestrict a)) := by
    calc
      _ = ∫ x, F x * gammaA θ a (endValue a x) ∂(P₀ : Measure (D (a : ℝ) ℝ)) :=
        integral_congr_ae (hw₀eq.mono fun x hx => by rw [hx])
      _ = _ := (gamma_identity_path h.alpha_mem a ha F F.continuous.measurable
        ⟨‖F‖, fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm x⟩).symm
  change Tendsto (fun k => ∫ x, F x * w k x ∂(P k : Measure (D (a : ℝ) ℝ)))
    atTop (𝓝 (∫ x, F x * w₀ x ∂(P₀ : Measure (D (a : ℝ) ℝ)))) at ht
  simpa only [← hsource, htarget] using ht

end BGW.StableTrees.ExactPrefix
