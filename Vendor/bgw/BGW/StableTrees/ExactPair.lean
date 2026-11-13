/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPairDensity
public import BGW.StableTrees.ExactPairWeighted
import BGW.Probability.WeakConvergence
import BGW.Skorokhod.RestrictContinuity

/-!
# Exact-size walk and height prefix convergence

The pair is weighted on a larger horizon and then restricted at an almost surely continuous
time. This supplies the joint exact-size prefix limit along every admissible size sequence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail BGW.StableTrees.TailPair
  BGW.StableTrees.ExactPrefix

private theorem continuousAt_restrictPair {a T : ℝ≥0} (haT : a ≤ T)
    {z : D (T : ℝ) ℝ × C(Icc (0 : ℝ) (T : ℝ), ℝ)}
    (hz : ContinuousAt z.1 ⟨a, a.coe_nonneg, haT⟩) :
    ContinuousAt (restrictPair haT) z := by
  apply ContinuousAt.prodMk
  · exact (continuousAt_restrict a.coe_nonneg (NNReal.coe_le_coe.mpr haT) hz).comp
      continuousAt_fst
  · exact (ContinuousMap.continuous_precomp
      ⟨Set.inclusion (Set.Icc_subset_Icc_right (NNReal.coe_le_coe.mpr haT)),
        continuous_inclusion _⟩).continuousAt.comp continuousAt_snd

private theorem ae_continuousAt_restrictPair {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a a' : ℝ≥0} (haa' : a ≤ a') (ha : a ∈ Ioo (0 : ℝ≥0) 1) (ha' : a' ≤ 1) :
    ∀ᵐ z ∂(((excLaw θ).map (restrictPair ha')).toMeasure),
      ContinuousAt (restrictPair haa') z := by
  change ∀ᵐ z ∂(((unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1)).map
    (restrictPair ha')), ContinuousAt (restrictPair haa') z
  rw [Measure.map_map (measurable_restrictPair ha') (measurable_excursionPair θ 1)]
  apply (ae_map_iff ((measurable_restrictPair ha').comp
    (measurable_excursionPair θ 1)).aemeasurable
      (measurableSet_of_continuousAt (restrictPair haa'))).mpr
  filter_upwards [levyExcLaw_noFixedJump hθ a ha] with e he
  apply continuousAt_restrictPair
  change ContinuousAt (excursionRestrict a' e) ⟨a, a.coe_nonneg, haa'⟩
  have hl : Function.leftLim (excursionRestrict a' e) ⟨a, a.coe_nonneg, haa'⟩ =
      excursionRestrict a' e ⟨a, a.coe_nonneg, haa'⟩ := by
    rw [leftLim_excursionRestrict a' a ha.1 haa' e]
    exact he
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (isCadlag (excursionRestrict a' e)).isRightContinuous _⟩
  change Tendsto (excursionRestrict a' e) (𝓝[<] _) (𝓝 _)
  simpa only [hl] using (isCadlag (excursionRestrict a' e)).tendsto_nhdsLT_leftLim
    ⟨a, a.coe_nonneg, haa'⟩

private noncomputable def weightedTailPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ProbabilityMeasure (D (a : ℝ) ℝ × C(Icc (0 : ℝ) (a : ℝ), ℝ)) := by
  let Q := (tailPairLaw μ B n a).toMeasure.withDensity
    (fun z => ENNReal.ofReal (prefixWeightFn μ B n a z.1))
  refine ⟨Q, ⟨?_⟩⟩
  change ((tailPairLaw μ B n a).toMeasure.withDensity _ ) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hm := congrArg (fun ν : Measure (D (a : ℝ) ℝ) => ν univ)
    (exactWalkPrefixLaw_eq_withDensity h hn a ha)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hm
  have hf : (tailPairLaw μ B n a).toMeasure.map Prod.fst =
      (tailWalkPrefixLaw μ B n a).toMeasure :=
    congrArg ProbabilityMeasure.toMeasure (tailPairLaw_map_fst μ B n a)
  rw [← hf] at hm
  rw [lintegral_map (μ := (tailPairLaw μ B n a).toMeasure) (g := Prod.fst)
    (f := fun x => ENNReal.ofReal (prefixWeightFn μ B n a x))
    (ENNReal.measurable_ofReal.comp (measurable_prefixWeightFn μ B n a))
    measurable_fst] at hm
  exact hm.symm

/-- **Joint exact-size prefixes** (C29 prefix part): along every unbounded sequence of admissible
sizes, the (walk, height) pair of the exact-size tree on `[0,a]`, `0 < a < 1`, converges jointly
to the excursion/height prefix of `excLaw θ`. -/
theorem tendsto_exactPairLaw_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => exactPairLaw μ B (q k) (hq k) a) atTop
      (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  let a' : ℝ≥0 := (a + 1) / 2
  have haa' : a < a' := by
    change (a : ℝ) < (a' : ℝ)
    dsimp [a']
    linarith [show (a : ℝ) < 1 from ha.2]
  have ha' : a' ∈ Ioo (0 : ℝ≥0) 1 := by
    constructor
    · exact ha.1.trans haa'
    · change (a' : ℝ) < 1
      dsimp [a']
      linarith [show (a : ℝ) < 1 from ha.2]
  let P := fun k => weightedTailPairLaw h (hq k) a' ha'
  let Q := (excLaw θ).map (restrictPair ha'.2.le)
  have hP : Tendsto P atTop (𝓝 Q) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro F
    have ht := tendsto_integral_mul_prefixWeightFn_tailPairLaw h hqtop hq a' ha' F
    have hi (k : ℕ) : (∫ z, F z ∂(P k).toMeasure) =
        ∫ z, F z * prefixWeightFn μ B (q k) a' z.1 ∂(tailPairLaw μ B (q k) a').toMeasure := by
      change (∫ z, F z ∂((tailPairLaw μ B (q k) a').toMeasure.withDensity _)) = _
      rw [integral_withDensity_eq_integral_toReal_smul
        (μ := (tailPairLaw μ B (q k) a').toMeasure)
        (f := fun z => ENNReal.ofReal (prefixWeightFn μ B (q k) a' z.1))
        (ENNReal.measurable_ofReal.comp
          ((measurable_prefixWeightFn μ B (q k) a').comp measurable_fst))
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change (ENNReal.ofReal (prefixWeightFn μ B (q k) a' z.1)).toReal * F z = _
        rw [ENNReal.toReal_ofReal (prefixWeightFn_nonneg μ B (q k) a' z.1), mul_comm]
    simpa only [hi] using ht
  have ht := BGW.Probability.tendsto_map_of_ae_continuousAt hP
    (fun _ => (measurable_restrictPair haa'.le).aemeasurable)
    (ae_continuousAt_restrictPair h.alpha_mem haa'.le ha ha'.2.le)
  have hQ : Q.map (restrictPair haa'.le) = (excLaw θ).map (restrictPair ha.2.le) := by
    apply Subtype.ext
    change ((excLaw θ).toMeasure.map (restrictPair ha'.2.le)).map (restrictPair haa'.le) =
      (excLaw θ).toMeasure.map (restrictPair ha.2.le)
    erw [Measure.map_map (measurable_restrictPair haa'.le) (measurable_restrictPair ha'.2.le)]
    rfl
  rw [hQ] at ht
  have hbuffer : ∀ᶠ k in atTop, ⌊(a : ℝ) * q k⌋₊ + 1 ≤ ⌊(a' : ℝ) * q k⌋₊ := by
    have hgap : 0 < (a' : ℝ) - a := sub_pos.mpr (NNReal.coe_lt_coe.mpr haa')
    have hcast : Tendsto (fun k => (q k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hqtop
    filter_upwards [hcast.eventually (eventually_ge_atTop (1 / ((a' : ℝ) - a)))] with k hk
    apply Nat.le_floor
    have hfloor := Nat.floor_le (mul_nonneg a.coe_nonneg (Nat.cast_nonneg (q k)))
    have hh := (div_le_iff₀ hgap).mp hk
    push_cast
    nlinarith
  apply ht.congr'
  filter_upwards [hbuffer] with k hk
  apply Subtype.ext
  exact (exactPairLaw_eq_map_withDensity h (hq k) haa'.le ha' hk).symm

end BGW.StableTrees.ExactPair
