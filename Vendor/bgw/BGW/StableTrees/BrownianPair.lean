/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.JointExcursion
public import BGW.ContinuumTrees.BrownianD
public import BGW.ContinuumTrees.VervaatBridge

import BGW.StableTrees.BrownianExcursion
import BGW.StableTrees.ExcursionHeightTwo
import BGW.Skorokhod.ContinuousEmbedding

/-!
# The Brownian joint excursion law

At stability index two, the normalized excursion path and its height are almost surely the same
function.  Combining this diagonal support with the Brownian path marginal identifies their joint
law with the law of a single scaled Vervaat excursion, viewed both as a càdlàg and as a continuous
path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace BGW.StableTrees.BrownianIdentification

open BGW.Skorokhod

/-- Measurability guard: the pair map `e ↦ (√2 e, √2 e)`, with the first coordinate seen as a
càdlàg path, is measurable (so the image law in `excLaw_two` is not a junk pushforward). -/
theorem measurable_sqrtTwoPair :
    Measurable (fun e : C(unitInterval, ℝ) =>
      (ofContinuous (T := 1) (Real.sqrt 2 • e), Real.sqrt 2 • e)) :=
  (BGW.ContinuumTrees.BrownianD.measurable_ofContinuous.comp
    (continuous_id.const_smul (Real.sqrt 2)).measurable).prodMk
      (continuous_id.const_smul (Real.sqrt 2)).measurable

private theorem measurable_ofContinuous_pair :
    Measurable (fun g : C(unitInterval, ℝ) => (ofContinuous (T := 1) g, g)) :=
  BGW.ContinuumTrees.BrownianD.measurable_ofContinuous.prodMk measurable_id

private theorem excLaw_two_reconstruction :
    (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))) =
      (((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
        Measure C(unitInterval, ℝ)).map
          (fun g => (ofContinuous (T := 1) g, g)) := by
  calc
    (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))) =
        (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))).map id := Measure.map_id.symm
    _ = (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))).map
        ((fun g : C(unitInterval, ℝ) => (ofContinuous (T := 1) g, g)) ∘ Prod.snd) := by
      apply Measure.map_congr
      filter_upwards [excLaw_height_eq_path_two] with z hz
      apply Prod.ext
      · apply BGW.Skorokhod.ext
        intro t
        exact (hz t).symm
      · rfl
    _ = (((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
        Measure C(unitInterval, ℝ)).map
          (fun g => (ofContinuous (T := 1) g, g)) :=
      (Measure.map_map measurable_ofContinuous_pair measurable_snd).symm

private theorem excLaw_two_map_snd_aux :
    (((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
      Measure C(unitInterval, ℝ)) =
      (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)).map
        (fun e => Real.sqrt 2 • e) := by
  have hscale : Measurable (fun e : C(unitInterval, ℝ) => Real.sqrt 2 • e) :=
    (continuous_id.const_smul (Real.sqrt 2)).measurable
  have hfirst :
      (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))).map Prod.fst =
        (((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
          Measure C(unitInterval, ℝ)).map (ofContinuous (T := 1)) := by
    calc
      (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))).map Prod.fst =
          ((((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
            Measure C(unitInterval, ℝ)).map
              (fun g => (ofContinuous (T := 1) g, g))).map Prod.fst :=
        congrArg (Measure.map Prod.fst) excLaw_two_reconstruction
      _ = (((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
          Measure C(unitInterval, ℝ)).map
            (Prod.fst ∘ (fun g : C(unitInterval, ℝ) => (ofContinuous (T := 1) g, g))) :=
        Measure.map_map measurable_fst measurable_ofContinuous_pair
      _ = (((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
          Measure C(unitInterval, ℝ)).map (ofContinuous (T := 1)) := rfl
  apply (isClosedEmbedding_ofContinuous (T := 1) (E := ℝ)).measurableEmbedding.map_injective
  rw [← hfirst]
  calc
    (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))).map Prod.fst =
        (levyExcLaw 2 : Measure (D 1 ℝ)) :=
      congrArg ProbabilityMeasure.toMeasure (excLaw_map_fst 2)
    _ = (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)).map
        (fun e => ofContinuous (T := 1) (Real.sqrt 2 • e)) := levyExcLaw_two
    _ = ((BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)).map
        (fun e => Real.sqrt 2 • e)).map (ofContinuous (T := 1)) :=
      (Measure.map_map BGW.ContinuumTrees.BrownianD.measurable_ofContinuous hscale).symm

/-- **K18c.**  At `θ = 2` the normalized excursion/height pair has the law of `(√2 e, √2 e)` for
one Brownian excursion `e` (Vervaat transform of the Brownian bridge). -/
theorem excLaw_two :
    excLaw 2 = BGW.ContinuumTrees.VervaatBridge.law.map
      (fun e => (BGW.Skorokhod.ofContinuous (T := 1) (Real.sqrt 2 • e),
        Real.sqrt 2 • e)) := by
  apply Subtype.ext
  calc
    (excLaw 2 : Measure (D 1 ℝ × C(unitInterval, ℝ))) =
        (((excLaw 2).map Prod.snd : ProbabilityMeasure C(unitInterval, ℝ)) :
          Measure C(unitInterval, ℝ)).map
            (fun g => (ofContinuous (T := 1) g, g)) := excLaw_two_reconstruction
    _ = ((BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)).map
        (fun e => Real.sqrt 2 • e)).map
          (fun g => (ofContinuous (T := 1) g, g)) :=
      congrArg (Measure.map (fun g : C(unitInterval, ℝ) => (ofContinuous (T := 1) g, g)))
        excLaw_two_map_snd_aux
    _ = (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)).map
        ((fun g : C(unitInterval, ℝ) => (ofContinuous (T := 1) g, g)) ∘
          (fun e => Real.sqrt 2 • e)) :=
      Measure.map_map measurable_ofContinuous_pair
        (continuous_id.const_smul (Real.sqrt 2)).measurable

/-- Height marginal at `θ = 2` (C30(a)): the excursion height has the law of `√2 e`. -/
theorem excLaw_two_map_snd :
    (excLaw 2).map Prod.snd =
      BGW.ContinuumTrees.VervaatBridge.law.map (fun e => Real.sqrt 2 • e) := by
  apply Subtype.ext
  exact excLaw_two_map_snd_aux

/-- The C29 (K16) limit at `θ = 2`: the duplicated excursion height has the law of
`(√2 e, √2 e)`. -/
theorem excLaw_two_map_diag :
    (excLaw 2).map (fun p => (p.2, p.2)) =
      BGW.ContinuumTrees.VervaatBridge.law.map
        (fun e => (Real.sqrt 2 • e, Real.sqrt 2 • e)) := by
  rw [excLaw_two]
  apply Subtype.ext
  exact Measure.map_map (measurable_snd.prodMk measurable_snd) measurable_sqrtTwoPair

end BGW.StableTrees.BrownianIdentification
