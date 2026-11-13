/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.VervaatIto
import BGW.StableTrees.BrownianIdentification
public import BGW.ContinuumTrees.VervaatBridge
import BGW.Skorokhod.VervaatComparison
import BGW.ContinuumTrees.CodingScaling

/-!
# Brownian excursion normalization

At stability index two, the normalized Itô excursion is the Vervaat transform of a Brownian
bridge scaled by `√2`. Positive scaling commutes with the continuous-loop Vervaat transform, so
this law is `√2` times the Brownian Vervaat path law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open BGW.ContinuumTrees.Vervaat

namespace BGW.StableTrees.BrownianIdentification

open BGW.Skorokhod

/-- Positive scaling commutes with the continuous-loop Vervaat transform. -/
theorem vervaat_smul {c : ℝ} (hc : 0 < c) (g : {g : C(unitInterval, ℝ) // g 0 = g 1}) :
    BGW.ContinuumTrees.Vervaat.vervaat
        ⟨c • g.1, by simp only [ContinuousMap.smul_apply, g.2]⟩ =
      c • BGW.ContinuumTrees.Vervaat.vervaat g := by
  have hmin : BGW.ContinuumTrees.Coding.intervalMin (c • g.1) 0 1 =
      c * BGW.ContinuumTrees.Coding.intervalMin g.1 0 1 :=
    BGW.ContinuumTrees.Coding.intervalMin_smul g.1 c hc.le 0 1
  have hminimizer (t : unitInterval) :
      (c • g.1) t = BGW.ContinuumTrees.Coding.intervalMin (c • g.1) 0 1 ↔
        g.1 t = BGW.ContinuumTrees.Coding.intervalMin g.1 0 1 := by
    rw [ContinuousMap.smul_apply, smul_eq_mul, hmin]
    constructor <;> intro h <;> nlinarith
  have hfirst : firstMinimum (c • g.1) = firstMinimum g.1 := by
    apply le_antisymm
    · exact (isLeast_firstMinimum (c • g.1)).2
        ((hminimizer _).mpr (isLeast_firstMinimum g.1).1)
    · exact (isLeast_firstMinimum g.1).2
        ((hminimizer _).mp (isLeast_firstMinimum (c • g.1)).1)
  apply ContinuousMap.ext
  intro t
  simp only [vervaat_apply, ContinuousMap.smul_apply, smul_eq_mul, hfirst, hmin]
  ring

/-- **K18b.** At `θ = 2` the normalized Itô excursion is `√2` times the Brownian excursion
(Vervaat transform of the Brownian bridge). -/
theorem levyExcLaw_two :
    (levyExcLaw 2 : Measure (D 1 ℝ)) =
      (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)).map
        (fun e => ofContinuous (T := 1) (Real.sqrt 2 • e)) := by
  rw [← BGW.StableTrees.VervaatIto.map_vervaatD_stableBridgeLaw
    (by norm_num : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2), stableBridgeLaw_two]
  let c : ℝ := (NNReal.sqrt 2 : ℝ≥0)
  have hc : 0 < c := by
    dsimp [c]
    simp
  have hscaleNN : Measurable (fun g : C(unitInterval, ℝ) =>
      ofContinuous (T := 1) (c • g)) := by
    exact BGW.ContinuumTrees.BrownianD.measurable_ofContinuous.comp
      (continuous_id.const_smul c).measurable
  have hscaleR : Measurable (fun g : C(unitInterval, ℝ) =>
      ofContinuous (T := 1) (Real.sqrt 2 • g)) := by
    exact BGW.ContinuumTrees.BrownianD.measurable_ofContinuous.comp
      (continuous_id.const_smul (Real.sqrt 2)).measurable
  change Measure.map vervaatD
      (Measure.map (fun g : C(unitInterval, ℝ) => ofContinuous (T := 1) (c • g))
        (Measure.map BGW.ContinuumTrees.BrownianBridge.path
          ProbabilityTheory.gaussianLimit)) =
    Measure.map (fun e : C(unitInterval, ℝ) => ofContinuous (T := 1) (Real.sqrt 2 • e))
      (Measure.map BGW.ContinuumTrees.VervaatBridge.path ProbabilityTheory.gaussianLimit)
  rw [Measure.map_map measurable_vervaatD hscaleNN,
    Measure.map_map (measurable_vervaatD.comp hscaleNN)
      BGW.ContinuumTrees.BrownianBridge.measurable_path,
    Measure.map_map hscaleR BGW.ContinuumTrees.VervaatBridge.measurable_path]
  congr 1
  funext ω
  have hloop :
      (c • BGW.ContinuumTrees.BrownianBridge.path ω) 0 =
        (c • BGW.ContinuumTrees.BrownianBridge.path ω) 1 := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul,
      BGW.ContinuumTrees.BrownianBridge.path_zero,
      BGW.ContinuumTrees.BrownianBridge.path_one, mul_zero]
  have hloop' : BGW.ContinuumTrees.BrownianBridge.path ω 0 =
      BGW.ContinuumTrees.BrownianBridge.path ω 1 := by
    rw [BGW.ContinuumTrees.BrownianBridge.path_zero,
      BGW.ContinuumTrees.BrownianBridge.path_one]
  simp only [Function.comp_apply]
  rw [vervaatD_ofContinuous _ hloop]
  have hsmul := vervaat_smul hc
    ⟨BGW.ContinuumTrees.BrownianBridge.path ω, hloop'⟩
  simpa [c, BGW.ContinuumTrees.VervaatBridge.path, Real.coe_sqrt] using
    congrArg (fun e : C(unitInterval, ℝ) => ofContinuous (T := 1) e) hsmul

end BGW.StableTrees.BrownianIdentification
