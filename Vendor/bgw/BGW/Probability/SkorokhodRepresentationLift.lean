/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.SkorokhodRepresentation
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Skorokhod representations with lifted limit variables

Graph disintegration lifts a represented marginal through a measurable map and retains the
original probability carrier. Combined with Skorokhod representation, this gives full-sequence
almost sure convergence to a measurable image of an original-carrier random variable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory Topology

namespace BGW.Probability

private theorem map_compProd_comap {Ω S E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure Ω) [SFinite μ] (κ : Kernel S E) [IsSFiniteKernel κ]
    {Y : Ω → S} (hY : Measurable Y) :
    (μ ⊗ₘ κ.comap Y hY).map (fun p => (Y p.1, p.2)) = μ.map Y ⊗ₘ κ := by
  have hm : Measurable (fun p : Ω × E => (Y p.1, p.2)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hm hs,
    Measure.compProd_apply (hs.preimage hm),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hY]
  rfl

/-- A random variable with the image law of a standard Borel probability admits a lift on a
product extension, retaining its original marginal and satisfying the image identity a.s. -/
theorem exists_lift_of_map_eq {Ω S E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace E]
    [StandardBorelSpace E] [MeasurableEq S]
    (μ : ProbabilityMeasure Ω) (ν : ProbabilityMeasure E)
    {Y : Ω → S} (hY : Measurable Y) {f : E → S} (hf : Measurable f)
    (hlaw : (μ : Measure Ω).map Y = (ν : Measure E).map f) :
    ∃ νlift : ProbabilityMeasure (Ω × E),
      (νlift : Measure (Ω × E)).map Prod.fst = (μ : Measure Ω) ∧
      (νlift : Measure (Ω × E)).map Prod.snd = (ν : Measure E) ∧
      ∀ᵐ p ∂(νlift : Measure (Ω × E)), f p.2 = Y p.1 := by
  let : Nonempty E := ν.nonempty
  let ρ : Measure (S × E) := (ν : Measure E).map (fun e => (f e, e))
  have hρfst : ρ.fst = (ν : Measure E).map f :=
    Measure.fst_map_prodMk hf measurable_id
  let κ : Kernel S E := ρ.condKernel
  let νlift : Measure (Ω × E) := (μ : Measure Ω) ⊗ₘ κ.comap Y hY
  have hm : Measurable (fun p : Ω × E => (Y p.1, p.2)) := by fun_prop
  have hjoint : νlift.map (fun p => (Y p.1, p.2)) = ρ := by
    rw [map_compProd_comap _ _ hY, hlaw, ← hρfst]
    exact ρ.disintegrate κ
  have hfirst : νlift.map Prod.fst = (μ : Measure Ω) :=
    Measure.fst_compProd _ _
  have hsecond : νlift.map Prod.snd = (ν : Measure E) := by
    have he := congrArg (Measure.map (Prod.snd : S × E → E)) hjoint
    rw [Measure.map_map measurable_snd hm] at he
    change νlift.map Prod.snd = ρ.map Prod.snd at he
    rw [he]
    dsimp [ρ]
    have hfm : Measurable (fun e : E => (f e, e)) := by fun_prop
    rw [Measure.map_map measurable_snd hfm]
    exact Measure.map_id
  have hgraph : ∀ᵐ p ∂νlift, f p.2 = Y p.1 := by
    have hr : ∀ᵐ q ∂ρ, f q.2 = q.1 := by
      exact ae_map_iff (hf.prodMk measurable_id).aemeasurable
        (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst) |>.mpr
          (Eventually.of_forall fun _ => rfl)
    rw [← hjoint] at hr
    exact ae_of_ae_map hm.aemeasurable hr
  have hprob : IsProbabilityMeasure νlift := inferInstance
  exact ⟨⟨νlift, hprob⟩, hfirst, hsecond, hgraph⟩

/-- Full-sequence Skorokhod representation whose limiting variable is lifted to its original
standard Borel carrier. All finite-index laws and the original limiting law are retained. -/
theorem exists_representation_with_lift {S E : Type*}
    [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    [MeasurableSpace E] [StandardBorelSpace E]
    (P : ℕ → ProbabilityMeasure S) (ν : ProbabilityMeasure E)
    (f : E → S) (hf : Measurable f)
    (hP : Tendsto P atTop (𝓝 (ν.map f))) :
    ∃ (η : ProbabilityMeasure (unitInterval × E)) (X : ℕ → unitInterval × E → S),
      (∀ n, Measurable (X n)) ∧
      (∀ n, (η : Measure (unitInterval × E)).map (X n) = (P n : Measure S)) ∧
      (η : Measure (unitInterval × E)).map Prod.snd = (ν : Measure E) ∧
      ∀ᵐ p ∂(η : Measure (unitInterval × E)),
        Tendsto (fun n => X n p) atTop (𝓝 (f p.2)) := by
  obtain ⟨U, V, hU, hV, hUlaw, hVlaw, hconv⟩ :=
    BGW.Probability.exists_tendsto_ae_of_tendsto hP
  let μ : ProbabilityMeasure unitInterval := ⟨volume, inferInstance⟩
  obtain ⟨η, hηfst, hηsnd, hηgraph⟩ := exists_lift_of_map_eq μ ν hV hf hVlaw
  let X (n : ℕ) (p : unitInterval × E) := U n p.1
  have hXm (n : ℕ) : Measurable (X n) := (hU n).comp measurable_fst
  have hXlaw (n : ℕ) : (η : Measure (unitInterval × E)).map (X n) = (P n : Measure S) := by
    change (η : Measure (unitInterval × E)).map (U n ∘ Prod.fst) = _
    rw [← Measure.map_map (hU n) measurable_fst, hηfst]
    exact hUlaw n
  have hconv' : ∀ᵐ p ∂(η : Measure (unitInterval × E)),
      Tendsto (fun n => X n p) atTop (𝓝 (f p.2)) := by
    have hpull : ∀ᵐ p ∂(η : Measure (unitInterval × E)),
        Tendsto (fun n => U n p.1) atTop (𝓝 (V p.1)) := by
      have hc : ∀ᵐ z ∂((η : Measure (unitInterval × E)).map Prod.fst),
          Tendsto (fun n => U n z) atTop (𝓝 (V z)) := by
        rw [hηfst]
        exact hconv
      exact ae_of_ae_map measurable_fst.aemeasurable hc
    filter_upwards [hpull, hηgraph] with p hp hpg
    rwa [← hpg] at hp
  exact ⟨η, X, hXm, hXlaw, hηsnd, hconv'⟩

end BGW.Probability
