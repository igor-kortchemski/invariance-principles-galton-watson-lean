/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightContinuityHolder

/-!
# One common continuous stable height process

Moment bounds construct a continuous modification. Rational agreement identifies it with
`heightLoc`, reconstructed from `heightUniv`. Literal prefix locality and uniqueness imply
one graph event for all horizons. The compact walk/height law is its graph pushforward.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Graph identity on one event for all horizons** (CT8 blueprint §2 item 3). -/
theorem ae_heightPrefix_restrict_all {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0, ∀ t : Set.Icc (0 : ℝ) T,
      heightPrefix θ T (DLoc.restrict T f) t = heightLoc θ f ⟨t, t.2.1⟩ := by
  filter_upwards [ae_exists_continuous_height hθ] with f hf
  have he : heightLoc θ f = Classical.choose hf :=
    heightLoc_eq_of_rational_agreement θ f _ (Classical.choose_spec hf)
  intro T t
  let c : C(Set.Icc (0 : ℝ) T, ℝ) :=
    ⟨fun t => heightLoc θ f ⟨t, t.2.1⟩,
      (continuous_heightLoc θ f).comp (continuous_subtype_val.subtype_mk fun t => t.2.1)⟩
  have hc (u : Set.Icc (0 : ℝ) T) (hu : IsRationalTime ⟨u, u.2.1⟩) :
      c u = heightUniv θ f ⟨u, u.2.1⟩ := by
    change heightLoc θ f ⟨u, u.2.1⟩ = _
    rw [he]
    exact Classical.choose_spec hf _ hu
  exact congrArg (fun d : C(Set.Icc (0 : ℝ) T, ℝ) => d t)
    (heightPrefix_eq_of_rational_agreement θ T f c hc)

/-- **Graph identity**: almost surely, on every time of `[0,T]`, the prefix map applied to the
restriction of the path is the continuous height. -/
theorem ae_heightPrefix_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : Set.Icc (0 : ℝ) T,
      heightPrefix θ T (DLoc.restrict T f) t = heightLoc θ f ⟨t, t.2.1⟩ := by
  exact (ae_heightPrefix_restrict_all hθ).mono fun _ hf => hf T

/-- Fixed-time evaluation of the prefix map is H02's height a.s. -/
theorem ae_heightPrefix_eval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (t : Set.Icc (0 : ℝ) T) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      heightPrefix θ T (DLoc.restrict T f) t = height θ f ⟨t, t.2.1⟩ := by
  filter_upwards [ae_heightPrefix_restrict hθ T, ae_heightLoc_eq_height hθ ⟨t, t.2.1⟩]
    with f hf ht
  exact (hf t).trans ht

/-- **Pair law**: the walk/height pair on `[0,T]` is the graph pushforward of the stable process
law on `[0,T]` (all `T`, including `T = 0`). -/
theorem map_heightPrefix_pair {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)).map
        (fun g => (g, heightPrefix θ T g)) := by
  have he : (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict T) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)) := by
    by_cases hT : T = 0
    · subst T
      exact map_restrict_zero_stableLocalLaw hθ
    · exact map_restrict_stableLocalLaw hθ (pos_iff_ne_zero.mpr hT)
  have hm : Measurable (fun g : D (T : ℝ) ℝ => (g, heightPrefix θ T g)) :=
    measurable_id.prodMk (measurable_heightPrefix θ T)
  rw [← he]
  simpa only [Function.comp_def] using
    (Measure.map_map hm (DLoc.measurable_restrict T)
      (μ := (stableLocalLaw θ : Measure DLoc))).symm

end BGW.StableTrees
