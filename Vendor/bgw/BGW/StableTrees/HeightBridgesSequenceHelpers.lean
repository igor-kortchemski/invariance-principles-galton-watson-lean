/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesDiagonal
public import BGW.StableTrees.HeightBridgesAgeLaws
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Extraction and inheritance on the separate height laws

Each age window retains its own measure. Fubini converts the extracted product limits
to almost-everywhere age statements; stable fiber limits are identified using H02 uniqueness.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The initial cutoff sequence from which universal height cutoffs are extracted. -/
noncomputable def heightBaseEps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Initial cutoff positivity. -/
theorem heightBaseEps_pos (n : ℕ) : 0 < heightBaseEps n := by
  unfold heightBaseEps
  positivity

/-- The initial cutoffs strictly decrease. -/
theorem strictAnti_heightBaseEps : StrictAnti heightBaseEps := by
  intro i j hij
  unfold heightBaseEps
  exact one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.add_lt_add_right hij 1)

/-- The initial cutoffs tend to zero through positive values. -/
theorem tendsto_heightBaseEps : Tendsto heightBaseEps atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall heightBaseEps_pos⟩

/-- Fixed almost sure limits are inherited by eventual subsequences. -/
theorem ae_tendsto_comp_of_eventual_subseq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u : ℕ → Ω → ℝ} {L : Ω → ℝ} {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hsub : ∃ N, ∀ k ≥ N, ∃ j, ψ k = φ j)
    (h : ∀ᵐ x ∂μ, Tendsto (fun k => u (φ k) x) atTop (𝓝 (L x))) :
    ∀ᵐ x ∂μ, Tendsto (fun k => u (ψ k) x) atTop (𝓝 (L x)) :=
  h.mono fun x hx => tendsto_comp_of_eventual_subseq (u := fun k => u k x) hφ hψ hsub hx

/-- Existence of almost sure finite limits is inherited by eventual subsequences. -/
theorem ae_exists_tendsto_comp_of_eventual_subseq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {u : ℕ → Ω → ℝ} {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hsub : ∃ N, ∀ k ≥ N, ∃ j, ψ k = φ j)
    (h : ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun k => u (φ k) x) atTop (𝓝 L)) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun k => u (ψ k) x) atTop (𝓝 L) := by
  filter_upwards [h] with x hx
  obtain ⟨L, hL⟩ := hx
  exact ⟨L, tendsto_comp_of_eventual_subseq (u := fun k => u k x) hφ hψ hsub hL⟩

/-- Extraction at almost every age under the stable law, with H02's identified limit. -/
theorem exists_height_stable_age_subseq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) S), ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        Tendsto (fun k => heightApprox (heightBaseEps (φ (ψ k))) f s.toNNReal) atTop
          (𝓝 (height θ f s.toNNReal)) := by
  obtain ⟨M, _, hM⟩ := exists_heightApprox_tendstoInMeasure_stable_ages hθ S
  have hcut := tendsto_heightBaseEps.comp hφ.tendsto_atTop
  obtain ⟨ψ, hψ, hlim⟩ := (hM.comp hcut).exists_seq_tendsto_ae
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hlim] with s hs
  have hknown := (heightApprox_tendstoInMeasure hθ s.toNNReal).comp
    (hcut.comp hψ.tendsto_atTop)
  have hm : TendstoInMeasure (stableLocalLaw θ : Measure DLoc)
      (fun k f => heightApprox (heightBaseEps (φ (ψ k))) f s.toNNReal)
      atTop (fun f => M (s, f)) :=
    tendstoInMeasure_of_tendsto_ae (fun k =>
      (measurable_heightApprox_uncurry.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable) hs
  have heq := tendstoInMeasure_ae_unique hknown hm
  filter_upwards [hs, heq] with f hf he
  rw [he]
  exact hf

/-- Extraction on a surviving excursion age window, with its own restricted product law. -/
theorem exists_height_excursion_age_subseq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) S),
        ∀ᵐ e ∂(excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime},
          ∃ L : ℝ, Tendsto (fun k =>
            heightApprox (heightBaseEps (φ (ψ k))) e.path s.toNNReal) atTop (𝓝 L) := by
  have := sigmaFinite_excursionMeasure hθ
  obtain ⟨M, _, hM⟩ := exists_heightApprox_tendstoInMeasure_excursion_ages hθ S
  obtain ⟨ψ, hψ, hlim⟩ :=
    (hM.comp (tendsto_heightBaseEps.comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
  rw [heightExcursionAgeMeasure] at hlim
  have hfull := (ae_restrict_iff' measurableSet_heightExcursionAge_survival).mp hlim
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hfull] with s hs
  apply (ae_restrict_iff' (measurableSet_lt measurable_const measurable_excursion_lifetime)).mpr
  filter_upwards [hs] with e he
  intro heAlive
  exact ⟨M (s, e), he heAlive⟩

/-- Extraction on the unit-law age window, with its own finite product law. -/
theorem exists_height_unit_age_subseq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
        ∃ L : ℝ, Tendsto (fun k =>
          heightApprox (heightBaseEps (φ (ψ k))) e.path s.toNNReal) atTop (𝓝 L) := by
  obtain ⟨M, _, hM⟩ := exists_heightApprox_tendstoInMeasure_unit_ages hθ
  obtain ⟨ψ, hψ, hlim⟩ :=
    (hM.comp (tendsto_heightBaseEps.comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hlim] with s hs
  exact hs.mono fun e he => ⟨M (s, e), he⟩

end BGW.StableTrees
