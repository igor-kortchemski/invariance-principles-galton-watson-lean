/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesSequenceHelpers
public import BGW.StableTrees.HeightBridgesUniversalBasic

/-!
# Universal height sequence by predicates on subsequences

The six countable families retain their own laws. The common extraction diagonalizes
their convergence predicates, including the finite survival-restricted excursion age windows.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

private theorem ae_age_of_integer_windows {Q : ℝ → Prop}
    (hQ : ∀ n : ℕ, ∀ᵐ s : ℝ ∂volume.restrict
      (Ioo (0 : ℝ) (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ)), Q s) (S : ℝ≥0) :
    ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) S), Q s := by
  obtain ⟨n, hn⟩ := exists_nat_gt (S : ℝ)
  have hSn : (S : ℝ) ≤ (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    linarith only [hn]
  have hle : volume.restrict (Ioo (0 : ℝ) S) ≤
      volume.restrict (Ioo (0 : ℝ) (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ)) :=
    Measure.restrict_mono_set _ (show Ioo (0 : ℝ) S ⊆
      Ioo (0 : ℝ) (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) from
        fun _ hs => ⟨hs.1, hs.2.trans_le hSn⟩)
  exact (hQ n).filter_mono (ae_mono hle)

/-- A universal sequence exists (diagonal extraction from the in-measure statements).
The excursion age windows use the finite survival restriction of `volume ⊗ N`.
Joint limits are obtained by the Cauchy criterion, without choosing a family of fixed-age limits. -/
theorem exists_isUniversalHeightSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ ε : ℕ → ℝ, IsUniversalHeightSeq θ ε := by
  classical
  let QN := {q : ℚ // 0 < q}
  let QU := {q : ℚ // 0 < q ∧ q < 1}
  let I := (ℚ ⊕ QN) ⊕ (QU ⊕ (ℕ ⊕ (ℕ ⊕ Unit)))
  let Good : I → (ℕ → ℕ) → Prop := fun i φ => match i with
    | .inl (.inl q) => ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        Tendsto (fun k => heightApprox (heightBaseEps (φ k)) f (q : ℝ).toNNReal)
          atTop (𝓝 (height θ f (q : ℝ).toNNReal))
    | .inl (.inr q) =>
        ∀ᵐ e ∂(excursionMeasure θ).restrict {e : Excursion | (q.1 : ℝ).toNNReal < e.lifetime},
          ∃ L : ℝ, Tendsto (fun k =>
            heightApprox (heightBaseEps (φ k)) e.path (q.1 : ℝ).toNNReal) atTop (𝓝 L)
    | .inr (.inl q) => ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
        ∃ L : ℝ, Tendsto (fun k =>
          heightApprox (heightBaseEps (φ k)) e.path (q.1 : ℝ).toNNReal) atTop (𝓝 L)
    | .inr (.inr (.inl n)) => ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) ((n : ℝ≥0) + 1)),
        ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
          Tendsto (fun k => heightApprox (heightBaseEps (φ k)) f s.toNNReal)
            atTop (𝓝 (height θ f s.toNNReal))
    | .inr (.inr (.inr (.inl n))) =>
        ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) ((n : ℝ≥0) + 1)),
          ∀ᵐ e ∂(excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime},
            ∃ L : ℝ, Tendsto (fun k =>
              heightApprox (heightBaseEps (φ k)) e.path s.toNNReal) atTop (𝓝 L)
    | .inr (.inr (.inr (.inr _))) => ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
        ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
          ∃ L : ℝ, Tendsto (fun k =>
            heightApprox (heightBaseEps (φ k)) e.path s.toNNReal) atTop (𝓝 L)
  have htail (i : I) (φ ψ : ℕ → ℕ) (hφ : StrictMono φ) (hψ : StrictMono ψ)
      (hsub : ∃ N, ∀ k ≥ N, ∃ j, ψ k = φ j) : Good i φ → Good i ψ := by
    rcases i with ((q | q) | (q | (n | (n | u))))
    · exact ae_tendsto_comp_of_eventual_subseq
        (μ := (stableLocalLaw θ : Measure DLoc))
        (u := fun n (f : DLoc) => heightApprox (heightBaseEps n) f (q : ℝ).toNNReal)
        (L := fun f => height θ f (q : ℝ).toNNReal) hφ hψ hsub
    · exact ae_exists_tendsto_comp_of_eventual_subseq
        (μ := (excursionMeasure θ).restrict {e : Excursion | (q.1 : ℝ).toNNReal < e.lifetime})
        (u := fun n (e : Excursion) =>
          heightApprox (heightBaseEps n) e.path (q.1 : ℝ).toNNReal) hφ hψ hsub
    · exact ae_exists_tendsto_comp_of_eventual_subseq
        (μ := (unitExcursionLaw θ : Measure Excursion))
        (u := fun n (e : Excursion) =>
          heightApprox (heightBaseEps n) e.path (q.1 : ℝ).toNNReal) hφ hψ hsub
    · intro h
      filter_upwards [h] with s hs
      exact ae_tendsto_comp_of_eventual_subseq
        (μ := (stableLocalLaw θ : Measure DLoc))
        (u := fun n (f : DLoc) => heightApprox (heightBaseEps n) f s.toNNReal)
        (L := fun f => height θ f s.toNNReal) hφ hψ hsub hs
    · intro h
      filter_upwards [h] with s hs
      exact ae_exists_tendsto_comp_of_eventual_subseq
        (μ := (excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime})
        (u := fun n (e : Excursion) => heightApprox (heightBaseEps n) e.path s.toNNReal)
        hφ hψ hsub hs
    · intro h
      filter_upwards [h] with s hs
      exact ae_exists_tendsto_comp_of_eventual_subseq
        (μ := (unitExcursionLaw θ : Measure Excursion))
        (u := fun n (e : Excursion) => heightApprox (heightBaseEps n) e.path s.toNNReal)
        hφ hψ hsub hs
  have hext (i : I) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
      ∃ ψ, StrictMono ψ ∧ Good i (φ ∘ ψ) := by
    have hcut := tendsto_heightBaseEps.comp hφ.tendsto_atTop
    rcases i with ((q | q) | (q | (n | (n | u))))
    · exact ((heightApprox_tendstoInMeasure hθ (q : ℝ).toNNReal).comp hcut).exists_seq_tendsto_ae
    · have hq : 0 < (q.1 : ℝ).toNNReal :=
        Real.toNNReal_pos.mpr (by exact_mod_cast q.2)
      obtain ⟨L, _, hL⟩ := exists_heightApprox_tendstoInMeasure_excursion hθ _ hq
      obtain ⟨ψ, hψ, hlim⟩ := (hL.comp hcut).exists_seq_tendsto_ae
      exact ⟨ψ, hψ, hlim.mono fun e he => ⟨L e, he⟩⟩
    · have hq : 0 < (q.1 : ℝ).toNNReal :=
        Real.toNNReal_pos.mpr (by exact_mod_cast q.2.1)
      have hq1 : (q.1 : ℝ).toNNReal < 1 := by
        exact_mod_cast (show (((q.1 : ℝ).toNNReal : ℝ)) < 1 by
          rw [Real.coe_toNNReal _ (by exact_mod_cast q.2.1.le)]
          exact_mod_cast q.2.2)
      obtain ⟨L, _, hL⟩ := exists_heightApprox_tendstoInMeasure_unit hθ _ hq hq1
      obtain ⟨ψ, hψ, hlim⟩ := (hL.comp hcut).exists_seq_tendsto_ae
      exact ⟨ψ, hψ, hlim.mono fun e he => ⟨L e, he⟩⟩
    · exact exists_height_stable_age_subseq hθ ((n : ℝ≥0) + 1) φ hφ
    · exact exists_height_excursion_age_subseq hθ ((n : ℝ≥0) + 1) φ hφ
    · exact exists_height_unit_age_subseq hθ φ hφ
  obtain ⟨φ, hφ, hGood⟩ := exists_diagonal_subseq Good htail hext
  refine ⟨heightBaseEps ∘ φ, fun n => heightBaseEps_pos (φ n),
    strictAnti_heightBaseEps.comp_strictMono hφ,
    (tendsto_nhdsWithin_iff.mp tendsto_heightBaseEps).1.comp hφ.tendsto_atTop,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q _
    exact hGood (.inl (.inl q))
  · intro q hq
    exact hGood (.inl (.inr ⟨q, hq⟩))
  · intro q hq hq1
    exact hGood (.inr (.inl ⟨q, hq, hq1⟩))
  · exact ae_age_of_integer_windows (fun n => hGood (.inr (.inr (.inl n))))
  · exact ae_age_of_integer_windows (fun n => hGood (.inr (.inr (.inr (.inl n)))))
  · exact hGood (.inr (.inr (.inr (.inr ()))))

/-- The chosen universal cutoffs satisfy the full sequence specification. -/
theorem isUniversalHeightSeq_heightEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsUniversalHeightSeq θ (heightEps θ) := by
  classical
  have h := exists_isUniversalHeightSeq hθ
  unfold heightEps
  rw [dite_eq_left h]
  exact Classical.choose_spec h

end BGW.StableTrees
