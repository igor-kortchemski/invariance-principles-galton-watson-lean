/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcess
public import BGW.StableTrees.ExcursionMeasure
public import BGW.StableTrees.UnitExcursionLaw

/-!
# Universal height sequence: definitions and deterministic properties

The sequence interface records rational-age and almost-everywhere-age convergence under all laws.
The totalized limsup is measurable, nonnegative, and depends literally on the prefix.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- `ε` is positive, strictly decreasing to `0`, and along it the approximations converge almost
surely at every rational time: to H02's height under the stable law, and to some limit under
`N` on `{q < ζ}` and under the unit law at ages `q < 1`; the same holds at Lebesgue-almost every
age (needed by H04's locality at the random ages `q - g`). -/
def IsUniversalHeightSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 < ε k) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
  (∀ q : ℚ, 0 ≤ q → ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
    Tendsto (fun k => heightApprox (ε k) f (q : ℝ).toNNReal) atTop
      (𝓝 (height θ f (q : ℝ).toNNReal))) ∧
  (∀ q : ℚ, 0 < q →
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | (q : ℝ).toNNReal < e.lifetime}),
      ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path (q : ℝ).toNNReal) atTop (𝓝 L)) ∧
  (∀ q : ℚ, 0 < q → q < 1 → ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
    ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path (q : ℝ).toNNReal) atTop (𝓝 L)) ∧
  (∀ S : ℝ≥0, ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))),
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun k => heightApprox (ε k) f s.toNNReal) atTop (𝓝 (height θ f s.toNNReal))) ∧
  (∀ S : ℝ≥0, ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))),
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime}),
      ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path s.toNNReal) atTop (𝓝 L)) ∧
  (∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
    ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path s.toNNReal) atTop (𝓝 L))

open scoped Classical in
/-- The chosen universal sequence (junk `1/(k+1)` only if none exists). -/
noncomputable def heightEps (θ : ℝ) : ℕ → ℝ :=
  if h : ∃ ε : ℕ → ℝ, IsUniversalHeightSeq θ ε then Classical.choose h
  else fun k => 1 / ((k : ℝ) + 1)

/-- **The height read along the universal sequence** (a real limsup; junk where it diverges). -/
noncomputable def heightUniv (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  limsup (fun k => heightApprox (heightEps θ k) f t) atTop

/-- Every chosen cutoff is positive, including the fallback sequence. -/
theorem heightEps_pos (θ : ℝ) (k : ℕ) : 0 < heightEps θ k := by
  classical
  unfold heightEps
  split_ifs with h
  · exact (Classical.choose_spec h).1 k
  · positivity

/-- Joint measurability of the universal height. -/
theorem measurable_heightUniv_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1) := by
  exact Measurable.limsup fun k => measurable_heightApprox_uncurry.comp
    (measurable_const.prodMk measurable_id)

/-- `heightUniv θ f 0 = 0` for every path. -/
theorem heightUniv_zero (θ : ℝ) (f : DLoc) : heightUniv θ f 0 = 0 := by
  simp [heightUniv, heightApprox_zero]

/-- `heightUniv` is nonnegative for every path. -/
theorem heightUniv_nonneg (θ : ℝ) (f : DLoc) (t : ℝ≥0) : 0 ≤ heightUniv θ f t := by
  unfold heightUniv
  have hn (k : ℕ) : 0 ≤ heightApprox (heightEps θ k) f t :=
    mul_nonneg (inv_nonneg.mpr (heightEps_pos θ k).le) ENNReal.toReal_nonneg
  rw [limsup_eq_toReal_of_nonneg hn]
  exact ENNReal.toReal_nonneg

/-- Agreement of compact prefixes implies agreement of every contained approximation. -/
theorem heightApprox_eq_of_restrict_eq (ε : ℝ) (T : ℝ≥0) (f g : DLoc)
    (hfg : DLoc.restrict T f = DLoc.restrict T g) (t : ℝ≥0) (ht : t ≤ T) :
    heightApprox ε f t = heightApprox ε g t := by
  have heval (u : ℝ≥0) (hu : u ≤ T) : f.1 u = g.1 u :=
    congrArg (fun p : D (T : ℝ) ℝ => p ⟨u, u.2, hu⟩) hfg
  have hinf (s : ℝ≥0) : futureInf f t s = futureInf g t s := by
    unfold futureInf
    congr 1
    funext u
    exact heval u (u.2.2.trans ht)
  unfold heightApprox
  congr 3
  ext s
  simp only [mem_ofPred_eq]
  by_cases hs : 0 ≤ s ∧ s ≤ (t : ℝ)
  · rw [heval s.toNNReal ((Real.toNNReal_le_iff_le_coe.mpr hs.2).trans ht), hinf]
  · tauto

/-- **Literal prefix locality**: `heightUniv θ f t` reads `f` only on `[0,t]`. -/
theorem heightUniv_eq_of_restrict_eq (θ : ℝ) (T : ℝ≥0) (f g : DLoc)
    (hfg : DLoc.restrict T f = DLoc.restrict T g) (t : ℝ≥0) (ht : t ≤ T) :
    heightUniv θ f t = heightUniv θ g t := by
  unfold heightUniv
  congr 1
  funext k
  exact heightApprox_eq_of_restrict_eq _ T f g hfg t ht

end BGW.StableTrees

