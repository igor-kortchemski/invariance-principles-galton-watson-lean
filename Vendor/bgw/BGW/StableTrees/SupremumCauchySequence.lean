/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyL2

/-!
# A fast occupation sequence and its adapted raw limit

The cutoffs are chosen strictly within the compact Cauchy radii. The raw real limsup
preserves prefix measurability on every path.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- There exists a fast positive occupation sequence. -/
theorem exists_isSupAuxEpsSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) : ∃ ε : ℕ → ℝ, IsSupAuxEpsSeq θ ε := by
  have hc (k : ℕ) := supOccupation_compact_L2_cauchy hθ k ((1 / 16 : ℝ) ^ k)
    (by positivity)
  choose a ha hb using hc
  obtain ⟨u, hu, hupos, hu0⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hp : ∀ k n : ℕ, ∃ m : ℕ, n < m ∧ u m < a k := by
    intro k n
    exact ((eventually_gt_atTop n).and (hu0.eventually (Iio_mem_nhds (ha k)))).exists
  choose next hnext using hp
  let idx : ℕ → ℕ := Nat.rec (next 0 0) (fun k n => next (k + 1) n)
  have hi : StrictMono idx := strictMono_nat_of_lt_succ fun k => (hnext (k + 1) (idx k)).1
  have hs (k : ℕ) : u (idx k) < a k := by
    cases k with
    | zero => exact (hnext 0 0).2
    | succ k => exact (hnext (k + 1) (idx k)).2
  refine ⟨fun k => u (idx k), fun k => hupos _, fun i j hij => hu (hi hij),
    hu0.comp hi.tendsto_atTop, fun k η hη hηle => ?_⟩
  exact hb k _ η (hupos _) (hs k) hη (hηle.trans_lt (hs k))

open scoped Classical in
/-- The chosen fast sequence (junk `1/(k+1)` for `θ ∉ (1,2]`). -/
noncomputable def supAuxEps (θ : ℝ) : ℕ → ℝ :=
  if h : 1 < θ ∧ θ ≤ 2 then Classical.choose (exists_isSupAuxEpsSeq h)
  else fun k => 1 / ((k : ℝ) + 1)

/-- The selected sequence satisfies the fast Cauchy bounds. -/
theorem isSupAuxEpsSeq_supAuxEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsSupAuxEpsSeq θ (supAuxEps θ) := by
  simp only [supAuxEps, hθ, and_self, dite_true]
  exact Classical.choose_spec (exists_isSupAuxEpsSeq hθ)

/-- The auxiliary limit `M^*_t = limsup_k O_{ε_k}(t)` along `supAuxEps θ` (raw, real-valued,
adapted; the `limsup` keeps adaptedness by definition). -/
noncomputable def supAuxLimit (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  limsup (fun k => supOccupation (supAuxEps θ k) f t) atTop

/-- The raw auxiliary limit is jointly measurable for every index. -/
theorem measurable_supAuxLimit_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supAuxLimit θ p.2 p.1) := by
  exact measurable_supOccupation_limsup (supAuxEps θ)

/-- The raw auxiliary limit is strongly adapted for every index. -/
theorem stronglyAdapted_supAuxLimit (θ : ℝ) :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => supAuxLimit θ f t) := by
  intro t
  have hm : Measurable[DLoc.rawFiltration t] (fun f : DLoc => supAuxLimit θ f t) :=
    Measurable.limsup (fun k => measurable_rawFiltration_supOccupation (supAuxEps θ k) t)
  exact (hm.mono (DLoc.rawFiltration.le_rightCont t) le_rfl).stronglyMeasurable

end BGW.StableTrees
