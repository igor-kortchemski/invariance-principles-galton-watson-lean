/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightBasic

/-!
# Exact cancellation of the occupation before an excursion start

A valid excursion cut adds no new minimum before its start. Splitting the occupation at
the start therefore gives an exact additive identity for every cutoff, including zero.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Extending a horizon inside a valid cut leaves all pre-start future infima unchanged. -/
theorem futureInf_eq_before_cut {g d : ℝ≥0} {f : DLoc} (hcut : cutValid g d f)
    {u s : ℝ≥0} (hu : u ≤ d - g) (hs : s ≤ g) :
    futureInf f (g + u) s = futureInf f g s := by
  have hgu : g + u ≤ d := by
    simpa only [add_comm] using (le_tsub_iff_right hcut.1.le).mp hu
  have hlow : f.1 g ≤ futureInf f (g + u) g := by
    let : Nonempty (Icc (min g (g + u)) (g + u)) :=
      ⟨⟨g + u, min_le_right _ _, le_rfl⟩⟩
    apply le_ciInf
    intro v
    exact hcut.2.2 v (by simpa using v.2.1) (v.2.2.trans hgu)
  rw [futureInf_split f hs (le_add_of_nonneg_right (show 0 ≤ u from zero_le))]
  exact min_eq_left ((futureInf_le_eval f g s g ⟨min_le_right _ _, le_rfl⟩).trans hlow)

/-- **Exact finite-cutoff cancellation** (deterministic): if the cut of `(T(x-), T(x))` is valid,
then for every cutoff `ε` and every age `u ≤ T(x) - T(x-)`, the host approximation at
`T(x-) + u` is the host approximation at `T(x-)` plus the approximation of the jump excursion at
age `u` (no correction term: the pre-start integrands coincide). -/
theorem heightApprox_jumpExcursion_add (ε : ℝ) (x : ℝ≥0) (f : DLoc)
    (hcut : cutValid (passageTimeMinus x f) (passageTime x f) f) {u : ℝ≥0}
    (hu : u ≤ passageTime x f - passageTimeMinus x f) :
    heightApprox ε f (passageTimeMinus x f + u) =
      heightApprox ε f (passageTimeMinus x f) + heightApprox ε (jumpExcursion x f).path u := by
  let g := passageTimeMinus x f
  let d := passageTime x f
  have hgu : g + u ≤ d := by
    simpa only [add_comm] using (le_tsub_iff_right hcut.1.le).mp hu
  have hpaths : DLoc.restrict u (DLoc.shift g f) =
      DLoc.restrict u (jumpExcursion x f).path := by
    apply BGW.Skorokhod.ext
    intro t
    let v : ℝ≥0 := ⟨(t : ℝ), t.2.1⟩
    change f.1 (g + v) - f.1 g = (excursionCut g d f).path.1 v
    have he := excursionCut_eval (show cutValid g d f from hcut) v
    have htu : v ≤ u := t.2.2
    have htd : g + v ≤ d := (show g + v ≤ g + u from add_le_add le_rfl htu).trans hgu
    rw [min_eq_left htd] at he
    exact he.symm
  have hshift := heightApprox_eq_of_restrict_eq ε u _ _ hpaths u le_rfl
  have hsplit := heightApprox_sub_shift_eq ε f (g + u) g (by simp)
  rw [add_tsub_cancel_left, hshift] at hsplit
  have hvol : volume {s : ℝ | 0 ≤ s ∧ s < (g : ℝ) ∧
      f.1 s.toNNReal < futureInf f (g + u) s.toNNReal + ε} =
      volume {s : ℝ | 0 ≤ s ∧ s ≤ (g : ℝ) ∧
        f.1 s.toNNReal < futureInf f g s.toNNReal + ε} := by
    apply measure_congr
    filter_upwards [volume.ae_ne (g : ℝ)] with s hs
    by_cases hs0 : 0 ≤ s
    · by_cases hsg : s ≤ (g : ℝ)
      · have hsg' : s < (g : ℝ) := lt_of_le_of_ne hsg hs
        rw [futureInf_eq_before_cut hcut hu (Real.toNNReal_le_iff_le_coe.mpr hsg)]
        simp only [hs0, hsg, hsg', true_and]
        rfl
      · simp only [hs0, hsg, not_lt.mpr (not_le.mp hsg).le,
          false_and, and_false]
    · simp only [hs0, false_and]
  rw [hvol] at hsplit
  change heightApprox ε f (g + u) - heightApprox ε (jumpExcursion x f).path u =
    heightApprox ε f g at hsplit
  linarith only [hsplit]

/-- The chosen cutoffs approach zero from above, including the fallback parameter branch. -/
theorem heightEps_tendsto_nhdsWithin_zero (θ : ℝ) :
    Tendsto (heightEps θ) atTop (𝓝[>] (0 : ℝ)) := by
  have ht : Tendsto (heightEps θ) atTop (𝓝 0) := by
    unfold heightEps
    split_ifs with h
    · exact (Classical.choose_spec h).2.2.1
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (heightEps_pos θ)⟩

/-- **Raw height of a jump excursion** (deterministic): with a valid cut and a vanishing
pre-start approximation at `T(x-)`, the universal raw height of the excursion at age
`u ≤ T(x) - T(x-)` is the host's universal raw height at `T(x-) + u`. -/
theorem heightUniv_jumpExcursion_eq (θ : ℝ) (x : ℝ≥0) (f : DLoc)
    (hcut : cutValid (passageTimeMinus x f) (passageTime x f) f)
    (hpre : Tendsto (fun ε : ℝ => heightApprox ε f (passageTimeMinus x f)) (𝓝[>] (0 : ℝ))
      (𝓝 0))
    {u : ℝ≥0} (hu : u ≤ passageTime x f - passageTimeMinus x f) :
    heightUniv θ (jumpExcursion x f).path u = heightUniv θ f (passageTimeMinus x f + u) := by
  have hnon (g : DLoc) (t : ℝ≥0) (k : ℕ) : 0 ≤ heightApprox (heightEps θ k) g t :=
    mul_nonneg (inv_nonneg.mpr (heightEps_pos θ k).le) ENNReal.toReal_nonneg
  have hlim : Tendsto
      (fun k => ENNReal.ofReal (heightApprox (heightEps θ k) f (passageTimeMinus x f)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hpre.comp (heightEps_tendsto_nhdsWithin_zero θ))
  unfold heightUniv
  rw [limsup_eq_toReal_of_nonneg (hnon (jumpExcursion x f).path u),
    limsup_eq_toReal_of_nonneg (hnon f (passageTimeMinus x f + u))]
  have he (k : ℕ) :
      ENNReal.ofReal (heightApprox (heightEps θ k) f (passageTimeMinus x f + u)) =
        ENNReal.ofReal (heightApprox (heightEps θ k) f (passageTimeMinus x f)) +
          ENNReal.ofReal (heightApprox (heightEps θ k) (jumpExcursion x f).path u) := by
    rw [heightApprox_jumpExcursion_add _ x f hcut hu,
      ENNReal.ofReal_add (hnon f (passageTimeMinus x f) k)
        (hnon (jumpExcursion x f).path u k)]
  simp_rw [he]
  exact congrArg ENNReal.toReal (ENNReal.limsup_add_of_left_tendsto_zero hlim _).symm

end BGW.StableTrees
