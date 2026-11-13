/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeGerm
public import BGW.StableTrees.SupremumAuxLocalTimeConditional
import BGW.StableTrees.StableLocalMarkov

/-!
# The auxiliary clock germ event

The extended occupation limsup is monotone on every path. This makes immediate positivity a
raw-prefix event at every positive horizon, hence an event of the right-continuous germ.
The potential has already been constructed independently of the zero-one argument.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Immediate positivity of the extended helper is measurable in the germ sigma-algebra. -/
theorem measurableSet_supAuxGermClock_positive (θ : ℝ) :
    MeasurableSet[DLoc.filtration 0] {f : DLoc | ∀ n : ℕ,
      0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))} := by
  have he (u : ℝ≥0) (hu : 0 < u) :
      {f : DLoc | ∀ n : ℕ, 0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))} =
        ⋂ n : {n : ℕ // 1 / ((n : ℝ≥0) + 1) < u},
          {f : DLoc | 0 < supAuxGermClock θ f (1 / ((n.1 : ℝ≥0) + 1))} := by
    ext f
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro hf n
      exact hf n.1
    · intro hf k
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt
        (lt_min hu (by positivity : (0 : ℝ≥0) < 1 / ((k : ℝ≥0) + 1)))
      have hnu := hn.trans_le (min_le_left _ _)
      have hnk := hn.le.trans (min_le_right _ _)
      exact (hf ⟨n, hnu⟩).trans_le (monotone_supAuxGermClock θ f hnk)
  rw [DLoc.filtration, Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro u
  rw [MeasurableSpace.measurableSet_iInf]
  intro hu
  rw [he u hu]
  apply MeasurableSet.iInter
  intro n
  have hm := (measurable_rawFiltration_supAuxGermClock θ (1 / ((n.1 : ℝ≥0) + 1))).mono
    (DLoc.rawFiltration.mono n.2.le) le_rfl
  exact measurableSet_lt measurable_const hm

/-- Blumenthal's law applies to the extended helper's immediate-positivity event. -/
theorem measure_supAuxGermClock_positive_zeroOne {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc) {f | ∀ n : ℕ,
      0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))} = 0 ∨
    (stableLocalLaw θ : Measure DLoc) {f | ∀ n : ℕ,
      0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))} = 1 :=
  measure_zeroOne_filtration_zero hθ (measurableSet_supAuxGermClock_positive θ)

end BGW.StableTrees
