/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeGermLaw
public import BGW.StableTrees.SupremumAuxLocalTimeScalingLaw

/-!
# Immediate positivity of the auxiliary clock

Scaling makes positivity probabilities independent of positive time. Continuity from above
identifies their common value with the germ event. The mean potential rules out value zero,
and Blumenthal's law then gives immediate positivity on one event.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The clock is measurable at each deterministic time, including exceptional paths. -/
theorem measurable_supAuxLocalTime_eval (θ : ℝ) (t : ℝ≥0) :
    Measurable (fun f : DLoc => supAuxLocalTime θ f t) := by
  have hc : Measurable (fun _ : DLoc => t) := measurable_const
  have hh := (measurable_supAuxLocalTime_uncurry θ).comp (hc.prodMk measurable_id)
  exact hh

/-- The probability of positive clock value is independent of positive time. -/
theorem measure_supAuxLocalTime_pos_eq_one_time {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc) {f | 0 < supAuxLocalTime θ f t} =
      (stableLocalLaw θ : Measure DLoc) {f | 0 < supAuxLocalTime θ f 1} := by
  let c : Ioi (0 : ℝ) := ⟨t, ht⟩
  have he := congrArg (fun μ : Measure ℝ => μ (Ioi 0))
    (map_supAuxLocalTime_scaling hθ c t)
  have hd : 0 < (c : ℝ) / (c : ℝ) ^ (1 / θ) :=
    div_pos c.2 (Real.rpow_pos_of_pos c.2 _)
  have hT : t / (c : ℝ).toNNReal = 1 := by
    change t / ((t : ℝ).toNNReal) = 1
    rw [Real.toNNReal_coe, div_self ht.ne']
  have hsm : Measurable (fun f : DLoc => ((c : ℝ) / (c : ℝ) ^ (1 / θ)) *
      supAuxLocalTime θ f (t / (c : ℝ).toNNReal)) := by
    exact (measurable_supAuxLocalTime_eval θ (t / (c : ℝ).toNNReal)).const_mul _
  rw [Measure.map_apply (measurable_supAuxLocalTime_eval θ t) measurableSet_Ioi,
    Measure.map_apply hsm measurableSet_Ioi, hT] at he
  have hs : (fun f : DLoc => ((c : ℝ) / (c : ℝ) ^ (1 / θ)) * supAuxLocalTime θ f 1) ⁻¹'
      Ioi (0 : ℝ) = {f | 0 < supAuxLocalTime θ f 1} := by
    ext f
    exact mul_pos_iff_of_pos_left hd
  rw [hs] at he
  exact he

/-- The unit-time clock is positive with nonzero probability, by the mean potential. -/
theorem measure_supAuxLocalTime_one_pos_ne_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc) {f | 0 < supAuxLocalTime θ f 1} ≠ 0 := by
  intro hz
  have hn (n : ℕ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supAuxLocalTime θ f (n + 1) ≤ 0 := by
    apply ae_iff.mpr
    simpa only [not_le] using (measure_supAuxLocalTime_pos_eq_one_time hθ
      (t := (n : ℝ≥0) + 1) (by positivity)).trans hz
  have hall : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t, supAuxLocalTime θ f t = 0 := by
    filter_upwards [ae_all_iff.mpr hn, ae_supAuxLocalTime_continuous hθ,
      ae_supAuxLocalTime_nonneg hθ] with f hf hm hp
    intro t
    obtain ⟨n, hnt⟩ := exists_nat_ge t
    apply le_antisymm _ (hp t)
    exact (hm.2.1 (hnt.trans (by simp))).trans (hf n)
  have htail : supAuxDiscountedTail θ 1 0 =ᵐ[(stableLocalLaw θ : Measure DLoc)] 0 := by
    filter_upwards [hall, ae_supAuxLocalTime_continuous hθ] with f hf hm
    have hs : supAuxStieltjes θ f = 0 := by
      ext s
      exact (pathStieltjes_apply ⟨hm.2.1, hm.2.2⟩ s).trans (hf s.toNNReal)
    simp only [supAuxDiscountedTail, hs, StieltjesFunction.measure_zero,
      Measure.restrict_zero, integral_zero_measure,
      Pi.zero_apply]
  have hmean := integral_supAuxDiscountedTail_zero hθ (q := 1) zero_lt_one
  rw [integral_eq_zero_of_ae htail, supPotential_zero hθ zero_lt_one] at hmean
  norm_num at hmean

/-- The extended-helper germ event has the same mass as unit-time clock positivity. -/
theorem measure_supAuxGermClock_positive_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc) {f | ∀ n : ℕ,
      0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))} =
      (stableLocalLaw θ : Measure DLoc) {f | 0 < supAuxLocalTime θ f 1} := by
  let P : Measure DLoc := stableLocalLaw θ
  let E : ℕ → Set DLoc := fun n => {f | 0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))}
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have hm := (measurable_rawFiltration_supAuxGermClock θ (1 / ((n : ℝ≥0) + 1))).mono
      (DLoc.rawFiltration.le _) le_rfl
    exact measurableSet_lt measurable_const hm
  have hanti : Antitone E := by
    intro n m hnm f hf
    have ht : 1 / ((m : ℝ≥0) + 1) ≤ 1 / ((n : ℝ≥0) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact hf.trans_le (monotone_supAuxGermClock θ f ht)
  have hm (n : ℕ) : P (E n) = P {f | 0 < supAuxLocalTime θ f 1} := by
    calc
      _ = P {f | 0 < supAuxLocalTime θ f (1 / ((n : ℝ≥0) + 1))} := by
        apply measure_congr
        filter_upwards [ae_supAuxGermClock_eq hθ] with f hf
        exact propext (by simp only [E, mem_ofPred_eq, hf, ENNReal.ofReal_pos])
      _ = _ := measure_supAuxLocalTime_pos_eq_one_time hθ (by positivity)
  have hl := tendsto_measure_iInter_atTop (fun n => (hE n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P (E 0)⟩
  have hc : (P ∘ E) = fun _ : ℕ => P {f | 0 < supAuxLocalTime θ f 1} := funext hm
  rw [hc] at hl
  have he := tendsto_nhds_unique hl tendsto_const_nhds
  have hset : (⋂ n, E n) = {f | ∀ n : ℕ,
      0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))} := by
    ext f
    simp only [mem_iInter, E, mem_ofPred_eq]
  rw [hset] at he
  exact he

/-- **Immediate increase**: `L^aux_t > 0` for every `t > 0`, almost surely. -/
theorem ae_supAuxLocalTime_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0, 0 < t → 0 < supAuxLocalTime θ f t := by
  have hmass : (stableLocalLaw θ : Measure DLoc) {f | ∀ n : ℕ,
      0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1))} = 1 := by
    rcases measure_supAuxGermClock_positive_zeroOne hθ with hz | ho
    · exact False.elim (measure_supAuxLocalTime_one_pos_ne_zero hθ
        ((measure_supAuxGermClock_positive_eq hθ).symm.trans hz))
    · exact ho
  have hmeas := DLoc.filtration.le 0 _ (measurableSet_supAuxGermClock_positive θ)
  have hae : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ n : ℕ,
      0 < supAuxGermClock θ f (1 / ((n : ℝ≥0) + 1)) :=
    (mem_ae_iff_prob_eq_one hmeas).mpr hmass
  filter_upwards [hae, ae_supAuxGermClock_eq hθ, ae_supAuxLocalTime_continuous hθ]
    with f hf he hm
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
  have hp : 0 < supAuxLocalTime θ f (1 / ((n : ℝ≥0) + 1)) := by
    apply ENNReal.ofReal_pos.mp
    rw [← he]
    exact hf n
  exact hp.trans_le (hm.2.1 hn.le)

end BGW.StableTrees
