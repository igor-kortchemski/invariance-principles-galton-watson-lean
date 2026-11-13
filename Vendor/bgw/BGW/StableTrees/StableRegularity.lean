/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLocShiftAt
public import BGW.StableTrees.StableStrongMarkov

import BGW.StableTrees.StableDensityAPI
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Two-sided regularity of zero for the stable process

Right-continuity identifies the positive- and negative-time regularity events with the vanishing
of strict passage times. Stable scaling gives a fixed positive lower bound on each approximating
passage event; continuity from above and the germ zero-one law then give almost sure regularity.
The strong Markov property transfers the result to finite stopping times (J. Bertoin, *Lévy
Processes*, Cambridge University Press, 1996, Chapter VII, Corollary 5, for the spectrally positive
case).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.Skorokhod.DLoc

/-- `0` is regular for `(-∞, 0)`: the path takes negative values in every `(0, ε)`. -/
def RegularBelowAtZero (f : DLoc) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ DLoc.eval t f < 0

/-- `0` is regular for `(0, ∞)`: the path takes positive values in every `(0, ε)`. -/
def RegularAboveAtZero (f : DLoc) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < DLoc.eval t f

private theorem passageBelow_eq_zero_of_forall_lt {f : DLoc}
    (h : ∀ ε : ℝ≥0, 0 < ε → strictPassageBelow 0 f < (ε : ℝ≥0∞)) :
    strictPassageBelow 0 f = 0 := by
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro ε hε hεp
  exact (not_lt_of_ge (h ε hε).le hεp).elim

private theorem passageAbove_eq_zero_of_forall_lt {f : DLoc}
    (h : ∀ ε : ℝ≥0, 0 < ε → strictPassageAbove 0 f < (ε : ℝ≥0∞)) :
    strictPassageAbove 0 f = 0 := by
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro ε hε hεp
  exact (not_lt_of_ge (h ε hε).le hεp).elim

private theorem passageBelow_lt_of_regular {f : DLoc} (h : RegularBelowAtZero f)
    {ε : ℝ≥0} (hε : 0 < ε) : strictPassageBelow 0 f < (ε : ℝ≥0∞) := by
  obtain ⟨t, -, htε, hval⟩ := h ε hε
  apply iInf_lt_iff.mpr
  exact ⟨t, iInf_lt_iff.mpr ⟨hval, WithTop.coe_lt_coe.mpr htε⟩⟩

private theorem passageAbove_lt_of_regular {f : DLoc} (h : RegularAboveAtZero f)
    {ε : ℝ≥0} (hε : 0 < ε) : strictPassageAbove 0 f < (ε : ℝ≥0∞) := by
  obtain ⟨t, -, htε, hval⟩ := h ε hε
  apply iInf_lt_iff.mpr
  exact ⟨t, iInf_lt_iff.mpr ⟨hval, WithTop.coe_lt_coe.mpr htε⟩⟩

private theorem exists_time_of_passageAbove_lt {f : DLoc} {ε : ℝ≥0}
    (h : strictPassageAbove 0 f < (ε : ℝ≥0∞)) :
    ∃ t : ℝ≥0, t < ε ∧ 0 < f.1 t := by
  obtain ⟨q, hq0, hqε, hval⟩ := (strictPassageAbove_lt_iff 0 f ε).mp h
  have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  refine ⟨Real.toNNReal q, ?_, hval⟩
  have h : (Real.toNNReal q : ℝ) < (ε : ℝ) := by
    rwa [Real.coe_toNNReal q hq0R]
  exact_mod_cast h

private theorem exists_time_of_passageBelow_lt {f : DLoc} {ε : ℝ≥0}
    (h : strictPassageBelow 0 f < (ε : ℝ≥0∞)) :
    ∃ t : ℝ≥0, t < ε ∧ f.1 t < 0 := by
  let g : DLoc := ⟨fun t => -f.1 t, f.2.continuous_comp continuous_neg⟩
  have hpass : strictPassageAbove 0 g < (ε : ℝ≥0∞) := by
    rw [← show strictPassageBelow (-0) f = strictPassageAbove 0 g by
      simpa [g] using strictPassageBelow_neg 0 f]
    simpa using h
  obtain ⟨t, htε, hval⟩ := exists_time_of_passageAbove_lt hpass
  exact ⟨t, htε, by simpa [g] using (neg_pos.mp hval)⟩

private theorem regularBelow_iff_passageBelow_eq_zero (f : DLoc) :
    RegularBelowAtZero f ↔ strictPassageBelow 0 f = 0 := by
  constructor
  · exact fun h => passageBelow_eq_zero_of_forall_lt fun _ hε => passageBelow_lt_of_regular h hε
  · intro h ε hε
    have hpass : strictPassageBelow 0 f < (ε : ℝ≥0∞) := by
      rw [h]
      exact WithTop.coe_pos.mpr hε
    obtain ⟨t, htε, hval⟩ := exists_time_of_passageBelow_lt hpass
    rcases eq_or_ne t 0 with ht | ht
    · subst t
      have hneg : ∀ᶠ u in 𝓝[Set.Ioi 0] (0 : ℝ≥0), f.1 u < 0 :=
        (f.2.isRightContinuous 0).eventually (isOpen_Iio.mem_nhds hval)
      have hlt : ∀ᶠ u in 𝓝[Set.Ioi 0] (0 : ℝ≥0), u < ε :=
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds htε)
      have hpos : ∀ᶠ u in 𝓝[Set.Ioi 0] (0 : ℝ≥0), 0 < u := self_mem_nhdsWithin
      obtain ⟨u, hu, huε, hu0⟩ := (hneg.and (hlt.and hpos)).exists
      exact ⟨u, hu0, huε, hu⟩
    · exact ⟨t, pos_iff_ne_zero.mpr ht, htε, hval⟩

private theorem regularAbove_iff_passageAbove_eq_zero (f : DLoc) :
    RegularAboveAtZero f ↔ strictPassageAbove 0 f = 0 := by
  constructor
  · exact fun h => passageAbove_eq_zero_of_forall_lt fun _ hε => passageAbove_lt_of_regular h hε
  · intro h ε hε
    have hpass : strictPassageAbove 0 f < (ε : ℝ≥0∞) := by
      rw [h]
      exact WithTop.coe_pos.mpr hε
    obtain ⟨t, htε, hval⟩ := exists_time_of_passageAbove_lt hpass
    rcases eq_or_ne t 0 with ht | ht
    · subst t
      have hposval : ∀ᶠ u in 𝓝[Set.Ioi 0] (0 : ℝ≥0), 0 < f.1 u :=
        (f.2.isRightContinuous 0).eventually (isOpen_Ioi.mem_nhds hval)
      have hlt : ∀ᶠ u in 𝓝[Set.Ioi 0] (0 : ℝ≥0), u < ε :=
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds htε)
      have hpos : ∀ᶠ u in 𝓝[Set.Ioi 0] (0 : ℝ≥0), 0 < u := self_mem_nhdsWithin
      obtain ⟨u, hu, huε, hu0⟩ := (hposval.and (hlt.and hpos)).exists
      exact ⟨u, hu0, huε, hu⟩
    · exact ⟨t, pos_iff_ne_zero.mpr ht, htε, hval⟩

private theorem passageBelow_zero_eq_iInter {u : ℝ≥0} (hu : 0 < u) :
    {f : DLoc | strictPassageBelow 0 f = 0} =
      ⋂ n : {n : ℕ // 1 / ((n : ℝ≥0) + 1) < u},
        {f : DLoc | strictPassageBelow 0 f < ((1 / ((n.1 : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)} := by
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro h n
    rw [h]
    exact WithTop.coe_pos.mpr (by positivity)
  · intro h
    apply passageBelow_eq_zero_of_forall_lt
    intro ε hε
    by_cases hεu : ε < u
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ≥0) hε
      exact h ⟨n, hn.trans hεu⟩ |>.trans (WithTop.coe_lt_coe.mpr hn)
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ≥0) hu
      exact h ⟨n, hn⟩ |>.trans_le (WithTop.coe_le_coe.mpr (hn.le.trans (le_of_not_gt hεu)))

private theorem passageAbove_zero_eq_iInter {u : ℝ≥0} (hu : 0 < u) :
    {f : DLoc | strictPassageAbove 0 f = 0} =
      ⋂ n : {n : ℕ // 1 / ((n : ℝ≥0) + 1) < u},
        {f : DLoc | strictPassageAbove 0 f < ((1 / ((n.1 : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)} := by
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro h n
    rw [h]
    exact WithTop.coe_pos.mpr (by positivity)
  · intro h
    apply passageAbove_eq_zero_of_forall_lt
    intro ε hε
    by_cases hεu : ε < u
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ≥0) hε
      exact h ⟨n, hn.trans hεu⟩ |>.trans (WithTop.coe_lt_coe.mpr hn)
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ≥0) hu
      exact h ⟨n, hn⟩ |>.trans_le (WithTop.coe_le_coe.mpr (hn.le.trans (le_of_not_gt hεu)))

private theorem regularBelow_set_eq_iInter :
    {f : DLoc | RegularBelowAtZero f} =
      ⋂ n : ℕ, {f : DLoc | strictPassageBelow 0 f <
        ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)} := by
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · exact fun h n => passageBelow_lt_of_regular h (by positivity)
  · intro h
    apply (regularBelow_iff_passageBelow_eq_zero f).2
    apply passageBelow_eq_zero_of_forall_lt
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ≥0) hε
    exact (h n).trans (WithTop.coe_lt_coe.mpr hn)

private theorem regularAbove_set_eq_iInter :
    {f : DLoc | RegularAboveAtZero f} =
      ⋂ n : ℕ, {f : DLoc | strictPassageAbove 0 f <
        ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)} := by
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · exact fun h n => passageAbove_lt_of_regular h (by positivity)
  · intro h
    apply (regularAbove_iff_passageAbove_eq_zero f).2
    apply passageAbove_eq_zero_of_forall_lt
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ≥0) hε
    exact (h n).trans (WithTop.coe_lt_coe.mpr hn)

private theorem measurableSet_germ_regularBelow :
    MeasurableSet[DLoc.filtration 0] {f : DLoc | RegularBelowAtZero f} := by
  rw [show {f : DLoc | RegularBelowAtZero f} = {f | strictPassageBelow 0 f = 0} by
    ext f
    exact regularBelow_iff_passageBelow_eq_zero f]
  rw [DLoc.filtration, Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro u
  rw [MeasurableSpace.measurableSet_iInf]
  intro hu
  rw [passageBelow_zero_eq_iInter hu]
  apply MeasurableSet.iInter
  intro n
  let r : ℝ≥0 := 1 / ((n.1 : ℝ≥0) + 1)
  have hru : r < u := n.2
  have hle : DLoc.filtration r ≤ DLoc.rawFiltration u := by
    rw [DLoc.filtration, Filtration.rightCont_eq]
    exact iInf₂_le_of_le u hru le_rfl
  exact hle _ ((isStoppingTime_strictPassageBelow 0).measurableSet_lt r)

private theorem measurableSet_germ_regularAbove :
    MeasurableSet[DLoc.filtration 0] {f : DLoc | RegularAboveAtZero f} := by
  rw [show {f : DLoc | RegularAboveAtZero f} = {f | strictPassageAbove 0 f = 0} by
    ext f
    exact regularAbove_iff_passageAbove_eq_zero f]
  rw [DLoc.filtration, Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro u
  rw [MeasurableSpace.measurableSet_iInf]
  intro hu
  rw [passageAbove_zero_eq_iInter hu]
  apply MeasurableSet.iInter
  intro n
  let r : ℝ≥0 := 1 / ((n.1 : ℝ≥0) + 1)
  have hru : r < u := n.2
  have hle : DLoc.filtration r ≤ DLoc.rawFiltration u := by
    rw [DLoc.filtration, Filtration.rightCont_eq]
    exact iInf₂_le_of_le u hru le_rfl
  exact hle _ ((isStoppingTime_strictPassageAbove 0).measurableSet_lt r)

/-- The negative regularity event is measurable. -/
theorem measurableSet_regularBelowAtZero : MeasurableSet {f : DLoc | RegularBelowAtZero f} :=
  DLoc.filtration.le 0 _ measurableSet_germ_regularBelow

/-- The positive regularity event is measurable. -/
theorem measurableSet_regularAboveAtZero : MeasurableSet {f : DLoc | RegularAboveAtZero f} :=
  DLoc.filtration.le 0 _ measurableSet_germ_regularAbove

/-- The negative regularity event is germ-measurable. -/
theorem measurableSet_filtration_zero_regularBelowAtZero :
    MeasurableSet[DLoc.filtration 0] {f : DLoc | RegularBelowAtZero f} :=
  measurableSet_germ_regularBelow

/-- The positive regularity event is germ-measurable. -/
theorem measurableSet_filtration_zero_regularAboveAtZero :
    MeasurableSet[DLoc.filtration 0] {f : DLoc | RegularAboveAtZero f} :=
  measurableSet_germ_regularAbove

end BGW.Skorokhod.DLoc

namespace BGW.StableTrees

private theorem stableLaw_Iio_zero_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    0 < (stableLaw θ : Measure ℝ) (Set.Iio 0) := by
  let d : ℝ → ℝ := Scalar.stableDensity θ
  have hd : Continuous d := Scalar.continuous_stableDensity hθ
  have hd0 : 0 < d 0 := Scalar.stableDensity_zero_pos hθ
  have hev : ∀ᶠ x in 𝓝 0, 0 < d x :=
    hd.continuousAt.eventually (isOpen_Ioi.mem_nhds hd0)
  have hleft : ∀ᶠ x in 𝓝[Set.Iio 0] 0, 0 < d x :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx, hx0⟩ := (hleft.and self_mem_nhdsWithin).exists
  have hmeas : Measurable (fun x => ENNReal.ofReal (d x)) :=
    ENNReal.measurable_ofReal.comp hd.measurable
  have hnonempty : (Function.support (fun x => ENNReal.ofReal (d x)) ∩ Set.Iio 0).Nonempty := by
    refine ⟨x, ?_, hx0⟩
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  rw [stableLaw_eq_withDensity hθ, withDensity_apply _ measurableSet_Iio]
  exact (setLIntegral_pos_iff hmeas).2
    (((ENNReal.continuous_ofReal.comp hd).isOpen_support.inter isOpen_Iio).measure_pos
      volume hnonempty)

private theorem stableLaw_Ioi_zero_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    0 < (stableLaw θ : Measure ℝ) (Set.Ioi 0) := by
  let d : ℝ → ℝ := Scalar.stableDensity θ
  have hd : Continuous d := Scalar.continuous_stableDensity hθ
  have hd0 : 0 < d 0 := Scalar.stableDensity_zero_pos hθ
  have hev : ∀ᶠ x in 𝓝 0, 0 < d x :=
    hd.continuousAt.eventually (isOpen_Ioi.mem_nhds hd0)
  have hright : ∀ᶠ x in 𝓝[Set.Ioi 0] 0, 0 < d x :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx, hx0⟩ := (hright.and self_mem_nhdsWithin).exists
  have hmeas : Measurable (fun x => ENNReal.ofReal (d x)) :=
    ENNReal.measurable_ofReal.comp hd.measurable
  have hnonempty : (Function.support (fun x => ENNReal.ofReal (d x)) ∩ Set.Ioi 0).Nonempty := by
    refine ⟨x, ?_, hx0⟩
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  rw [stableLaw_eq_withDensity hθ, withDensity_apply _ measurableSet_Ioi]
  exact (setLIntegral_pos_iff hmeas).2
    (((ENNReal.continuous_ofReal.comp hd).isOpen_support.inter isOpen_Ioi).measure_pos
      volume hnonempty)

private theorem stableLawAt_Iio {θ t : ℝ} (ht : 0 < t) :
    (stableLawAt θ t : Measure ℝ) (Set.Iio 0) = (stableLaw θ : Measure ℝ) (Set.Iio 0) := by
  rw [stableLawAt]
  change Measure.map (fun x => t ^ (1 / θ) * x) (stableLaw θ : Measure ℝ) (Set.Iio 0) = _
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  congr 1
  ext x
  simp [Real.rpow_pos_of_pos ht _]

private theorem stableLawAt_Ioi {θ t : ℝ} (ht : 0 < t) :
    (stableLawAt θ t : Measure ℝ) (Set.Ioi 0) = (stableLaw θ : Measure ℝ) (Set.Ioi 0) := by
  rw [stableLawAt]
  change Measure.map (fun x => t ^ (1 / θ) * x) (stableLaw θ : Measure ℝ) (Set.Ioi 0) = _
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext x
  simp [Real.rpow_pos_of_pos ht _]

private theorem measure_eval_Iio {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc) {f | DLoc.eval t f < 0} =
      (stableLaw θ : Measure ℝ) (Set.Iio 0) := by
  calc
    _ = ((stableLocalLaw θ : Measure DLoc).map (DLoc.eval t)) (Set.Iio 0) := by
      rw [Measure.map_apply (DLoc.measurable_eval t) measurableSet_Iio]
      rfl
    _ = (stableLawAt θ (t : ℝ) : Measure ℝ) (Set.Iio 0) := by
      rw [map_eval_stableLocalLaw hθ ht]
    _ = _ := stableLawAt_Iio (by exact_mod_cast ht)

private theorem measure_eval_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc) {f | 0 < DLoc.eval t f} =
      (stableLaw θ : Measure ℝ) (Set.Ioi 0) := by
  calc
    _ = ((stableLocalLaw θ : Measure DLoc).map (DLoc.eval t)) (Set.Ioi 0) := by
      rw [Measure.map_apply (DLoc.measurable_eval t) measurableSet_Ioi]
      rfl
    _ = (stableLawAt θ (t : ℝ) : Measure ℝ) (Set.Ioi 0) := by
      rw [map_eval_stableLocalLaw hθ ht]
    _ = _ := stableLawAt_Ioi (by exact_mod_cast ht)

private theorem stableLaw_le_measure_passageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ≥0} (hε : 0 < ε) :
    (stableLaw θ : Measure ℝ) (Set.Iio 0) ≤
      (stableLocalLaw θ : Measure DLoc) {f | DLoc.strictPassageBelow 0 f < (ε : ℝ≥0∞)} := by
  let t : ℝ≥0 := ε / 2
  have ht : 0 < t := half_pos hε
  have htε : t < ε := half_lt_self hε
  calc
    _ = (stableLocalLaw θ : Measure DLoc) {f | DLoc.eval t f < 0} :=
      (measure_eval_Iio hθ ht).symm
    _ ≤ _ := by
      apply measure_mono
      intro f hf
      change DLoc.strictPassageBelow 0 f < (ε : ℝ≥0∞)
      change DLoc.eval t f < 0 at hf
      apply iInf_lt_iff.mpr
      exact ⟨t, iInf_lt_iff.mpr ⟨hf, WithTop.coe_lt_coe.mpr htε⟩⟩

private theorem stableLaw_le_measure_passageAbove {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ≥0} (hε : 0 < ε) :
    (stableLaw θ : Measure ℝ) (Set.Ioi 0) ≤
      (stableLocalLaw θ : Measure DLoc) {f | DLoc.strictPassageAbove 0 f < (ε : ℝ≥0∞)} := by
  let t : ℝ≥0 := ε / 2
  have ht : 0 < t := half_pos hε
  have htε : t < ε := half_lt_self hε
  calc
    _ = (stableLocalLaw θ : Measure DLoc) {f | 0 < DLoc.eval t f} :=
      (measure_eval_Ioi hθ ht).symm
    _ ≤ _ := by
      apply measure_mono
      intro f hf
      change DLoc.strictPassageAbove 0 f < (ε : ℝ≥0∞)
      change 0 < DLoc.eval t f at hf
      apply iInf_lt_iff.mpr
      exact ⟨t, iInf_lt_iff.mpr ⟨hf, WithTop.coe_lt_coe.mpr htε⟩⟩

private theorem measure_regularBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc) {f | DLoc.RegularBelowAtZero f} = 1 := by
  let P : Measure DLoc := stableLocalLaw θ
  let E : ℕ → Set DLoc := fun n => {f | DLoc.strictPassageBelow 0 f <
    ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    DLoc.filtration.le _ _ ((DLoc.isStoppingTime_strictPassageBelow 0).measurableSet_lt _)
  have hanti : Antitone E := by
    intro m n hmn f hf
    have hmn' : (m : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hmn
    have hfrac : 1 / ((n : ℝ≥0) + 1) ≤ 1 / ((m : ℝ≥0) + 1) :=
      one_div_le_one_div_of_le (by positivity) (add_le_add hmn' le_rfl)
    dsimp [E] at hf
    dsimp [E]
    exact hf.trans_le (WithTop.coe_le_coe.mpr hfrac)
  have hlim : P {f | DLoc.RegularBelowAtZero f} = ⨅ n, P (E n) := by
    rw [DLoc.regularBelow_set_eq_iInter]
    exact hanti.measure_iInter (fun n => (hEm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  have hbound : (stableLaw θ : Measure ℝ) (Set.Iio 0) ≤
      P {f | DLoc.RegularBelowAtZero f} := by
    rw [hlim]
    exact le_iInf fun n => stableLaw_le_measure_passageBelow hθ (by positivity)
  rcases measure_zeroOne_filtration_zero hθ
    DLoc.measurableSet_filtration_zero_regularBelowAtZero with hzero | hone
  · have hpos := (stableLaw_Iio_zero_pos hθ).trans_le hbound
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos).elim
  · exact hone

private theorem measure_regularAbove {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc) {f | DLoc.RegularAboveAtZero f} = 1 := by
  let P : Measure DLoc := stableLocalLaw θ
  let E : ℕ → Set DLoc := fun n => {f | DLoc.strictPassageAbove 0 f <
    ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    DLoc.filtration.le _ _ ((DLoc.isStoppingTime_strictPassageAbove 0).measurableSet_lt _)
  have hanti : Antitone E := by
    intro m n hmn f hf
    have hmn' : (m : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hmn
    have hfrac : 1 / ((n : ℝ≥0) + 1) ≤ 1 / ((m : ℝ≥0) + 1) :=
      one_div_le_one_div_of_le (by positivity) (add_le_add hmn' le_rfl)
    dsimp [E] at hf
    dsimp [E]
    exact hf.trans_le (WithTop.coe_le_coe.mpr hfrac)
  have hlim : P {f | DLoc.RegularAboveAtZero f} = ⨅ n, P (E n) := by
    rw [DLoc.regularAbove_set_eq_iInter]
    exact hanti.measure_iInter (fun n => (hEm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  have hbound : (stableLaw θ : Measure ℝ) (Set.Ioi 0) ≤
      P {f | DLoc.RegularAboveAtZero f} := by
    rw [hlim]
    exact le_iInf fun n => stableLaw_le_measure_passageAbove hθ (by positivity)
  rcases measure_zeroOne_filtration_zero hθ
    DLoc.measurableSet_filtration_zero_regularAboveAtZero with hzero | hone
  · have hpos := (stableLaw_Ioi_zero_pos hθ).trans_le hbound
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos).elim
  · exact hone

/-- **regularity of `0` for both half-lines.** Almost surely, for every `ε > 0` the path takes
a negative value and a positive value at times in `(0, ε)`. -/
theorem ae_regular_both_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.RegularBelowAtZero f ∧ DLoc.RegularAboveAtZero f := by
  filter_upwards [
    (ae_iff_measure_eq DLoc.measurableSet_regularBelowAtZero.nullMeasurableSet).2
      (by simpa using measure_regularBelow hθ),
    (ae_iff_measure_eq DLoc.measurableSet_regularAboveAtZero.nullMeasurableSet).2
      (by simpa using measure_regularAbove hθ)] with f hf hg
  exact ⟨hf, hg⟩

/-- Almost sure regularity of `0` for the negative half-line. -/
theorem ae_regularBelowAtZero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), DLoc.RegularBelowAtZero f :=
  (ae_regular_both_stableLocalLaw hθ).mono fun _ h => h.1

/-- Almost sure regularity of `0` for the positive half-line. -/
theorem ae_regularAboveAtZero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), DLoc.RegularAboveAtZero f :=
  (ae_regular_both_stableLocalLaw hθ).mono fun _ h => h.2

/-- **Regularity after a stopping time**, obtained from the strong Markov property. -/
theorem ae_regular_both_shiftAt_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : MeasureTheory.IsStoppingTime DLoc.filtration τ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤ →
      DLoc.RegularBelowAtZero (DLoc.shiftAt τ f) ∧ DLoc.RegularAboveAtZero (DLoc.shiftAt τ f) := by
  let P : Measure DLoc := stableLocalLaw θ
  let S : Set DLoc := {f | τ f < ⊤}
  let B : Set DLoc := {f | DLoc.RegularBelowAtZero f ∧ DLoc.RegularAboveAtZero f}
  have hB : MeasurableSet B :=
    DLoc.measurableSet_regularBelowAtZero.inter DLoc.measurableSet_regularAboveAtZero
  have haeP : ∀ᵐ f ∂P, f ∈ B := ae_regular_both_stableLocalLaw hθ
  have haeMap : ∀ᵐ f ∂((P.restrict S).map (DLoc.shiftAt τ)), f ∈ B := by
    rw [map_shiftAt_restrict_stableLocalLaw hθ hτ]
    exact Measure.ae_smul_measure haeP _
  have haeRes : ∀ᵐ f ∂P.restrict S, DLoc.shiftAt τ f ∈ B :=
    (ae_map_iff (DLoc.measurable_shiftAt hτ).aemeasurable hB).mp haeMap
  have hS : MeasurableSet S :=
    hτ.measurableSpace_le _ (DLoc.measurableSet_lt_top_stopped hτ)
  exact (ae_restrict_iff' hS).mp haeRes

/-- Almost surely both strict passage times at level zero vanish. -/
theorem ae_strictPassage_zero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.strictPassageAbove 0 f = 0 ∧ DLoc.strictPassageBelow 0 f = 0 := by
  filter_upwards [ae_regular_both_stableLocalLaw hθ] with f hf
  exact ⟨(DLoc.regularAbove_iff_passageAbove_eq_zero f).mp hf.2,
    (DLoc.regularBelow_iff_passageBelow_eq_zero f).mp hf.1⟩

end BGW.StableTrees
