/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessBasic

/-!
# Erasure of finite measures on heights

The tail quantile retains precisely the mass below the cut and the necessary part of its atom.
Continuity of measures identifies both sides of the cut, including complete erasure.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace BGW.StableTrees

private theorem tail_levels_nonempty {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ]
    {m : ℝ≥0∞} (hm : 0 < m) : {h : ℝ≥0 | ρ (Ioi h) ≤ m}.Nonempty := by
  have hmono : Antitone (fun n : ℕ => Ioi (n : ℝ≥0)) := by
    intro i j hij
    exact Ioi_subset_Ioi (by exact_mod_cast hij)
  have he : (⋂ n : ℕ, Ioi (n : ℝ≥0)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (x : ℝ)
    have hxn := mem_iInter.mp hx n
    exact (not_lt_of_ge hn.le) hxn
  have ht := tendsto_measure_iInter_atTop
    (μ := ρ) (fun _ : ℕ => measurableSet_Ioi.nullMeasurableSet) hmono
    ⟨0, measure_ne_top ρ _⟩
  simp only [he, measure_empty] at ht
  obtain ⟨n, hn⟩ := ((ht.eventually (eventually_lt_nhds hm)).exists)
  exact ⟨n, hn.le⟩

private theorem eraseCut_tail_le {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ]
    {m : ℝ≥0∞} (hm : 0 < m) : ρ (Ioi (eraseCut m ρ)) ≤ m := by
  let c := eraseCut m ρ
  let d : ℕ → ℝ≥0 := fun n => 1 / (n + 1 : ℝ≥0)
  have hd : Antitone d := by
    intro i j hij
    dsimp [d]
    gcongr
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdt : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmono : Monotone (fun n => Ioi (c + d n)) := by
    intro i j hij
    exact Ioi_subset_Ioi (add_le_add (le_refl c) (hd hij))
  have he : (⋃ n, Ioi (c + d n)) = Ioi c := by
    ext x
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact (lt_add_of_pos_right c (hdpos n)).trans hn
    · intro hx
      have ht : Tendsto (fun n => c + d n) atTop (𝓝 c) := by
        simpa using tendsto_const_nhds.add hdt
      exact (ht.eventually (eventually_lt_nhds hx)).exists
  rw [← he, hmono.measure_iUnion]
  apply iSup_le
  intro n
  have hc : c < c + d n := lt_add_of_pos_right c (hdpos n)
  obtain ⟨a, ha, han⟩ := (csInf_lt_iff (OrderBot.bddBelow _)
    (tail_levels_nonempty hm)).mp hc
  exact (measure_mono (Ioi_subset_Ioi han.le)).trans ha

private theorem eraseCut_mass_ge {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ]
    {m : ℝ≥0∞} (hm : m ≤ ρ univ) : m ≤ ρ (Ici (eraseCut m ρ)) := by
  let c := eraseCut m ρ
  by_cases hc : c = 0
  · have he : Ici c = univ := by
      ext x
      simp only [mem_Ici, hc, mem_univ, iff_true]
      exact zero_le
    change m ≤ ρ (Ici c)
    rw [he]
    exact hm
  have hcpos : 0 < c := pos_iff_ne_zero.mpr hc
  let d : ℕ → ℝ≥0 := fun n => 1 / (n + 1 : ℝ≥0)
  have hd : Antitone d := by
    intro i j hij
    dsimp [d]
    gcongr
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdt : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n => c - d n) atTop (𝓝 c) := by
    simpa only [tsub_zero] using (tendsto_const_nhds (x := c)).sub hdt
  have hmono : Antitone (fun n => Ioi (c - d n)) := by
    intro i j hij
    exact Ioi_subset_Ioi (tsub_le_tsub_left (hd hij) c)
  have he : (⋂ n, Ioi (c - d n)) = Ici c := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_Ici]
    constructor
    · intro hx
      exact le_of_tendsto ht (Eventually.of_forall fun n => (hx n).le)
    · intro hx n
      exact (tsub_lt_self hcpos (hdpos n)).trans_le hx
  rw [← he, hmono.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet)
    ⟨0, measure_ne_top ρ _⟩]
  apply le_iInf
  intro n
  by_contra hn
  have hmem : ρ (Ioi (c - d n)) ≤ m := (not_le.mp hn).le
  have hcut : c ≤ c - d n := csInf_le (OrderBot.bddBelow _) hmem
  exact (not_le_of_gt (tsub_lt_self hcpos (hdpos n))) hcut

private theorem mass_partition (ρ : Measure ℝ≥0) (c : ℝ≥0) :
    ρ (Iio c) + ρ (Ici c) = ρ univ := by
  simpa only [compl_Iio] using measure_add_measure_compl (μ := ρ) measurableSet_Iio

/-- Erasing at most the total (finite) mass removes exactly that mass. -/
theorem eraseMass_univ {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ] {m : ℝ≥0∞} (hm : m ≤ ρ univ) :
    eraseMass m ρ univ = ρ univ - m := by
  by_cases hm0 : m = 0
  · simp [hm0, eraseMass_zero]
  have hmf : m ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top ρ univ) hm
  have hb := eraseCut_mass_ge hm
  rw [eraseMass, ite_eq_right hm0]
  simp only [Measure.add_apply, Measure.restrict_apply_univ, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [add_comm, ENNReal.sub_add_eq_add_sub hb hmf,
    add_comm (ρ (Ici (eraseCut m ρ))), mass_partition]

/-- Distribution-function characterization of erasure (includes `m ≥ ρ univ` and `m = ⊤`). -/
theorem eraseMass_Iic {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ] (m : ℝ≥0∞) (h : ℝ≥0) :
    eraseMass m ρ (Iic h) = min (ρ (Iic h)) (ρ univ - m) := by
  by_cases hm0 : m = 0
  · simp only [hm0, eraseMass_zero, tsub_zero]
    exact (min_eq_left (measure_mono (subset_univ _))).symm
  by_cases hm : m ≤ ρ univ
  · have hmf : m ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top ρ univ) hm
    by_cases hh : h < eraseCut m ρ
    · have htail : m ≤ ρ (Ioi h) := by
        by_contra hn
        have hc : eraseCut m ρ ≤ h := csInf_le' ((not_le.mp hn).le)
        exact (not_le_of_gt hh) hc
      have hpart : ρ (Iic h) + ρ (Ioi h) = ρ univ := by
        simpa only [compl_Iic] using measure_add_measure_compl (μ := ρ) measurableSet_Iic
      have hle : ρ (Iic h) ≤ ρ univ - m :=
        ENNReal.le_sub_of_add_le_right hmf (by
          rw [← hpart]
          exact add_le_add le_rfl htail)
      rw [min_eq_left hle, eraseMass, ite_eq_right hm0]
      have hi : Iic h ∩ Iio (eraseCut m ρ) = Iic h := by
        exact inter_eq_left.mpr (fun _ hx => hx.trans_lt hh)
      simp [Measure.add_apply, Measure.restrict_apply measurableSet_Iic, hi,
        Measure.smul_apply, Measure.dirac_apply', not_le.mpr hh]
    · have hch : eraseCut m ρ ≤ h := le_of_not_gt hh
      have htail : ρ (Ioi h) ≤ m :=
        (measure_mono (Ioi_subset_Ioi hch)).trans (eraseCut_tail_le (pos_iff_ne_zero.mpr hm0))
      have hpart : ρ (Iic h) + ρ (Ioi h) = ρ univ := by
        simpa only [compl_Iic] using measure_add_measure_compl (μ := ρ) measurableSet_Iic
      have hle : ρ univ - m ≤ ρ (Iic h) := tsub_le_iff_right.mpr (by
        rw [← hpart]
        exact add_le_add le_rfl htail)
      rw [min_eq_right hle, ← eraseMass_univ hm]
      have hi : Iic h ∩ Iio (eraseCut m ρ) = Iio (eraseCut m ρ) :=
        inter_eq_right.mpr (fun _ hx => hx.le.trans hch)
      simp [eraseMass, hm0, Measure.add_apply, Measure.restrict_apply measurableSet_Iic,
        hi, Measure.smul_apply, Measure.dirac_apply', hch]
  · have htot : ρ univ ≤ m := (not_le.mp hm).le
    have hc : eraseCut m ρ = 0 := le_antisymm
      (csInf_le' ((measure_mono (subset_univ _)).trans htot)) zero_le
    simp [eraseMass, hm0, hc, tsub_eq_zero_of_le htot]

end BGW.StableTrees
