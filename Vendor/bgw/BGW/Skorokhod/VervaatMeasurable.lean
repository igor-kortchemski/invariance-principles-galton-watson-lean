/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.VervaatRotate
public import BGW.Skorokhod.MeasurableCylinders
import BGW.Skorokhod.MeasurableExtrema
import BGW.Skorokhod.Restrict

/-!
# Measurability of the càdlàg Vervaat map

The first minimizing time is measurable because its sublevel sets are equality
sets between prefix infima and the global infimum. Joint evaluation then gives
measurability of the rotated path.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace BGW.Skorokhod

private theorem leftLim_restrict (f : D 1 ℝ) (a : Icc (0 : ℝ) 1)
    (t : Icc (0 : ℝ) (a : ℝ)) :
    Function.leftLim (restrict a.2.2 f) t =
      Function.leftLim f ⟨t, t.2.1, t.2.2.trans a.2.2⟩ := by
  by_cases ht : (t : ℝ) = 0
  · have hbot : IsBot t := fun s => by change (t : ℝ) ≤ s; rw [ht]; exact s.2.1
    have hbot' : IsBot (⟨t, t.2.1, t.2.2.trans a.2.2⟩ : Icc (0 : ℝ) 1) :=
      fun s => by change (t : ℝ) ≤ s; rw [ht]; exact s.2.1
    rw [leftLim_eq_of_isBot hbot, leftLim_eq_of_isBot hbot']
    rfl
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have : (𝓝[<] t).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨⟨0, le_rfl, a.2.1⟩, htpos⟩
    let inc : Icc (0 : ℝ) (a : ℝ) → Icc (0 : ℝ) 1 :=
      fun s => ⟨s, s.2.1, s.2.2.trans a.2.2⟩
    have hc : Continuous inc := continuous_subtype_val.subtype_mk _
    apply leftLim_eq_of_tendsto
    apply ((isCadlag f).tendsto_nhdsLT_leftLim (inc t)).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs

private theorem prefix_inf_eq_restrict (f : D 1 ℝ) (a : Icc (0 : ℝ) 1) :
    (⨅ t : Iic a, f t) = ⨅ t, restrict a.2.2 f t := by
  let : Nonempty (Icc (0 : ℝ) (a : ℝ)) := ⟨⟨0, le_rfl, a.2.1⟩⟩
  have hb := (isBounded_range f).bddBelow
  have hbp : BddBelow (range (fun t : Iic a => f t)) :=
    hb.mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  have hbr := (isBounded_range (restrict a.2.2 f)).bddBelow
  apply le_antisymm
  · apply le_ciInf
    intro t
    exact ciInf_le hbp ⟨⟨t, t.2.1, t.2.2.trans a.2.2⟩, t.2.2⟩
  · apply le_ciInf
    intro t
    exact ciInf_le hbr ⟨t, t.1.2.1, t.2⟩

/-- A prefix contains the first minimizing time exactly when its infimum is global. -/
theorem vervaatTime_le_iff_prefix_inf (f : D 1 ℝ) (a : Icc (0 : ℝ) 1) :
    vervaatTime f ≤ a ↔ (⨅ t : Iic a, f t) = ⨅ t, f t := by
  have hb := (isBounded_range f).bddBelow
  have hbp : BddBelow (range (fun t : Iic a => f t)) :=
    hb.mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  constructor
  · intro hle
    apply le_antisymm
    · rw [← min_leftLim_vervaatTime f]
      apply le_min
      · apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f (vervaatTime f))
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact ciInf_le hbp ⟨s, hs.trans hle⟩
      · exact ciInf_le hbp ⟨vervaatTime f, hle⟩
    · exact le_ciInf fun t => ciInf_le hb t
  · intro heq
    obtain ⟨t, ht⟩ := exists_min_leftLim (restrict a.2.2 f) a.2.1
    rw [leftLim_restrict, ← prefix_inf_eq_restrict, heq] at ht
    exact (vervaatTime_le f ht).trans t.2.2

/-- The canonical first minimum time is measurable, including at paths with tied minima. -/
@[fun_prop] theorem measurable_vervaatTime : Measurable vervaatTime := by
  apply measurable_of_Iic
  intro a
  have heq : vervaatTime ⁻¹' Iic a =
      {f : D 1 ℝ | (⨅ t : Iic a, f t) = ⨅ t, f t} := by
    ext f
    exact vervaatTime_le_iff_prefix_inf f a
  rw [heq]
  exact measurableSet_eq_fun (measurable_iInf_eval (ordConnected_Iic))
    ((lipschitzWith_one_iInf zero_le_one).continuous.measurable)

/-- The càdlàg Vervaat map is Borel (C33.4). -/
theorem measurable_vervaatD : Measurable vervaatD := by
  classical
  have heval (t : Icc (0 : ℝ) 1) : Measurable (fun f : D 1 ℝ => vervaatD f t) := by
    have hg : Measurable (fun f : D 1 ℝ => (vervaatTime f : ℝ)) :=
      measurable_vervaatTime.subtype_coe
    have ha : Measurable (fun f : D 1 ℝ =>
        projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)) :=
      continuous_projIcc.measurable.comp (hg.add_const (t : ℝ))
    have hb : Measurable (fun f : D 1 ℝ =>
        projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1)) :=
      continuous_projIcc.measurable.comp ((hg.add_const (t : ℝ)).sub_const 1)
    have hm : Measurable (fun f : D 1 ℝ => ⨅ s, f s) :=
      (lipschitzWith_one_iInf zero_le_one).continuous.measurable
    exact Measurable.ite (measurableSet_le (hg.add_const (t : ℝ)) measurable_const)
      ((measurable_eval₂.comp (measurable_id.prodMk ha)).sub hm)
      ((((measurable_eval₂.comp (measurable_id.prodMk hb)).add
        (measurable_eval ⟨1, zero_le_one, le_rfl⟩)).sub hm).sub
        (measurable_eval ⟨0, le_rfl, zero_le_one⟩))
  apply Measurable.of_comap_le
  have hspace : (instMeasurableSpace : MeasurableSpace (D 1 ℝ)) =
      ⨆ t : Icc (0 : ℝ) 1, MeasurableSpace.comap (fun f : D 1 ℝ => f t)
        (inferInstance : MeasurableSpace ℝ) := by
    simpa only [mem_univ, iSup_pos] using
      (measurableSpace_eq_iSup_comap_eval (T := 1) (E := ℝ) (S := univ)
        dense_univ zero_le_one (mem_univ _))
  conv_lhs => rw [hspace]
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro t
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, inferInstance] using
    (heval t).comap_le

end BGW.Skorokhod
