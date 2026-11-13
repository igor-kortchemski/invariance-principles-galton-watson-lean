/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.MeasurableMaps

/-!
# Reversal of increments on Skorokhod space

The reversed-increment path evaluates to `f T - f ((T-u)-)`. Its càdlàg property
uses left-continuity of the left-limit function and right-continuity of the original path.
The map is the one of the duality lemma in J. Bertoin, *Lévy Processes*, Cambridge University
Press, 1996, Chapter II, Lemma 2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace BGW.Skorokhod

private theorem tendsto_leftLim_nhdsGT {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {g : α → ℝ} {a : α} (h : Tendsto g (𝓝[>] a) (𝓝 (g a))) :
    Tendsto (Function.leftLim g) (𝓝[>] a) (𝓝 (g a)) := by
  apply (closed_nhds_basis (g a)).tendsto_right_iff.2
  rintro S ⟨hS, hclosed⟩
  rcases eq_or_neBot (𝓝[>] a) with hbot | hne
  · simp [hbot]
  obtain ⟨b, hb⟩ : (Set.Ioi a).Nonempty :=
    Filter.nonempty_of_mem (self_mem_nhdsWithin : Set.Ioi a ∈ 𝓝[>] a)
  obtain ⟨c, hac, hc⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb).mp (h.eventually hS)
  filter_upwards [Ioo_mem_nhdsGT hac] with x hx
  apply hclosed.mem_of_mapClusterPt (mapClusterPt_leftLim g x)
  filter_upwards [Ioo_mem_nhdsLE_of_mem hx] with y hy using hc hy

/-- The reversed-increment function `u ↦ f T - f ((T-u)-)`. -/
noncomputable def reverseIncrementsFun {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    Set.Icc (0 : ℝ) T → ℝ :=
  fun u =>
    f ⟨T, hT, le_rfl⟩ -
      Function.leftLim f ⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩

/-- The reversed path is càdlàg, including at both endpoints. -/
theorem isCadlag_reverseIncrementsFun {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    IsCadlag (reverseIncrementsFun hT f) := by
  let r : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) T := fun u =>
    ⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩
  have hr (u : Set.Icc (0 : ℝ) T) : Tendsto r (𝓝 u) (𝓝 (r u)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [r] using tendsto_const_nhds.sub continuous_subtype_val.continuousAt
  change IsCadlag (fun u => f ⟨T, hT, le_rfl⟩ - Function.leftLim f (r u))
  constructor
  · intro u
    have hrev : Tendsto r (𝓝[>] u) (𝓝[≤] r u) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hr u).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      apply Subtype.coe_le_coe.mpr
      change T - (v : ℝ) ≤ T - (u : ℝ)
      exact sub_le_sub_left hv.le T
    have hleft := continuousWithinAt_leftLim_Iic
      ((isCadlag f).tendsto_nhdsLT_leftLim (r u))
    exact tendsto_const_nhds.sub (hleft.tendsto.comp hrev)
  · intro u
    refine ⟨f ⟨T, hT, le_rfl⟩ - f (r u), ?_⟩
    have hrev : Tendsto r (𝓝[<] u) (𝓝[>] r u) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hr u).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      apply Subtype.coe_lt_coe.mpr
      change T - (v : ℝ) > T - (u : ℝ)
      exact sub_lt_sub_left hv T
    exact tendsto_const_nhds.sub
      ((tendsto_leftLim_nhdsGT ((isCadlag f).isRightContinuous (r u)).tendsto).comp hrev)

/-- The time reversal of increments `R f (u) = f T - f ((T-u)-)`, with `f (0-) = f 0`. -/
noncomputable def reverseIncrements {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) : D T ℝ :=
  ⟨reverseIncrementsFun hT f, isCadlag_reverseIncrementsFun hT f⟩

/-- Pointwise formula (definitional). -/
theorem reverseIncrements_apply {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) (u : Set.Icc (0 : ℝ) T) :
    reverseIncrements hT f u =
      f ⟨T, hT, le_rfl⟩ -
        Function.leftLim f ⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩ := rfl

/-- `reverseIncrements` is Borel measurable. -/
theorem measurable_reverseIncrements {T : ℝ} (hT : 0 ≤ T) :
    Measurable (reverseIncrements hT) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (reverseIncrements hT)
      (inferInstance : MeasurableSpace (D T ℝ)) ≤
    (inferInstance : MeasurableSpace (D T ℝ))
  conv_lhs =>
    rw [measurableSpace_eq_iSup_comap_eval (T := T) (E := ℝ) (S := Set.univ)
      dense_univ hT (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro u _hu
  have hm : Measurable (fun f : D T ℝ =>
      f ⟨T, hT, le_rfl⟩ -
        Function.leftLim f ⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩) :=
    (measurable_eval_top hT).sub (measurable_leftLim_eval _)
  exact hm.comap_le

end BGW.Skorokhod
