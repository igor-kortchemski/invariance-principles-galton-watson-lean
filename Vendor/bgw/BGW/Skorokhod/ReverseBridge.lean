/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ReverseIncrements

/-!
# Reversal of a pinned bridge path

The bridge reversal evaluates to the negative of the left limit at the reversed time.  Unlike
reversal of increments, it does not subtract the terminal value; on paths ending at zero the two
operations coincide (J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996,
Chapter II, Lemma 2, for the reversal of increments).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace BGW.Skorokhod

private theorem tendsto_leftLim_nhdsGT_bridge {α : Type*} [LinearOrder α] [TopologicalSpace α]
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

/-- The bridge reversal function `s ↦ -f((1-s)-)`, defined on every path of `D 1 ℝ` (with
`f(0-) = f 0`). On paths with `f 1 = 0` it agrees with `reverseIncrementsFun` at `T = 1`; it
preserves positive jumps (the sign flips together with the time). -/
noncomputable def reverseBridgeFun (f : D 1 ℝ) : Set.Icc (0 : ℝ) 1 → ℝ :=
  fun s => -Function.leftLim f ⟨1 - s, by linarith [s.2.2], by linarith [s.2.1]⟩

/-- The reversed function is càdlàg, including at both endpoints. -/
theorem isCadlag_reverseBridgeFun (f : D 1 ℝ) : IsCadlag (reverseBridgeFun f) := by
  let r : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := fun u =>
    ⟨1 - u, by linarith [u.2.2], by linarith [u.2.1]⟩
  have hr (u : Set.Icc (0 : ℝ) 1) : Tendsto r (𝓝 u) (𝓝 (r u)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [r] using tendsto_const_nhds.sub continuous_subtype_val.continuousAt
  change IsCadlag (fun u => -Function.leftLim f (r u))
  constructor
  · intro u
    have hrev : Tendsto r (𝓝[>] u) (𝓝[≤] r u) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hr u).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      apply Subtype.coe_le_coe.mpr
      change 1 - (v : ℝ) ≤ 1 - (u : ℝ)
      exact sub_le_sub_left hv.le 1
    have hleft := continuousWithinAt_leftLim_Iic
      ((isCadlag f).tendsto_nhdsLT_leftLim (r u))
    exact (hleft.tendsto.comp hrev).neg
  · intro u
    refine ⟨-f (r u), ?_⟩
    have hrev : Tendsto r (𝓝[<] u) (𝓝[>] r u) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hr u).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      apply Subtype.coe_lt_coe.mpr
      change 1 - (v : ℝ) > 1 - (u : ℝ)
      exact sub_lt_sub_left hv 1
    exact (tendsto_leftLim_nhdsGT_bridge
      ((isCadlag f).isRightContinuous (r u)).tendsto |>.comp hrev).neg

/-- The bridge reversal as a totalized map on `D 1 ℝ`. -/
noncomputable def reverseBridge (f : D 1 ℝ) : D 1 ℝ :=
  ⟨reverseBridgeFun f, isCadlag_reverseBridgeFun f⟩

/-- Pointwise formula (definitional). -/
theorem reverseBridge_apply (f : D 1 ℝ) (s : Set.Icc (0 : ℝ) 1) :
    reverseBridge f s =
      -Function.leftLim f ⟨1 - s, by linarith [s.2.2], by linarith [s.2.1]⟩ := rfl

/-- Agreement with the increment reversal on paths ending at `0`. -/
theorem reverseBridge_eq_reverseIncrements {f : D 1 ℝ} (hf : f ⟨1, zero_le_one, le_rfl⟩ = 0) :
    reverseBridge f = reverseIncrements zero_le_one f := by
  ext s
  rw [reverseBridge_apply, reverseIncrements_apply, hf, zero_sub]

/-- `reverseBridge` is Borel measurable. -/
theorem measurable_reverseBridge : Measurable reverseBridge := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap reverseBridge (inferInstance : MeasurableSpace (D 1 ℝ)) ≤
    (inferInstance : MeasurableSpace (D 1 ℝ))
  conv_lhs =>
    rw [measurableSpace_eq_iSup_comap_eval (T := 1) (E := ℝ) (S := Set.univ)
      dense_univ zero_le_one (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro u _hu
  exact (measurable_leftLim_eval _).neg.comap_le

/-- Left limits transform reversal into evaluation at the reversed time, provided the original
path has no terminal jump. -/
theorem leftLim_reverseBridge (f : D 1 ℝ)
    (hf : f ⟨1, zero_le_one, le_rfl⟩ = Function.leftLim f ⟨1, zero_le_one, le_rfl⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    Function.leftLim (reverseBridge f) t =
      -f ⟨1 - t, by linarith [t.2.2], by linarith [t.2.1]⟩ := by
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext ht
    subst t
    rw [leftLim_eq_of_isBot (f := reverseBridge f) (fun u => u.2.1), reverseBridge_apply]
    simp only [sub_zero]
    rw [← hf]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    let r : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := fun u =>
      ⟨1 - u, by linarith [u.2.2], by linarith [u.2.1]⟩
    have hr (u : Set.Icc (0 : ℝ) 1) : Tendsto r (𝓝 u) (𝓝 (r u)) := by
      apply tendsto_subtype_rng.mpr
      simpa only [r] using tendsto_const_nhds.sub continuous_subtype_val.continuousAt
    have hrev : Tendsto r (𝓝[<] t) (𝓝[>] r t) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hr t).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      apply Subtype.coe_lt_coe.mpr
      change 1 - (v : ℝ) > 1 - (t : ℝ)
      exact sub_lt_sub_left hv 1
    let z : Set.Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
    have hz : z < t := htpos
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
    apply leftLim_eq_of_tendsto
    change Tendsto (fun u => -Function.leftLim f (r u)) (𝓝[<] t) (𝓝 (-f (r t)))
    simpa only [Function.comp_def] using (tendsto_leftLim_nhdsGT_bridge
      ((isCadlag f).isRightContinuous (r t)).tendsto |>.comp hrev).neg

end BGW.Skorokhod
