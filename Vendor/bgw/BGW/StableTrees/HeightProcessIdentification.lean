/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessErasure
import BGW.Skorokhod.JumpDetection

/-!
# Fixed-time height approximation

Reversal identifies occupation approximations outside the countable set of jumps.
Prefix events transport along the equality of restricted-path laws, yielding both
almost sure convergence along the public sequence and convergence in measure.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

private theorem ae_leftLim_eq_on_interval (f : DLoc) (t : ℝ≥0) :
    ∀ᵐ s : ℝ ∂volume, 0 ≤ s → s ≤ (t : ℝ) →
      Function.leftLim f.1 s.toNNReal = f.1 s.toNNReal := by
  let A : ℕ → Set ℝ≥0 := fun n => {s | s ≤ t ∧ 1 / (n + 1 : ℝ) < jumpSize f.1 s}
  have hA (n : ℕ) : (A n).Countable :=
    (finite_setOf_jump_gt_cadlag f.2 (by positivity) t).countable
  have hK := (countable_iUnion hA).image (fun s : ℝ≥0 => (s : ℝ))
  filter_upwards [hK.ae_notMem volume] with s hs hs0 hst
  by_contra hne
  have hpos : 0 < jumpSize f.1 s.toNNReal := by
    exact abs_pos.mpr (sub_ne_zero.mpr (fun he => hne he.symm))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  apply hs
  refine ⟨s.toNNReal, mem_iUnion.mpr ⟨n, ?_⟩, Real.coe_toNNReal _ hs0⟩
  exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hst, hn⟩

/-- Occupation reversal holds pathwise for paths with nonnegative jumps. -/
theorem heightApprox_eq_supOccupation_reversed (f : DLoc)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r) (t : ℝ≥0) (ε : ℝ) :
    heightApprox ε f t = supOccupation ε (reversedAt t f) t := by
  let B : Set ℝ := {u | 0 ≤ u ∧ u ≤ (t : ℝ) ∧
    supReflected (reversedAt t f) u.toNNReal < ε}
  have hB : MeasurableSet B := by
    refine (measurableSet_le measurable_const measurable_id).inter ?_
    refine (measurableSet_le measurable_id measurable_const).inter ?_
    have hm : Measurable (fun u : ℝ => supReflected (reversedAt t f) u.toNNReal) :=
      Measurable.comp (g := fun q : ℝ≥0 × DLoc => supReflected q.2 q.1)
        (f := fun u : ℝ => (u.toNNReal, reversedAt t f))
        measurable_supReflected_uncurry (measurable_real_toNNReal.prodMk measurable_const)
    exact measurableSet_lt hm measurable_const
  have hvol : volume ((fun s : ℝ => (t : ℝ) - s) ⁻¹' B) = volume B := by
    exact (volume.measurePreserving_sub_left (t : ℝ)).measure_preimage hB.nullMeasurableSet
  unfold heightApprox supOccupation
  congr 2
  change volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
    f.1 s.toNNReal < futureInf f t s.toNNReal + ε} = volume B
  rw [← hvol]
  apply measure_congr
  filter_upwards [ae_leftLim_eq_on_interval f t] with s hs
  apply propext
  change (0 ≤ s ∧ s ≤ (t : ℝ) ∧
      f.1 s.toNNReal < futureInf f t s.toNNReal + ε) ↔
    (0 ≤ (t : ℝ) - s ∧ (t : ℝ) - s ≤ (t : ℝ) ∧
      supReflected (reversedAt t f) ((t : ℝ) - s).toNNReal < ε)
  by_cases hs0 : 0 ≤ s
  · by_cases hst : s ≤ (t : ℝ)
    · have hst' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hst
      have he : ((t : ℝ) - s).toNNReal = t - s.toNNReal := by
        apply NNReal.coe_injective
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr hst), NNReal.coe_sub hst',
          Real.coe_toNNReal _ hs0]
      rw [he, supReflected_reversedAt_window f hst' hf (hs hs0 hst)]
      constructor <;> rintro ⟨ha, hb, hc⟩ <;> refine ⟨by linarith, by linarith, ?_⟩ <;> linarith
    · constructor <;> rintro ⟨ha, hb, hc⟩ <;> exfalso <;> linarith
  · constructor <;> rintro ⟨ha, hb, hc⟩ <;> exfalso <;> linarith

/-- **Identification** (a.s. for each fixed `t`, all `ε > 0` at once): the interval-infimum
approximation is the H01 occupation approximation of the reversed process. -/
theorem ae_heightApprox_eq_supOccupation_reversed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ ε : ℝ, 0 < ε →
      heightApprox ε f t = supOccupation ε (reversedAt t f) t := by
  filter_upwards [ae_leftLim_le_stableLocalLaw hθ] with f hf
  intro ε _hε
  exact heightApprox_eq_supOccupation_reversed f hf t ε

/-- The raw filtration is contained in the sigma-algebra of the restricted path. -/
theorem rawFiltration_le_restrict_comap (t : ℝ≥0) :
    DLoc.rawFiltration t ≤ MeasurableSpace.comap (DLoc.restrict t) inferInstance := by
  change (⨆ s ≤ t, MeasurableSpace.comap (DLoc.eval s) inferInstance) ≤ _
  apply iSup₂_le
  intro s hst
  have hm : Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (DLoc.eval s) :=
    (BGW.Skorokhod.measurable_eval ⟨s, s.2, hst⟩).comp
      (comap_measurable (DLoc.restrict t))
  exact hm.comap_le

/-- The occupation at a fixed horizon is measurable from the restricted path. -/
theorem measurable_supOccupation_prefix (ε : ℝ) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => supOccupation ε f t) :=
  (measurable_rawFiltration_supOccupation ε t).mono (rawFiltration_le_restrict_comap t) le_rfl

/-- The supremum local time at a fixed horizon is measurable from the restricted path. -/
theorem measurable_supLocalTime_prefix (θ : ℝ) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => supLocalTime θ f t) := by
  exact Measurable.limsup fun k => measurable_supOccupation_prefix (supEps θ k) t

private theorem measure_reversed_prefix_event {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) {A : Set DLoc}
    (hA : MeasurableSet[MeasurableSpace.comap (DLoc.restrict t) inferInstance] A) :
    (stableLocalLaw θ : Measure DLoc) ((reversedAt t) ⁻¹' A) =
      (stableLocalLaw θ : Measure DLoc) A := by
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have hm : Measurable (fun f : DLoc => reversedAt t f) :=
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => reversedAt p.1 p.2)
      (f := fun f : DLoc => (t, f)) measurable_reversedAt_uncurry
      (measurable_const.prodMk measurable_id)
  calc
    _ = ((stableLocalLaw θ : Measure DLoc).map
        (fun f => DLoc.restrict t (reversedAt t f))) B :=
      (Measure.map_apply ((DLoc.measurable_restrict t).comp hm) hB).symm
    _ = ((stableLocalLaw θ : Measure DLoc).map (DLoc.restrict t)) B := by
      rw [map_restrict_reversedAt_stableLocalLaw hθ ht]
    _ = _ := Measure.map_apply (DLoc.measurable_restrict t) hB

/-- A measurable almost sure prefix property transports to the reversed prefix. -/
theorem ae_reversedAt_of_prefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) {p : DLoc → Prop}
    (hp : MeasurableSet[MeasurableSpace.comap (DLoc.restrict t) inferInstance] {f | p f})
    (ha : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), p f) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), p (reversedAt t f) := by
  rw [ae_iff] at ha ⊢
  exact (measure_reversed_prefix_event hθ ht hp.compl).trans ha

/-- The height approximation vanishes at its initial time for every path and cutoff. -/
theorem heightApprox_zero (ε : ℝ) (f : DLoc) : heightApprox ε f 0 = 0 := by
  have hz : volume {s : ℝ | 0 ≤ s ∧ s ≤ (0 : ℝ≥0) ∧
      f.1 s.toNNReal < futureInf f 0 s.toNNReal + ε} = 0 := by
    apply measure_mono_null (t := ({0} : Set ℝ))
    · intro s hs
      exact le_antisymm hs.2.1 hs.1
    · exact measure_singleton 0
  unfold heightApprox
  rw [hz]
  simp

/-- The height starts at zero on every path, including exceptional paths. -/
theorem height_zero (θ : ℝ) (f : DLoc) : height θ f 0 = 0 := by
  unfold height supLocalTime
  simp only [supOccupation_zero, limsup_const]

/-- **A.s. convergence along the deterministic sequence `supEps θ`**, for each fixed `t`
(the null set depends on `t`). -/
theorem ae_tendsto_heightApprox_supEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun k => heightApprox (supEps θ k) f t) atTop (𝓝 (height θ f t)) := by
  by_cases ht : t = 0
  · subst t
    filter_upwards with f
    simp only [heightApprox_zero, height_zero]
    exact tendsto_const_nhds
  have hp : MeasurableSet[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      {f | Tendsto (fun k => supOccupation (supEps θ k) f t) atTop
        (𝓝 (supLocalTime θ f t))} := by
    let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict t) inferInstance
    exact measurableSet_tendsto_fun
      (fun k => measurable_supOccupation_prefix (supEps θ k) t) (measurable_supLocalTime_prefix θ t)
  have ha := ae_reversedAt_of_prefix hθ (pos_iff_ne_zero.mpr ht) hp
    ((ae_tendsto_supOccupation hθ).mono (fun _ hf => hf t))
  filter_upwards [ha, ae_heightApprox_eq_supOccupation_reversed hθ t] with f hf he
  exact (tendsto_congr (fun k => he (supEps θ k) (supEps_pos θ k))).mpr hf

/-- **Convergence in probability** for each fixed `t` along the full filter `ε ↓ 0`. -/
theorem heightApprox_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    TendstoInMeasure (stableLocalLaw θ : Measure DLoc)
      (fun (ε : ℝ) (f : DLoc) => heightApprox ε f t) (𝓝[>] (0 : ℝ))
      (fun f => height θ f t) := by
  by_cases ht : t = 0
  · subst t
    apply tendstoInMeasure_iff_dist.mpr
    intro δ hδ
    simp only [heightApprox_zero, height_zero, dist_self]
    simp only [not_le.mpr hδ, ofPred_false, measure_empty]
    exact tendsto_const_nhds
  have hrev : TendstoInMeasure (stableLocalLaw θ : Measure DLoc)
      (fun (ε : ℝ) (f : DLoc) => supOccupation ε (reversedAt t f) t)
      (𝓝[>] (0 : ℝ)) (fun f => height θ f t) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro δ hδ
    have hi := (tendstoInMeasure_iff_dist.mp (supOccupation_tendstoInMeasure hθ t)) δ hδ
    have he (ε : ℝ) :
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ dist (supOccupation ε (reversedAt t f) t) (height θ f t)} =
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ dist (supOccupation ε f t) (supLocalTime θ f t)} := by
      change (stableLocalLaw θ : Measure DLoc) ((reversedAt t) ⁻¹'
        {f | δ ≤ dist (supOccupation ε f t) (supLocalTime θ f t)}) = _
      exact measure_reversed_prefix_event hθ (pos_iff_ne_zero.mpr ht)
        (A := {f | δ ≤ dist (supOccupation ε f t) (supLocalTime θ f t)}) (by
        let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict t) inferInstance
        exact measurableSet_le measurable_const
          ((measurable_supOccupation_prefix ε t).dist (measurable_supLocalTime_prefix θ t)))
    simpa only [he] using hi
  apply hrev.congr' _ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with ε hε
  filter_upwards [ae_heightApprox_eq_supOccupation_reversed hθ t] with f hf
  exact (hf ε hε).symm

/-- The raw height is a.s. the finite nonnegative height, for each fixed `t`. -/
theorem ae_heightRaw_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      0 ≤ height θ f t ∧ heightRaw θ f t = ENNReal.ofReal (height θ f t) := by
  filter_upwards [ae_tendsto_heightApprox_supEps hθ t] with f hf
  have hn : 0 ≤ height θ f t := ge_of_tendsto hf (Eventually.of_forall fun k => by
    unfold heightApprox
    exact mul_nonneg (inv_nonneg.mpr (supEps_pos θ k).le) ENNReal.toReal_nonneg)
  refine ⟨hn, ?_⟩
  exact (ENNReal.tendsto_ofReal hf).liminf_eq

end BGW.StableTrees
