/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderRestartMarkov
public import BGW.StableTrees.SupremumLadderRestartOccupation
public import BGW.StableTrees.SupremumLadderRestartInverse

/-!
# Restart at inverse local time and the ascending ladder pair

Occupation additivity at a contact time identifies the restarted public clock. Strict
inversion then identifies the ladder increments with the ladder of the independent future.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VI (ladder processes).
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapter 6.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Restart identity at `A_z`**.  Let `f' = shiftAt A_z f`
be the post-`A_z` centered path.  Almost surely `X_{A_z} = S_{A_z} = B_z` (zero drawdown at `A_z`,
not zero overshoot), the reflected process restarts, `S_{A_z+t} = B_z + S'_t`, and
`M(A_z + t) = z + M'(t)` for all `t`, where `S', M'` are computed from `f'`. -/
theorem ae_supRestart_at_ladderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supLadderHeight θ z f = f.1 (supLadderTime θ z f) ∧
      ∀ t : ℝ≥0,
        supReflected f (supLadderTime θ z f + t) =
            supReflected (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) t ∧
        supRunning f (supLadderTime θ z f + t) =
            supLadderHeight θ z f +
              supRunning (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) t ∧
        supLocalTime θ f (supLadderTime θ z f + t) =
            (z : ℝ) + supLocalTime θ
              (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) t := by
  have hfuture : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun k => supOccupation (supEps θ k)
        (DLoc.shiftAt (supHitting θ z) f) t) atTop
        (𝓝 (supLocalTime θ (DLoc.shiftAt (supHitting θ z) f) t)) := by
    have h := ae_tendsto_supOccupation hθ
    rw [← map_shiftAt_supHitting hθ z] at h
    exact (ae_of_ae_map (DLoc.measurable_shiftAt
      (isStoppingTime_supHitting θ z)).aemeasurable h)
  filter_upwards [ae_supLadder_geometry hθ, ae_supLadder_spec hθ,
    ae_tendsto_supOccupation hθ, hfuture, ae_shiftAt_supHitting_eq hθ z,
    ae_eval_zero_stableLocalLaw hθ] with f hg hspec hf hf' hshift h0
  have hcontact := hg.2.2.1 z
  have hfuture' : ∀ t : ℝ≥0,
      Tendsto (fun k =>
        supOccupation (supEps θ k) (DLoc.shift (supLadderTime θ z f) f) t)
        atTop (𝓝 (supLocalTime θ (DLoc.shift (supLadderTime θ z f) f) t)) := by
    rw [hshift] at hf'
    simpa only [DLoc.shiftAt, ENNReal.toNNReal_coe] using hf'
  refine ⟨hg.2.2.2.1 z, fun t => ?_⟩
  change supReflected f (supLadderTime θ z f + t) =
    supReflected (DLoc.shift (supLadderTime θ z f) f) t ∧ _
  refine ⟨supReflected_shift_of_contact h0 hcontact t,
    supRunning_shift_of_contact h0 hcontact t, ?_⟩
  have hl := (hf (supLadderTime θ z f + t)).sub (hf (supLadderTime θ z f))
  have hr := hfuture' t
  have he (k : ℕ) := supOccupation_shift_of_contact
    ((isSupOccupationSeq_supEps hθ).1 k) h0 hcontact t
  have hlim := tendsto_nhds_unique hl (hr.congr (fun k => (he k).symm))
  rw [hspec.2.2.2.2.2 z] at hlim
  change supLocalTime θ f (supLadderTime θ z f + t) =
    (z : ℝ) + supLocalTime θ (DLoc.shift (supLadderTime θ z f) f) t
  linarith

/-- The ladder pair `(A_z, B_z)` as a real vector. -/
noncomputable def supLadderPair (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ × ℝ :=
  ((supLadderTime θ z f : ℝ), supLadderHeight θ z f)

/-- The ladder increment `(A_z - A_y, B_z - B_y)` over levels `y ≤ z`. -/
noncomputable def supLadderIncrement (θ : ℝ) (y z : ℝ≥0) (f : DLoc) : ℝ × ℝ :=
  ((supLadderTime θ z f : ℝ) - supLadderTime θ y f, supLadderHeight θ z f - supLadderHeight θ y f)

/-- Measurability of the ladder pair at each level. -/
theorem measurable_supLadderPair (θ : ℝ) (z : ℝ≥0) : Measurable (supLadderPair θ z) := by
  have hA : Measurable (supLadderTime θ z) :=
    Measurable.of_uncurry_left (f := supLadderTime θ) (measurable_supLadder_uncurry θ).1
  have hB : Measurable (supLadderHeight θ z) :=
    Measurable.of_uncurry_left (f := supLadderHeight θ) (measurable_supLadder_uncurry θ).2
  change Measurable (fun f : DLoc => ((supLadderTime θ z f : ℝ), supLadderHeight θ z f))
  exact hA.coe_nnreal_real.prodMk hB

/-- Measurability of each ladder increment. -/
theorem measurable_supLadderIncrement (θ : ℝ) (y z : ℝ≥0) :
    Measurable (supLadderIncrement θ y z) := by
  exact ((measurable_supLadderPair θ z).fst.sub (measurable_supLadderPair θ y).fst).prodMk
    ((measurable_supLadderPair θ z).snd.sub (measurable_supLadderPair θ y).snd)

/-- Start at the origin: `(A_0, B_0) = (0, 0)` almost surely. -/
theorem ae_supLadderPair_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), supLadderPair θ 0 f = (0, 0) := by
  filter_upwards [ae_supLadder_spec hθ, ae_eval_zero_stableLocalLaw hθ] with f hf h0
  simp only [supLadderPair, supLadderHeight, hf.2.1, NNReal.coe_zero, supRunning_zero, h0]

/-- Almost surely the ladder pair is nonnegative, nondecreasing in both coordinates, and
right-continuous in the level, for all levels simultaneously. -/
theorem ae_supLadderPair_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ z, 0 ≤ (supLadderPair θ z f).1 ∧ 0 ≤ (supLadderPair θ z f).2) ∧
      Monotone (fun z => (supLadderPair θ z f).1) ∧
      Monotone (fun z => (supLadderPair θ z f).2) ∧
      ∀ z, ContinuousWithinAt (fun z => supLadderPair θ z f) (Ici z) z := by
  filter_upwards [ae_supLadder_spec hθ, ae_supLadder_geometry hθ,
    ae_supLadderPair_zero hθ] with f hs hg h0
  have hA : Monotone (fun z => (supLadderPair θ z f).1) :=
    NNReal.coe_mono.comp hs.2.2.1
  have hB : Monotone (fun z => (supLadderPair θ z f).2) := hs.2.2.2.2.1
  refine ⟨fun z => ⟨(supLadderTime θ z f).coe_nonneg, ?_⟩, hA, hB, fun z => ?_⟩
  · have hb := hB (show 0 ≤ z from zero_le)
    simpa only [h0, Prod.snd_zero] using hb
  · exact (NNReal.continuous_coe.continuousAt.comp_continuousWithinAt
      (hs.2.2.2.1 z)).prodMk (hg.2.2.2.2 z)

/-- **Ladder process restarts**: with `f' = shiftAt A_z f`, for all `u ≥ 0` simultaneously,
`A_{z+u}(f) = A_z(f) + A_u(f')` and `B_{z+u}(f) = B_z(f) + B_u(f')`. -/
theorem ae_supLadder_restart {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ u : ℝ≥0,
      supLadderTime θ (z + u) f =
          supLadderTime θ z f +
            supLadderTime θ u (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) ∧
      supLadderHeight θ (z + u) f =
          supLadderHeight θ z f +
            supLadderHeight θ u (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) := by
  have hg : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ u, supLocalTimeInverse θ (DLoc.shiftAt (supHitting θ z) f) u =
        (supLadderTime θ u (DLoc.shiftAt (supHitting θ z) f) : WithTop ℝ≥0) := by
    have h := (ae_supLadder_spec hθ).mono (fun _ hf => hf.1)
    rw [← map_shiftAt_supHitting hθ z] at h
    exact ae_of_ae_map (DLoc.measurable_shiftAt (isStoppingTime_supHitting θ z)).aemeasurable h
  filter_upwards [ae_supRestart_at_ladderTime hθ z, ae_supLocalTime_spec hθ,
    ae_supLadder_spec hθ, hg, ae_shiftAt_supHitting_eq hθ z] with f hr hm hs hg he
  rw [he] at hg
  intro u
  have ha := supLadderTime_add_of_clock_restart hm.2.1 hs.1 hg
    (hs.2.2.2.2.2 z) (fun t => (hr.2 t).2.2) u
  refine ⟨ha, ?_⟩
  change supRunning f (supLadderTime θ (z + u) f) = _
  rw [ha]
  exact (hr.2 _).2.1

private theorem ae_increment_eq_restart {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {y z : ℝ≥0} (hyz : y ≤ z) :
    supLadderIncrement θ y z =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => supLadderPair θ (z - y) (DLoc.shiftAt (supHitting θ y) f) := by
  filter_upwards [ae_supLadder_restart hθ y, ae_shiftAt_supHitting_eq hθ y] with f hf he
  obtain ⟨ha, hb⟩ := hf (z - y)
  rw [add_tsub_cancel_of_le hyz] at ha hb
  rw [he]
  dsimp only [supLadderIncrement, supLadderPair]
  apply Prod.ext
  · change (supLadderTime θ z f : ℝ) - supLadderTime θ y f = _
    rw [ha, NNReal.coe_add]
    ring
  · change supLadderHeight θ z f - supLadderHeight θ y f = _
    rw [hb]
    ring

/-- **Stationary increments**: the increment over `[y, z]` has the law of the pair at level
`z - y`. -/
theorem map_supLadderIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {y z : ℝ≥0} (hyz : y ≤ z) :
    (stableLocalLaw θ : Measure DLoc).map (supLadderIncrement θ y z) =
      (stableLocalLaw θ : Measure DLoc).map (supLadderPair θ (z - y)) := by
  rw [Measure.map_congr (ae_increment_eq_restart hθ hyz)]
  rw [← Function.comp_def, ← Measure.map_map (measurable_supLadderPair θ (z - y))
    (DLoc.measurable_shiftAt (isStoppingTime_supHitting θ y)), map_shiftAt_supHitting hθ y]

private theorem indep_comap_congr {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {m : MeasurableSpace Ω} {f g : Ω → E}
    (hfg : f =ᵐ[P] g) (hg : Indep m (MeasurableSpace.comap g inferInstance) P) :
    Indep m (MeasurableSpace.comap f inferInstance) P := by
  intro A B hA hB
  apply Filter.Eventually.of_forall
  intro a
  change P (A ∩ B) = P A * P B
  obtain ⟨C, hC, rfl⟩ := hB
  have he : f ⁻¹' C =ᵐ[P] g ⁻¹' C := by
    filter_upwards [hfg] with x hx
    simp only [mem_preimage, hx]
  have hei : A ∩ f ⁻¹' C =ᵐ[P] A ∩ g ⁻¹' C := by
    filter_upwards [he] with x hx
    simp only [mem_inter_iff, mem_preimage] at *
    rw [hx]
  rw [measure_congr hei, measure_congr he]
  have hh := hg A (g ⁻¹' C) hA ⟨C, hC, rfl⟩
  simpa only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure] using hh

/-- **Independence of the future increment from `F_{A_y}`**: the increment over `[y, z]` is
independent of the stopped σ-algebra of `supHitting θ y`. -/
theorem indep_supLadderIncrement_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {y z : ℝ≥0}
    (hyz : y ≤ z) :
    Indep (isStoppingTime_supHitting θ y).measurableSpace
      (MeasurableSpace.comap (supLadderIncrement θ y z) (inferInstance : MeasurableSpace (ℝ × ℝ)))
      (stableLocalLaw θ : Measure DLoc) := by
  apply indep_comap_congr (ae_increment_eq_restart hθ hyz)
  apply indep_of_indep_of_le_right (indep_shiftAt_supHitting hθ y)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    (MeasurableSpace.comap_mono (g := DLoc.shiftAt (supHitting θ y))
      (measurable_supLadderPair θ (z - y)).comap_le)

private noncomputable def stoppedPair (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ × ℝ :=
  ((supHitting θ z f).toReal,
    stoppedValue (fun t (g : DLoc) => DLoc.eval t g) (supHitting θ z) f)

private theorem stoppedPair_measurable (θ : ℝ) {x y : ℝ≥0} (hxy : x ≤ y) :
    Measurable[(isStoppingTime_supHitting θ y).measurableSpace] (stoppedPair θ x) := by
  have hm : supHitting θ x ≤ supHitting θ y := by
    intro f
    apply le_iInf
    intro t
    split_ifs with ht
    · apply iInf_le_of_le t
      have hx : (x : ℝ≥0∞) < supLocalTimeENN θ f t :=
        (ENNReal.coe_le_coe.mpr hxy).trans_lt ht
      simp only [ite_eq_left hx]
      exact le_rfl
    · exact le_top
  exact ((isStoppingTime_supHitting θ x).measurable.ennreal_toReal.prodMk
    (DLoc.measurable_stoppedValue_eval (isStoppingTime_supHitting θ x))).mono
      ((isStoppingTime_supHitting θ x).measurableSpace_mono
        (isStoppingTime_supHitting θ y) hm) le_rfl

private theorem stoppedPair_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    stoppedPair θ z =ᵐ[(stableLocalLaw θ : Measure DLoc)] supLadderPair θ z := by
  filter_upwards [ae_supLadder_geometry hθ] with f hf
  apply Prod.ext
  · simp only [stoppedPair, supLadderPair, hf.2.1 z, ENNReal.coe_toReal]
  · change stoppedValue (fun t (g : DLoc) => DLoc.eval t g)
      (supHitting θ z) f = supLadderHeight θ z f
    rw [hf.2.2.2.1 z]
    simp only [stoppedValue, hf.2.1 z]
    rfl

/-- **Independent increments**: along every finite monotone chain of levels
`z 0 ≤ z 1 ≤ ... ≤ z n`, the `n` successive increments are mutually independent. -/
theorem iIndepFun_supLadderIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (n : ℕ)
    (z : Fin (n + 1) → ℝ≥0) (hz : Monotone z) :
    iIndepFun (fun k : Fin n => supLadderIncrement θ (z k.castSucc) (z k.succ))
      (stableLocalLaw θ : Measure DLoc) := by
  classical
  let P : Measure DLoc := stableLocalLaw θ
  let F : Fin n → DLoc → ℝ × ℝ := fun k =>
    supLadderIncrement θ (z k.castSucc) (z k.succ)
  let G : Fin n → DLoc → ℝ × ℝ := fun k f =>
    stoppedPair θ (z k.succ) f - stoppedPair θ (z k.castSucc) f
  have he (k : Fin n) : G k =ᵐ[P] F k := by
    filter_upwards [stoppedPair_eq hθ (z k.succ), stoppedPair_eq hθ (z k.castSucc)]
      with f h₁ h₂
    simp only [G, h₁, h₂, F, supLadderIncrement, supLadderPair, Prod.mk_sub_mk]
  suffices hi : iIndepFun G P from hi.congr he
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hm
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    have ha : a ∉ S := fun h => (lt_irrefl a) (hlt a h)
    let A : Set DLoc := ⋂ k ∈ S, G k ⁻¹' sets k
    have hA : MeasurableSet[(isStoppingTime_supHitting θ (z a.castSucc)).measurableSpace] A := by
      apply MeasurableSet.biInter S.countable_toSet
      intro k hk
      have hka : k.succ ≤ a.castSucc := by exact_mod_cast hlt k hk
      have hm₁ := stoppedPair_measurable θ (hz hka)
      have hm₂ := stoppedPair_measurable θ (hz (show k.castSucc ≤ a.castSucc by
        exact_mod_cast (hlt k hk).le))
      exact (hm₁.sub hm₂) (hm k (Finset.mem_insert_of_mem hk))
    have hind := indep_comap_congr (he a)
      (indep_supLadderIncrement_stopped hθ (hz (Fin.castSucc_le_succ a)))
    have hfact := hind A (G a ⁻¹' sets a) hA
      ⟨sets a, hm a (Finset.mem_insert_self _ _), rfl⟩
    simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure] at hfact
    rw [Finset.prod_insert ha, Finset.set_biInter_insert, inter_comm, hfact]
    rw [ih (fun k hk => hm k (Finset.mem_insert_of_mem hk)), mul_comm]

end BGW.StableTrees
