module

public import BGWLeaves.GeneralAFunctional.TreeLocal
public import BGWLeaves.LocalEstimates.SizeTailKernel
public import BGWLeaves.Coding

/-! Moving remaining-mark counts in the marked forest local limit. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeMoving

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeLocal
open scoped ENNReal Topology

theorem moving_index_atTop {u q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {s : ℝ} (hs : 0 < s) (hu : Tendsto (fun k => (u k : ℝ) / q k) atTop (𝓝 s)) :
    Tendsto u atTop atTop := by
  have ht := hu.pos_mul_atTop hs (tendsto_natCast_atTop_atTop.comp hq)
  have he : ∀ᶠ k in atTop, ((u k : ℝ) / q k) * q k = u k := by
    filter_upwards [hq.eventually_ne_atTop 0] with k hk
    have hn : (q k : ℝ) ≠ 0 := by exact_mod_cast hk
    field_simp
  exact tendsto_natCast_atTop_iff.mp (ht.congr' he)

/-- Marked exploration scales inherit the stable regular-variation ratio. -/
theorem markScale_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {u q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {s : ℝ} (hs : 0 < s)
    (hu : Tendsto (fun k => (u k : ℝ) / q k) atTop (𝓝 s)) :
    Tendsto (fun k => markScale μ A θ (u k) / markScale μ A θ (q k)) atTop
      (𝓝 (s ^ (1 / θ))) := by
  have hcan := isRealStableAttracted_norming hc hne hDA
  have hutop := moving_index_atTop hq hs hu
  have hr := GeneralAInf.BlockStable.norming_floor_ratio hc hne hDA hA
  have hm : 0 < (μ.toMeasure A).toReal ^ (1 / θ) :=
    Real.rpow_pos_of_pos (ENNReal.toReal_pos hA (measure_ne_top _ _)) _
  have ht := ((hcan.tendsto_norming_ratio hs hq hu).mul (hr.comp hq)).div (hr.comp hutop) hm.ne'
  rw [mul_div_cancel_right₀ _ hm.ne'] at ht
  apply ht.congr'
  filter_upwards [hutop.eventually hcan.pos, hq.eventually hcan.pos,
    ((markScale_atTop hc hne hDA hA).comp hq).eventually (eventually_gt_atTop 0),
    ((markScale_atTop hc hne hDA hA).comp hutop).eventually (eventually_gt_atTop 0)] with k hBu hBq hbq hbu
  dsimp only [Pi.div_apply, Function.comp_def, markScale] at *
  field_simp [hBu.ne', hBq.ne', hbu.ne', hbq.ne']

/-- Step D, with both the remaining-mark count and the pending-tree endpoint moving.
The endpoint range hypothesis is derived from the two scaling limits. -/
theorem moving_forest_limit {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {u q j : ℕ → ℕ} (hq : Tendsto q atTop atTop) {s x : ℝ} (hs : 0 < s)
    (hu : Tendsto (fun k => (u k : ℝ) / q k) atTop (𝓝 s))
    (hx : Tendsto (fun k => (j k : ℝ) / markScale μ A θ (q k)) atTop (𝓝 x))
    (hj : ∀ᶠ k in atTop, 1 ≤ j k)
    (hres : ∀ᶠ k in atTop, (arithFactor μ A : ℤ) ∣ (u k : ℤ) - j k) :
    Tendsto (fun k => (q k : ℝ) *
      ((Measure.pi fun _ : Fin (j k) => bienaymeLaw μ.toMeasure)
        (markedForestEvent A (j k) (u k))).toReal) atTop
      (𝓝 ((arithFactor μ A : ℝ) * qKernel θ s x)) := by
  have hutop := moving_index_atTop hq hs hu
  have hscale := markScale_ratio hc hne hDA hA hq hs hu
  have hsp : 0 < s ^ (1 / θ) := Real.rpow_pos_of_pos hs _
  have hy : Tendsto (fun k => (j k : ℝ) / markScale μ A θ (u k)) atTop
      (𝓝 (x / s ^ (1 / θ))) := by
    have ht := hx.div hscale hsp.ne'
    apply ht.congr'
    filter_upwards [((markScale_atTop hc hne hDA hA).comp hq).eventually (eventually_gt_atTop 0)]
      with k hk
    change 0 < markScale μ A θ (q k) at hk
    dsimp only [Pi.div_apply]
    field_simp [hk.ne']
  have hm : 0 < (μ.toMeasure A).toReal ^ (1 / θ) :=
    Real.rpow_pos_of_pos (ENNReal.toReal_pos hA (measure_ne_top _ _)) _
  have hr := GeneralAInf.BlockStable.norming_floor_ratio hc hne hDA hA
  have hjratio : Tendsto (fun k => (j k : ℝ) / norming (stepLaw μ) θ (u k)) atTop
      (𝓝 ((x / s ^ (1 / θ)) / (μ.toMeasure A).toReal ^ (1 / θ))) := by
    have ht := hy.div (hr.comp hutop) hm.ne'
    apply ht.congr'
    filter_upwards [((markScale_atTop hc hne hDA hA).comp hutop).eventually (eventually_gt_atTop 0)]
      with k hk
    change 0 < markScale μ A θ (u k) at hk
    dsimp only [Pi.div_apply, Function.comp_def, markScale] at *
    field_simp [hk.ne']
  let α := |(x / s ^ (1 / θ)) / (μ.toMeasure A).toReal ^ (1 / θ)| + 1
  have hα : 0 < α := by dsimp [α]; positivity
  have hbound : ∀ᶠ k in atTop, 1 ≤ j k ∧ (j k : ℝ) ≤ α * norming (stepLaw μ) θ (u k) := by
    have hlim : (x / s ^ (1 / θ)) / (μ.toMeasure A).toReal ^ (1 / θ) < α := by
      dsimp [α]
      linarith [le_abs_self ((x / s ^ (1 / θ)) / (μ.toMeasure A).toReal ^ (1 / θ))]
    filter_upwards [hj, hjratio.eventually (eventually_lt_nhds hlim),
      hutop.eventually (isRealStableAttracted_norming hc hne hDA).pos] with k hjk hk hp
    exact ⟨hjk, ((div_lt_iff₀ hp).mp hk).le⟩
  have ht := moving_forest_reference hc hne hDA hA hutop hα hs hbound hres hy hu
  convert ht using 1
  congr 1
  rw [LocalEstimates.SizeTailKernel.qKernel_scaling hs, qKernel_one, Real.rpow_neg hs.le]
  simp only [q₁, div_eq_mul_inv, one_mul]
  ring

end BGWLeaves.GeneralAFunctional.TreeMoving
