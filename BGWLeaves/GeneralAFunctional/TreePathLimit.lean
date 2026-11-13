module

public import BGWLeaves.GeneralAFunctional.TreePathDensity

/-! Continuous convergence of the augmented deterministic-prefix density. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreePathLimit

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreeAugmented BGWLeaves.GeneralAFunctional.TreeClocks
open BGWLeaves.GeneralAFunctional.TreePathDensity BGWLeaves.GeneralAFunctional.TreeKernel
open BGWLeaves.GeneralAFunctional.TreeLocal BGWLeaves.GeneralAFunctional.TreeResidue
open scoped ENNReal NNReal Topology

/-- A moving nonnegative floor introduces only `o(c_n)` error at a diverging scale. -/
theorem floor_mul_div_tendsto {c v : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {x : ℝ} (hx : 0 < x) (hv : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun i => (⌊v i * c i⌋₊ : ℝ) / c i) atTop (𝓝 x) := by
  have hinv : Tendsto (fun i => 1 / c i) atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop hc
  have hlo := hv.sub hinv
  simp only [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hv
  · filter_upwards [hc.eventually (eventually_gt_atTop 0)] with i hi
    have he : v i - 1 / c i = (v i * c i - 1) / c i := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one (v i * c i)]) hi.le
  · filter_upwards [hc.eventually (eventually_gt_atTop 0), hv.eventually (eventually_gt_nhds hx)] with i hi hvi
    have hh := div_le_div_of_nonneg_right (Nat.floor_le (mul_nonneg hvi.le hi.le)) hi.le
    simpa only [mul_div_cancel_right₀ _ hi.ne'] using hh

/-- Density convergence on arbitrary moving augmented states, not just actual prefixes. -/
theorem pathWeight_continuousConv {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (hqadm : ∀ i, ZetaAAdmissible μ A (q i))
    {b : ℝ≥0} (hb0 : 0 < b) (hb1 : b < 1) {z : PairSpace b × ℝ}
    (hend : ContinuousAt z.1.1 ⟨(b : ℝ), b.coe_nonneg, le_rfl⟩)
    (hx : 0 < DiscreteBridge.endValue b z.1.1) (hzmark : z.2 = b)
    {v : ℕ → PairSpace b × ℝ} (hv : Tendsto v atTop (𝓝 z)) :
    Tendsto (fun i => pathWeight μ A B (q i) (explorationIndex μ A (q i)) b (v i)) atTop
      (𝓝 (gammaA θ b (DiscreteBridge.endValue b z.1.1))) := by
  let r := fun i => explorationIndex μ A (q i)
  let k := fun i => recoveredMarks (q i) (v i)
  let raw := fun i => rawStack B (r i) b (v i)
  let j := fun i => recoveredStack μ A B (q i) (r i) b (v i)
  let x := DiscreteBridge.endValue b z.1.1
  have hr := (explorationIndex_atTop hA).comp hq
  have hc : Tendsto (fun i => B (r i)) atTop atTop := h.isRealStableAttracted.tendsto_norming_atTop.comp hr
  have hn : Tendsto (fun i => (q i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hq
  have hmark : Tendsto (fun i => (v i).2) atTop (𝓝 (b : ℝ)) := by simpa only [hzmark] using hv.snd_nhds
  have hk : Tendsto (fun i => (k i : ℝ) / q i) atTop (𝓝 (b : ℝ)) :=
    floor_mul_div_tendsto hn hb0 hmark
  have heval : Tendsto (fun i => DiscreteBridge.endValue b (v i).1.1) atTop (𝓝 x) :=
    (Skorokhod.continuousAt_eval hend).tendsto.comp hv.fst_nhds.fst_nhds
  have hrawB : Tendsto (fun i => (raw i : ℝ) / B (r i)) atTop (𝓝 x) := by
    have ht := (floor_mul_div_tendsto hc hx heval).add
      (tendsto_const_nhds.div_atTop hc : Tendsto (fun i => (1 : ℝ) / B (r i)) atTop (𝓝 0))
    simp only [add_zero] at ht
    convert ht using 1
    funext i
    simp only [raw, rawStack, Nat.cast_add, Nat.cast_one, add_div]
  have hscale := (markScale_ratio_exploration h hA).comp hq
  have hraw : Tendsto (fun i => (raw i : ℝ) / markScale μ A θ (q i)) atTop (𝓝 x) := by
    have ht := hrawB.div hscale one_ne_zero
    simp only [div_one] at ht
    apply ht.congr'
    filter_upwards [hr.eventually h.isRealStableAttracted.pos] with i hi
    change 0 < B (r i) at hi
    change ((raw i : ℝ) / B (r i)) / (markScale μ A θ (q i) / B (r i)) = _
    field_simp [hi.ne']
  have he : 0 < arithFactor μ A := GeneralA.Arithmetic.arithFactor_pos h.critical h.nondegenerate A
  have hctop := (markScale_atTop h.critical h.nondegenerate ⟨B, h⟩ hA).comp hq
  have hj : Tendsto (fun i => (j i : ℝ) / markScale μ A θ (q i)) atTop (𝓝 x) :=
    pendingProject_normalized_tendsto he hctop hraw
  have hjpos : ∀ᶠ i in atTop, 1 ≤ j i := by
    filter_upwards with i
    exact le_trans (Nat.succ_le_succ (Nat.zero_le _))
      (LeafLimitsGeneral.Residue.natProject_bounds he _ _).1
  have hres : ∀ᶠ i in atTop, (arithFactor μ A : ℤ) ∣ ((q i - k i : ℕ) : ℤ) - j i := by
    filter_upwards with i
    exact pendingProject_residue he _ _ _
  have ht := kernelDensity_tendsto h ⟨B, h⟩ hA hq hqadm hr hscale hb0 hb1 hx
    ((prefixLength_ratio b).comp hr) hk hj hjpos hres
  have hkn : ∀ᶠ i in atTop, k i ≤ q i := by
    filter_upwards [hk.eventually (eventually_lt_nhds (show (b : ℝ) < 1 from hb1)),
      hq.eventually_ge_atTop 1] with i hi hqi
    have hqpos : (0 : ℝ) < q i := by exact_mod_cast hqi
    have hh := (div_lt_iff₀ hqpos).mp hi
    simp only [one_mul] at hh
    exact_mod_cast hh.le
  have hgamma : 0 ≤ gammaA θ b (DiscreteBridge.endValue b z.1.1) :=
    gammaA_nonneg h.alpha_mem hb1 hx
  have ht' := ht.max (tendsto_const_nhds (x := (0 : ℝ)))
  have ht'' : Tendsto (fun i => max (kernelDensity μ A (q i) (r i) (prefixLength b (r i)) (k i) (j i)) 0)
      atTop (𝓝 (gammaA θ b (DiscreteBridge.endValue b z.1.1))) := by
    convert ht' using 1
    congr 1
    exact congrArg (fun x : ℝ => 𝓝 x) (max_eq_left hgamma).symm
  apply ht''.congr'
  filter_upwards [hkn] with i hi
  exact (ite_eq_left hi).symm

end BGWLeaves.GeneralAFunctional.TreePathLimit
