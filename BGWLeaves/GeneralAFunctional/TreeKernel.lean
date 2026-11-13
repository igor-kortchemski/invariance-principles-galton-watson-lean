module

public import BGWLeaves.GeneralAFunctional.TreeMoving
public import BGWLeaves.GeneralAFunctional.TreeMarkTail
public import BGW.StableTrees.ForestLocalLimitTail

/-! Moving-parameter analytic kernels for deterministic marked prefixes. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeKernel

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeLocal
open BGWLeaves.GeneralAFunctional.TreeMoving BGWLeaves.GeneralAFunctional.TreeMarkTail
open scoped ENNReal Topology

/-- The total-size forest-tail kernel allows arbitrary diverging reference sequences,
including sequences with repetitions. -/
theorem moving_forest_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q j r : ℕ → ℕ} (hq : Tendsto q atTop atTop) {x s : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hj : Tendsto (fun k => (j k : ℝ) / B (q k)) atTop (𝓝 x))
    (hr : Tendsto (fun k => (r k : ℝ) / q k) atTop (𝓝 s)) :
    Tendsto (fun k => forestTail μ (j k) (r k)) atTop
      (𝓝 (BGW.StableTrees.sizeTailKernel θ s x)) := by
  have herr : Tendsto (fun k => forestTail μ (j k) (r k) -
      BGW.StableTrees.sizeTailKernel θ ((r k : ℝ) / q k) ((j k : ℝ) / B (q k))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hbnd := forestTailLimit_uniform h (half_pos hs) (by linarith : s / 2 ≤ s + 1)
      (half_pos hx) (by linarith : x / 2 ≤ x + 1) (half_pos hε)
    have hp := h.isRealStableAttracted.pos
    filter_upwards [hq.eventually hbnd, hq.eventually hp, hq.eventually_ge_atTop 1,
      hj.eventually (eventually_gt_nhds (half_lt_self hx)),
      hj.eventually (eventually_lt_nhds (show x < x + 1 by linarith)),
      hr.eventually (eventually_gt_nhds (half_lt_self hs)),
      hr.eventually (eventually_lt_nhds (show s < s + 1 by linarith))]
      with k hk hBk hqk hjlo hjhi hrlo hrhi
    have hqpos : (0 : ℝ) < q k := by exact_mod_cast hqk
    rw [Real.dist_eq, sub_zero]
    exact (hk (r k) (j k) ((lt_div_iff₀ hqpos).mp hrlo).le
      ((div_lt_iff₀ hqpos).mp hrhi).le hjlo.le hjhi.le).trans_lt (half_lt_self hε)
  have hdom : IsOpen {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
  have hcont := (BGW.StableTrees.continuousOn_sizeTailKernel h.alpha_mem).continuousAt
    (hdom.mem_nhds (show (s, x) ∈ {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} from ⟨hs, hx⟩))
  have ht := herr.add (hcont.tendsto.comp (hr.prodMk_nhds hj))
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using ht

/-- Subtracting a moving revealed-mark count respects the remaining-time ratio. -/
theorem remaining_count_ratio {q k : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {b : ℝ} (hb : b < 1) (hk : Tendsto (fun i => (k i : ℝ) / q i) atTop (𝓝 b)) :
    Tendsto (fun i => ((q i - k i : ℕ) : ℝ) / q i) atTop (𝓝 (1 - b)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hk
  apply ht.congr'
  filter_upwards [hq.eventually_ge_atTop 1, hk.eventually (eventually_lt_nhds hb)] with i hqi hki
  have hqpos : (0 : ℝ) < q i := by exact_mod_cast hqi
  have hkle : k i ≤ q i := by
    have hh := (div_lt_iff₀ hqpos).mp hki
    simp only [one_mul] at hh
    exact_mod_cast hh.le
  rw [Nat.cast_sub hkle]
  field_simp

/-- Pure kernel density; revealing a prefix supplies its length, mark count and stack. -/
noncomputable def kernelDensity (μ : PMF ℕ) (A : Set ℕ) (n r l k j : ℕ) : ℝ :=
  forestTail μ 1 r / markedMass μ A n *
    (((Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
      (markedForestEvent A j (n - k))).toReal / forestTail μ j (r - l))

theorem prefixDensity_eq_kernelDensity (μ : PMF ℕ) (A : Set ℕ) (n r : ℕ)
    (a : List ℕ) (hkn : prefixMarks A a ≤ n) :
    TreeDensity.prefixDensity μ A n r a =
      kernelDensity μ A n r a.length (prefixMarks A a) (prefixStack a) := by
  unfold TreeDensity.prefixDensity remainingMass kernelDensity
  rw [ite_eq_left hkn]

/-- Convergence of the marked deterministic-prefix density on every moving test sequence.
Here `B` is a total-size stable-domain norming, and `hscale` identifies it with
the canonical marked exploration scale at the chosen deterministic size clock. -/
theorem kernelDensity_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {q r l k j : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hqadm : ∀ i, ZetaAAdmissible μ A (q i)) (hr : Tendsto r atTop atTop)
    (hscale : Tendsto (fun i => markScale μ A θ (q i) / B (r i)) atTop (𝓝 1))
    {b x : ℝ} (_hb0 : 0 < b) (hb1 : b < 1) (hx : 0 < x)
    (hl : Tendsto (fun i => (l i : ℝ) / r i) atTop (𝓝 b))
    (hk : Tendsto (fun i => (k i : ℝ) / q i) atTop (𝓝 b))
    (hj : Tendsto (fun i => (j i : ℝ) / markScale μ A θ (q i)) atTop (𝓝 x))
    (hjpos : ∀ᶠ i in atTop, 1 ≤ j i)
    (hres : ∀ᶠ i in atTop, (arithFactor μ A : ℤ) ∣ ((q i - k i : ℕ) : ℤ) - j i) :
    Tendsto (fun i => kernelDensity μ A (q i) (r i) (l i) (k i) (j i)) atTop
      (𝓝 (gammaA θ b x)) := by
  have hs : 0 < 1 - b := sub_pos.mpr hb1
  have hu := remaining_count_ratio hq hb1 hk
  have hnum := moving_forest_limit h.critical h.nondegenerate hDA hA hq hs hu hj hjpos hres
  have hden := normalized_markedMass_tendsto h.critical h.nondegenerate hDA hA hq hqadm
  have htail := (treeTail_asymp h).comp hr
  have htail' : Tendsto (fun i => markScale μ A θ (q i) * forestTail μ 1 (r i)) atTop
      (𝓝 (θ * Scalar.stableDensity θ 0)) := by
    have ht := hscale.mul htail
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [hr.eventually h.isRealStableAttracted.pos] with i hi
    dsimp only [Function.comp_def]
    field_simp [hi.ne']
  have hjB : Tendsto (fun i => (j i : ℝ) / B (r i)) atTop (𝓝 x) := by
    have ht := hj.mul hscale
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [((markScale_atTop h.critical h.nondegenerate hDA hA).comp hq).eventually
      (eventually_gt_atTop 0)] with i hi
    change 0 < markScale μ A θ (q i) at hi
    field_simp [hi.ne']
  have hG := moving_forest_tail h hr hx hs hjB (remaining_count_ratio hr hb1 hl)
  have hD0 : (arithFactor μ A : ℝ) * Scalar.stableDensity θ 0 ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (GeneralA.Arithmetic.arithFactor_pos h.critical h.nondegenerate A).ne'
    · exact (Scalar.stableDensity_zero_pos h.alpha_mem).ne'
  have hG0 : BGW.StableTrees.sizeTailKernel θ (1 - b) x ≠ 0 :=
    (BGW.StableTrees.sizeTailKernel_pos h.alpha_mem hs hx).ne'
  have ht := (htail'.div hden hD0).mul (hnum.div hG hG0)
  have hconst : (θ * Scalar.stableDensity θ 0 /
      ((arithFactor μ A : ℝ) * Scalar.stableDensity θ 0)) *
      ((arithFactor μ A : ℝ) * qKernel θ (1 - b) x /
        BGW.StableTrees.sizeTailKernel θ (1 - b) x) = gammaA θ b x := by
    rw [ClassicalLimits.Cited.gammaA_eq_paper, ClassicalLimits.Cited.sizeTailKernel_eq_kernel]
    have he : (arithFactor μ A : ℝ) ≠ 0 := by
      exact_mod_cast (GeneralA.Arithmetic.arithFactor_pos h.critical h.nondegenerate A).ne'
    field_simp [he, (Scalar.stableDensity_zero_pos h.alpha_mem).ne']
  rw [hconst] at ht
  apply ht.congr'
  filter_upwards [hq.eventually_ne_atTop 0,
    ((markScale_atTop h.critical h.nondegenerate hDA hA).comp hq).eventually
      (eventually_gt_atTop 0)] with i hqi hi
  have hq0 : (q i : ℝ) ≠ 0 := by exact_mod_cast hqi
  change 0 < markScale μ A θ (q i) at hi
  dsimp only [Pi.div_apply, Function.comp_def, kernelDensity]
  field_simp [hq0, hi.ne']

end BGWLeaves.GeneralAFunctional.TreeKernel
