/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimit
public import BGW.StableTrees.DiscreteBridgeBasic
import BGW.Probability.Rounding

/-!
# Endpoint weights for exact-size prefixes

The endpoint recovers the pending stack by rounding the integer walk value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteBridge (endValue)

namespace BGW.StableTrees.ExactPrefix

open BGW BGW.Skorokhod BGW.Probability.RealWalk
open BGW.Probability

/-- The number of pending subtrees `j = W_m + 1` read off the path value at `a`. -/
noncomputable def prefixStack (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (x : D (a : ℝ) ℝ) : ℕ :=
  (round (endValue a x * B n) + 1).toNat

/-- The RN weight `R_n(m,j)` (K03 `exactPrefixWeight`) as a function of the prefix path,
`m = ⌊a n⌋`, `j = prefixStack`. -/
noncomputable def prefixWeightFn (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (x : D (a : ℝ) ℝ) : ℝ :=
  exactPrefixWeight μ n ⌊(a : ℝ) * n⌋₊ (prefixStack B n a x)

/-- The pending-stack count is measurable. -/
theorem measurable_prefixStack (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    Measurable (prefixStack B n a) := by
  exact (measurable_of_countable (fun z : ℤ => (z + 1).toNat)).comp
    (measurable_round.comp ((measurable_eval _).mul_const _))

/-- Measurability of the weight (a function of the value at `a` only). -/
theorem measurable_prefixWeightFn (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    Measurable (prefixWeightFn μ B n a) :=
  (measurable_of_countable (exactPrefixWeight μ n ⌊(a : ℝ) * n⌋₊)).comp
    (measurable_prefixStack B n a)

/-- Tail-prefix atoms are lattice-good: `j ≥ 1` and `d ∣ (n - m) - j` (every tree has size
`≡ 1 mod d`, increments are `≡ -1 mod d`). -/
def LatticeGood (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (x : D (a : ℝ) ℝ) : Prop :=
  1 ≤ prefixStack B n a x ∧
    ((Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - (⌊(a : ℝ) * n⌋₊ : ℕ) - (prefixStack B n a x : ℕ))

private theorem tendsto_gammaA_seq {θ a x : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : a < 1) (hx : 0 < x) {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun k => gammaA θ a (z k)) atTop (𝓝 (gammaA θ a x)) := by
  have hc : ContinuousAt (fun p : ℝ × ℝ => gammaA θ p.1 p.2) (a, x) :=
    (continuousOn_gammaA hθ).continuousAt
      ((isOpen_Iio.preimage continuous_fst).inter (isOpen_Ioi.preimage continuous_snd)
        |>.mem_nhds ⟨ha, hx⟩)
  exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds hz)

/-- **Weight convergence along sequences**: if `y_k → x` in `D a ℝ`, `x` is continuous at `a`
with `x(a) > 0`, and each `y_k` is lattice-good at the size `q k`, then
`R_{q k}(m, j(y_k)) → gammaA θ a (x a)` (K03 `exactPrefixWeight_uniform`). -/
theorem tendsto_prefixWeightFn_continuousConv {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    {x : D (a : ℝ) ℝ} (hx : ContinuousAt x ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩)
    (hxpos : 0 < endValue a x) {y : ℕ → D (a : ℝ) ℝ}
    (hy : ∀ k, LatticeGood μ B (q k) a (y k)) (hyx : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun k => prefixWeightFn μ B (q k) a (y k)) atTop
      (𝓝 (gammaA θ a (endValue a x))) := by
  have _hx := hx
  have he : Tendsto (fun k => endValue a (y k)) atTop (𝓝 (endValue a x)) :=
    ((lipschitzWith_one_eval_right (E := ℝ) a.coe_nonneg).continuous.tendsto x).comp hyx
  have hBtop : Tendsto (fun k => B (q k)) atTop atTop :=
    (Scalar.tendsto_atTop h).comp hqtop
  have hr := round_normalized_tendsto he hBtop
  have hj : Tendsto (fun k => (prefixStack B (q k) a (y k) : ℝ) / B (q k))
      atTop (𝓝 (endValue a x)) := by
    have ht := hr.add (hBtop.const_div_atTop (1 : ℝ))
    rw [add_zero] at ht
    convert ht using 1
    ext k
    have hz : 0 ≤ round (endValue a (y k) * B (q k)) + 1 := by
      have hp := (hy k).1
      unfold prefixStack at hp
      omega
    unfold prefixStack
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hz, Int.cast_add, Int.cast_one, add_div]
  have hgam : Tendsto (fun k => gammaA θ a
      ((prefixStack B (q k) a (y k) : ℝ) / B (q k))) atTop
      (𝓝 (gammaA θ a (endValue a x))) :=
    tendsto_gammaA_seq h.alpha_mem ha.2 hxpos hj
  have herr : Tendsto (fun k => prefixWeightFn μ B (q k) a (y k) -
      gammaA θ a ((prefixStack B (q k) a (y k) : ℝ) / B (q k))) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hevent := (exactPrefixWeight_uniform h
      (show (a : ℝ) ∈ Ioo 0 1 from ⟨ha.1, ha.2⟩)
      (half_pos hxpos) (show endValue a x / 2 ≤ endValue a x + 1 by linarith)
      (half_pos hε))
    have hlo := hj.eventually (Ioi_mem_nhds (show endValue a x / 2 < endValue a x by
      linarith))
    have hhi := hj.eventually (Iio_mem_nhds (show endValue a x < endValue a x + 1 by
      linarith))
    apply eventually_atTop.mp
    filter_upwards [hqtop.eventually hevent, hlo, hhi] with k hk hl hu
    rw [Real.dist_eq, sub_zero]
    exact (hk (hq k) _ hl.le hu.le (hy k).2).trans_lt (half_lt_self hε)
  simpa only [sub_add_cancel, zero_add] using herr.add hgam


end BGW.StableTrees.ExactPrefix
