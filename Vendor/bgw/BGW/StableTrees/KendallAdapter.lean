/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableKendall
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Kendall adapter and Gamma analytic interface

The time-first Kendall kernel is adapted from the passage-time density theorem.  Its
survival kernel is identified with the passage-time tail, and is proved finite, positive,
measurable, and jointly continuous on its natural domain.  The Gamma factor inherits the
corresponding regularity API.

Main declarations: `qKernel` (`q_s(x) = (x/s) p_s(-x)`), `passageLaw_eq_qKernel`,
`sizeTailKernelENN` and `sizeTailKernelENN_eq_passageLaw` (`G_r(x) = P(T_x > r)`), the integrable
dominator `qKernel_le_of_ge`, continuity and measurability lemmas, and `gammaA` with
`gammaA_mul_sizeTail`.

## References

* D. G. Kendall, *Some problems in the theory of dams*, J. Roy. Statist. Soc. Ser. B 19 (1957),
  207–212.
* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII (Corollary VII.3).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-! ### Definitions -/

/-- **The Kendall density** `q_s(x) = (x/s) p_s(-x)`, time first, level second (real arguments,
junk for `s ≤ 0`).  Same function as `kendallKernel θ x s`. -/
noncomputable def qKernel (θ s x : ℝ) : ℝ := (x / s) * stableDensityAt θ s (-x)

/-- **Survival (size-tail) kernel in the nonnegative-integral form**
`∫⁻_{s > r} q_s(x) ds` (primary definition, never junk). -/
noncomputable def sizeTailKernelENN (θ r x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi r, ENNReal.ofReal (qKernel θ s x)

/-- **Survival (size-tail) kernel** `G_r(x) = ∫_{s > r} q_s(x) ds` as a real integral
(equal to `(sizeTailKernelENN θ r x).toReal` for `r ≥ 0`, `x ≥ 0`, see
`ofReal_sizeTailKernel`). -/
noncomputable def sizeTailKernel (θ r x : ℝ) : ℝ := ∫ s in Ioi r, qKernel θ s x

/-- **The Gamma factor** `Γ_a(x) = θ q_{1-a}(x) / G_{1-a}(x)` of the path-only Γ identity. -/
noncomputable def gammaA (θ a x : ℝ) : ℝ :=
  θ * qKernel θ (1 - a) x / sizeTailKernel θ (1 - a) x

private theorem measurable_stableCF_aux (α : ℝ) : Measurable (Scalar.stableCF α) := by
  let f : ℝ → ℂ := fun t =>
    if 0 < t then
      Complex.exp ((((t ^ α : ℝ) : ℂ) *
        Complex.exp (((-(Real.pi * α / 2)) : ℝ) * Complex.I)))
    else if t < 0 then
      Complex.exp (((((-t) ^ α : ℝ) : ℂ) *
        Complex.exp (((Real.pi * α / 2) : ℝ) * Complex.I)))
    else Complex.exp (0 ^ (α : ℂ))
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.ite measurableSet_Ioi (by fun_prop)
    apply Measurable.ite measurableSet_Iio (by fun_prop) (by fun_prop)
  have heq : Scalar.stableCF α = f := by
    funext t
    by_cases ht : 0 < t
    · simp only [f, ht, ite_true]
      rw [Scalar.stableCF, Scalar.neg_mul_I_cpow_of_pos ht]
    · by_cases ht' : t < 0
      · simp only [f, ht, ite_false, ht', ite_true]
        rw [Scalar.stableCF, Scalar.neg_mul_I_cpow_of_neg ht']
      · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) (le_of_not_gt ht')
        subst t
        simp [f, Scalar.stableCF]
  rw [heq]
  exact hf

private theorem measurable_stableDensity_aux (α : ℝ) : Measurable (Scalar.stableDensity α) := by
  have hi : StronglyMeasurable (fun z : ℝ × ℝ =>
      Scalar.stableCF α z.2 * Complex.exp (-((z.2 : ℂ) * z.1 * Complex.I))) := by
    exact ((measurable_stableCF_aux α).comp measurable_snd).stronglyMeasurable.mul
      (by fun_prop)
  have hint : StronglyMeasurable (fun x : ℝ => ∫ t : ℝ,
      Scalar.stableCF α t * Complex.exp (-((t : ℂ) * x * Complex.I))) :=
    hi.integral_prod_right'
  exact (Complex.continuous_re.measurable.comp hint.measurable).const_mul _

private theorem measurable_stableDensityAt_aux (θ : ℝ) :
    Measurable (fun z : ℝ × ℝ => stableDensityAt θ z.1 z.2) := by
  unfold stableDensityAt
  exact (measurable_fst.pow_const _).mul
    ((measurable_stableDensity_aux θ).comp ((measurable_fst.pow_const _).mul measurable_snd))

private theorem measurable_qKernel_aux (θ : ℝ) :
    Measurable (fun z : ℝ × ℝ => qKernel θ z.1 z.2) := by
  exact (measurable_snd.div measurable_fst).mul
    ((measurable_stableDensityAt_aux θ).comp (measurable_fst.prodMk measurable_snd.neg))

/-! ### Adapter to the existing Kendall theorem -/

/-- `qKernel` is `kendallKernel` with the time argument first. -/
theorem qKernel_eq_kendallKernel (θ s x : ℝ) : qKernel θ s x = kendallKernel θ x s := rfl

/-- `qKernel` is nonnegative for `x ≥ 0`, `s > 0`. -/
theorem qKernel_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {s x : ℝ}
    (hs : 0 < s) (hx : 0 ≤ x) :
    0 ≤ qKernel θ s x := kendallKernel_nonneg hθ hx hs

/-- **Kendall's identity, time-first form.**  For `x > 0`,
`passageLaw θ x` has density `qKernel θ s x` on `s > 0` (and `0` elsewhere) w.r.t. Lebesgue
measure on `ℝ` (a restatement of `kendall`). -/
theorem passageLaw_eq_qKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) (hx : 0 < x) :
    passageLaw θ x = volume.withDensity
      (fun s => ENNReal.ofReal (if 0 < s then qKernel θ s x else 0)) := by
  rw [kendall hθ hx, ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext s
  by_cases hs : 0 < s <;> simp [qKernel, hs, Set.indicator]

/-! ### Survival kernel: finiteness and identification -/

/-- **The tail is the passage-time tail**: for `r ≥ 0`, `x > 0`,
`∫⁻_{s>r} q_s(x) = P(T_x > r)`. -/
theorem sizeTailKernelENN_eq_passageLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ}
    (hr : 0 ≤ r)
    (x : ℝ≥0) (hx : 0 < x) :
    sizeTailKernelENN θ r (x : ℝ) = passageLaw θ x (Ioi r) := by
  rw [sizeTailKernelENN, passageLaw_eq_qKernel hθ x hx, withDensity_apply _ measurableSet_Ioi]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  simp only [mem_Ioi] at hs
  rw [ite_eq_left (hr.trans_lt hs)]

/-- **Finiteness** of the survival kernel (it is at most `1`), for `r ≥ 0`, `x > 0`. -/
theorem sizeTailKernelENN_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 ≤ r)
    {x : ℝ}
    (hx : 0 < x) : sizeTailKernelENN θ r x < ⊤ := by
  let x' : ℝ≥0 := ⟨x, hx.le⟩
  have hx' : 0 < x' := hx
  let _ : IsProbabilityMeasure (passageLaw θ x') := passageLaw_isProbabilityMeasure hθ x'
  change sizeTailKernelENN θ r (x' : ℝ) < ⊤
  rw [sizeTailKernelENN_eq_passageLaw hθ hr x' hx']
  exact measure_lt_top _ _

/-- **Finiteness**, `x : ℝ≥0` form (same statement for the cast level). -/
theorem sizeTailKernelENN_lt_top_nnreal {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ}
    (hr : 0 ≤ r)
    {x : ℝ≥0} (hx : 0 < x) : sizeTailKernelENN θ r (x : ℝ) < ⊤ :=
  sizeTailKernelENN_lt_top hθ hr (NNReal.coe_pos.2 hx)

private theorem integrableOn_qKernel_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ}
    (hr : 0 ≤ r) {x : ℝ} (hx : 0 < x) : IntegrableOn (fun s => qKernel θ s x) (Ioi r) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi r)] fun s => qKernel θ s x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact qKernel_nonneg hθ (hr.trans_lt hs) hx.le
  refine ⟨((measurable_qKernel_aux θ).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable.restrict, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal hnonneg).2 (sizeTailKernelENN_lt_top hθ hr hx)

/-- **Conversion** between the real and nonnegative-integral survival kernels
(finite real-valued reading), for `r ≥ 0`, `x > 0`. -/
theorem ofReal_sizeTailKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 ≤ r)
    {x : ℝ}
    (hx : 0 < x) : ENNReal.ofReal (sizeTailKernel θ r x) = sizeTailKernelENN θ r x := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi r)] fun s => qKernel θ s x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact qKernel_nonneg hθ (hr.trans_lt hs) hx.le
  exact ofReal_integral_eq_lintegral_ofReal (integrableOn_qKernel_aux hθ hr hx) hnonneg

/-- **Joint continuity of `q`** in `(s, x)` on `s > 0` (adapter of `kendallKernel_continuousOn`). -/
theorem continuousOn_qKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => qKernel θ z.1 z.2) {z | 0 < z.1} := by
  have h := (kendallKernel_continuousOn hθ).comp continuous_swap.continuousOn
    (s := {z : ℝ × ℝ | 0 < z.1}) (fun z hz => hz)
  exact h

/-- **Positivity of the survival kernel**: `G_r(x) > 0` for `r > 0`, `x > 0`. -/
theorem sizeTailKernel_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hx : 0 < x) : 0 < sizeTailKernel θ r x := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hrpow : Tendsto (fun s : ℝ => s ^ (-1 / θ)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (one_div_pos.2 hθ0)
  have hscale : Tendsto (fun s : ℝ => s ^ (-1 / θ) * (-x)) atTop (𝓝 0) := by
    simpa using hrpow.mul_const (-x)
  have hp : ∀ᶠ s in atTop, 0 < Scalar.stableDensity θ (s ^ (-1 / θ) * (-x)) :=
    hscale.eventually ((Scalar.continuous_stableDensity hθ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds (Scalar.stableDensity_zero_pos hθ)))
  obtain ⟨s, hdens, hs⟩ := (hp.and (eventually_gt_atTop (max r 1))).exists
  have hsr : r < s := (le_max_left r 1).trans_lt hs
  have hspos : 0 < s := zero_lt_one.trans_le ((le_max_right r 1).trans hs.le)
  have hq : 0 < qKernel θ s x := by
    rw [qKernel, stableDensityAt]
    exact mul_pos (div_pos hx hspos)
      (mul_pos (Real.rpow_pos_of_pos hspos _) hdens)
  have hcont (t : ℝ) (ht : 0 < t) : ContinuousAt (fun u => qKernel θ u x) t := by
    have hc : ContinuousAt (fun z : ℝ × ℝ => qKernel θ z.1 z.2) (t, x) :=
      (continuousOn_qKernel hθ).continuousAt
        ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
    have hm : ContinuousAt (fun u : ℝ => (u, x)) t :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hccomp : ContinuousAt (fun u : ℝ => qKernel θ (u, x).1 (u, x).2) t :=
      ContinuousAt.comp' (f := fun u : ℝ => (u, x)) hc hm
    exact hccomp
  let U : Set ℝ := {t | 0 < ENNReal.ofReal (qKernel θ t x)} ∩ Ioi r
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have htr : r < t := ht.2
    have htp : 0 < t := hr.trans htr
    have hc : ContinuousAt (fun u => ENNReal.ofReal (qKernel θ u x)) t :=
      ENNReal.continuous_ofReal.continuousAt.comp (hcont t htp)
    exact ((hc.eventually (isOpen_Ioi.mem_nhds ht.1)).and
      (isOpen_Ioi.mem_nhds htr)).mono fun u hu => ⟨hu.1, hu.2⟩
  have hUs : s ∈ U := ⟨ENNReal.ofReal_pos.2 hq, hsr⟩
  have hUpos : 0 < volume U := hUopen.measure_pos volume ⟨s, hUs⟩
  have hsubset : U ⊆ Function.support (fun t => ENNReal.ofReal (qKernel θ t x)) ∩ Ioi r :=
    fun _ ht => ⟨ne_of_gt ht.1, ht.2⟩
  have hpos : 0 < sizeTailKernelENN θ r x := by
    apply (setLIntegral_pos_iff
      (((measurable_qKernel_aux θ).comp
        (measurable_id.prodMk measurable_const)).ennreal_ofReal)).2
    exact hUpos.trans_le (measure_mono hsubset)
  apply ENNReal.ofReal_pos.1
  rwa [ofReal_sizeTailKernel hθ hr.le hx]

/-! ### Continuity and local bounds -/

/-- **Local integrable dominator** (from `Scalar.exists_stableDensity_le`,
`q_s(x) = (x/s) p_s(-x)` and
`p_s ≤ M s^{-1/θ}`): for `r > 0` and `X ≥ 0` there is `C` (depending on `θ`, `r`, `X`) with
`q_s(x) ≤ C x s^{-1-1/θ}` for all `s ≥ r`, `0 ≤ x ≤ X`.  The right side is integrable on
`s ≥ r` (exponent `-1-1/θ < -1`), uniformly in `x ≤ X`. -/
theorem qKernel_le_of_ge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 < r) (X : ℝ) :
    ∃ C : ℝ, ∀ s, r ≤ s → ∀ x, 0 ≤ x → x ≤ X →
      qKernel θ s x ≤ C * x * s ^ (-1 - 1 / θ) := by
  -- `hθ` is part of the stated interface; the density bound holds for every exponent.
  have _hθ := hθ
  obtain ⟨C, -, hC⟩ := Scalar.exists_stableDensity_le (α := θ)
  refine ⟨C, fun s hs x hx _ => ?_⟩
  have hspos : 0 < s := hr.trans_le hs
  calc
    qKernel θ s x = (x / s) *
      (s ^ (-1 / θ) * Scalar.stableDensity θ (s ^ (-1 / θ) * (-x))) := rfl
    _ ≤ (x / s) * (s ^ (-1 / θ) * C) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hx hspos.le)
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hC _))
        (Real.rpow_nonneg hspos.le _)
    _ = C * x * s ^ (-1 - 1 / θ) := by
      rw [show -1 - 1 / θ = (-1 : ℝ) + (-1 / θ) by ring,
        Real.rpow_add hspos, Real.rpow_neg_one, div_eq_mul_inv]
      ring

/-- **Measurability** of `q` jointly in `(s, x)` on all of `ℝ × ℝ`. -/
theorem measurable_qKernel (θ : ℝ) : Measurable (fun z : ℝ × ℝ => qKernel θ z.1 z.2) :=
  measurable_qKernel_aux θ

/-- **Measurability** of the nonnegative size-tail kernel jointly in `(r, x)`
(parametric lintegral of the jointly measurable `measurable_qKernel`). -/
theorem measurable_sizeTailKernelENN (θ : ℝ) :
    Measurable (fun z : ℝ × ℝ => sizeTailKernelENN θ z.1 z.2) := by
  have hmeas : Measurable (fun w : (ℝ × ℝ) × ℝ =>
      (Ioi w.1.1).indicator (fun s => ENNReal.ofReal (qKernel θ s w.1.2)) w.2) := by
    exact (((measurable_qKernel_aux θ).comp
      (measurable_snd.prodMk measurable_fst.snd)).ennreal_ofReal).indicator
        (measurableSet_lt measurable_fst.fst measurable_snd)
  simpa only [sizeTailKernelENN, lintegral_indicator measurableSet_Ioi] using
    hmeas.lintegral_prod_right'

/-- **Mass one of the Kendall density**, in `qKernel` form (from `lintegral_kendallKernel`). -/
theorem lintegral_qKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (qKernel θ s x) = 1 :=
  lintegral_kendallKernel hθ hx

/-- **Joint continuity of the survival kernel** in `(r, x)` on `r > 0`, `x > 0`, by dominated
convergence with the integrable dominator of `qKernel_le_of_ge`. -/
theorem continuousOn_sizeTailKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => sizeTailKernel θ z.1 z.2) {z | 0 < z.1 ∧ 0 < z.2} := by
  rintro z ⟨hz1, hz2⟩
  let r₀ : ℝ := z.1 / 2
  let X : ℝ := z.2 + 1
  have hr₀ : 0 < r₀ := half_pos hz1
  have hr₀z : r₀ < z.1 := by dsimp [r₀]; linarith
  have hzX : z.2 < X := by dsimp [X]; linarith
  have hX : 0 < X := hz2.trans hzX
  obtain ⟨C, hC⟩ := qKernel_le_of_ge hθ hr₀ X
  let bound : ℝ → ℝ := (Ioi r₀).indicator (fun s => |C| * X * s ^ (-1 - 1 / θ))
  have ha : -1 - 1 / θ < -1 := by
    have : 0 < 1 / θ := one_div_pos.2 (by linarith [hθ.1])
    linarith
  have hb : Integrable bound := by
    exact IntegrableOn.integrable_indicator
      ((integrableOn_Ioi_rpow_of_lt ha hr₀).const_mul (|C| * X)) measurableSet_Ioi
  have hnear : ∀ᶠ z' in 𝓝 z, r₀ < z'.1 ∧ z'.2 < X :=
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_snd continuous_const)).mem_nhds ⟨hr₀z, hzX⟩
  have hnear' : ∀ᶠ z' in 𝓝[{w | 0 < w.1 ∧ 0 < w.2}] z, r₀ < z'.1 ∧ z'.2 < X :=
    hnear.filter_mono nhdsWithin_le_nhds
  have hmeas : ∀ᶠ z' in 𝓝[{w | 0 < w.1 ∧ 0 < w.2}] z,
      AEStronglyMeasurable
        (fun s => (Ioi z'.1).indicator (fun t => qKernel θ t z'.2) s) volume := by
    filter_upwards [] with z'
    exact (((measurable_qKernel θ).comp
      (measurable_id.prodMk measurable_const)).indicator measurableSet_Ioi).aestronglyMeasurable
  have hbound : ∀ᶠ z' in 𝓝[{w | 0 < w.1 ∧ 0 < w.2}] z, ∀ᵐ s : ℝ,
      ‖(Ioi z'.1).indicator (fun t => qKernel θ t z'.2) s‖ ≤ bound s := by
    filter_upwards [hnear', self_mem_nhdsWithin] with z' hznear hzS
    filter_upwards [] with s
    dsimp [bound]
    by_cases hs : s ∈ Ioi z'.1
    · have hs0 : 0 < s := hr₀.trans (hznear.1.trans hs)
      simp only [Set.indicator, mem_Ioi, hs, hznear.1.trans hs, ↓reduceIte,
        abs_of_nonneg (qKernel_nonneg hθ hs0 hzS.2.le)]
      calc
        qKernel θ s z'.2 ≤ C * z'.2 * s ^ (-1 - 1 / θ) :=
          hC s (hznear.1.trans hs).le z'.2 hzS.2.le hznear.2.le
        _ ≤ |C| * X * s ^ (-1 - 1 / θ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (le_abs_self C) hznear.2.le hzS.2.le (abs_nonneg C))
            (Real.rpow_nonneg hs0.le _)
    · by_cases hs0 : s ∈ Ioi r₀
      · simp only [Set.indicator, hs, hs0, ↓reduceIte]
        simpa using (mul_nonneg (mul_nonneg (abs_nonneg C) hX.le)
          (Real.rpow_nonneg (hr₀.trans hs0).le (-1 - 1 / θ)))
      · simp [Set.indicator, hs, hs0]
  have hlim : ∀ᵐ s : ℝ,
      Tendsto (fun z' => (Ioi z'.1).indicator (fun t => qKernel θ t z'.2) s)
        (𝓝[{w | 0 < w.1 ∧ 0 < w.2}] z)
        (𝓝 ((Ioi z.1).indicator (fun t => qKernel θ t z.2) s)) := by
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ z.1 := by
      simp [ae_iff]
    filter_upwards [hne] with s hs
    rcases lt_or_gt_of_ne hs with hsr | hrs
    · simp only [Set.indicator, mem_Ioi, not_lt_of_ge hsr.le, ↓reduceIte]
      have hev : ∀ᶠ z' in 𝓝[{w | 0 < w.1 ∧ 0 < w.2}] z, s < z'.1 :=
        (continuous_fst.continuousAt.eventually (Ioi_mem_nhds hsr)).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with z' hz'
      simp only [not_lt_of_ge hz'.le, ↓reduceIte]
    · simp only [Set.indicator, mem_Ioi, hrs, ↓reduceIte]
      have hs0 : 0 < s := hz1.trans hrs
      have hc : ContinuousAt (fun w : ℝ × ℝ => qKernel θ w.1 w.2) (s, z.2) :=
        (continuousOn_qKernel hθ).continuousAt
          ((isOpen_lt continuous_const continuous_fst).mem_nhds hs0)
      have hm : ContinuousAt (fun z' : ℝ × ℝ => (s, z'.2)) z :=
        (continuous_const.prodMk continuous_snd).continuousAt
      have hccomp : ContinuousAt (fun z' : ℝ × ℝ => qKernel θ (s, z'.2).1 (s, z'.2).2) z :=
        ContinuousAt.comp' (f := fun z' : ℝ × ℝ => (s, z'.2)) hc hm
      have hq : ContinuousAt (fun z' : ℝ × ℝ => qKernel θ s z'.2) z := hccomp
      have hev : ∀ᶠ z' in 𝓝[{w | 0 < w.1 ∧ 0 < w.2}] z, z'.1 < s :=
        (continuous_fst.continuousAt.eventually (Iio_mem_nhds hrs)).filter_mono nhdsWithin_le_nhds
      apply Tendsto.congr' ?_ hq.continuousWithinAt
      filter_upwards [hev] with z' hz'
      simp only [hz', ↓reduceIte]
  change Tendsto (fun z' : ℝ × ℝ => ∫ s in Ioi z'.1, qKernel θ s z'.2)
    (𝓝[{w | 0 < w.1 ∧ 0 < w.2}] z) (𝓝 (∫ s in Ioi z.1, qKernel θ s z.2))
  simpa only [integral_indicator measurableSet_Ioi] using
    tendsto_integral_filter_of_dominated_convergence bound hmeas hbound hb hlim

private theorem measurable_sizeTailKernel_aux (θ : ℝ) :
    Measurable (fun z : ℝ × ℝ => sizeTailKernel θ z.1 z.2) := by
  have hmeas : StronglyMeasurable (fun w : (ℝ × ℝ) × ℝ =>
      (Ioi w.1.1).indicator (fun s => qKernel θ s w.1.2) w.2) := by
    exact ((measurable_qKernel_aux θ).comp
      (measurable_snd.prodMk measurable_fst.snd)).stronglyMeasurable.indicator
        (measurableSet_lt measurable_fst.fst measurable_snd)
  simpa only [sizeTailKernel, integral_indicator measurableSet_Ioi] using
    hmeas.integral_prod_right'.measurable

/-- **Continuity of `Γ_a(x)`** jointly in `(a, x)` on `a < 1`, `x > 0` (quotient of continuous
functions with positive denominator `sizeTailKernel_pos`). -/
theorem continuousOn_gammaA {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => gammaA θ z.1 z.2) {z | z.1 < 1 ∧ 0 < z.2} := by
  have harg : ContinuousOn (fun z : ℝ × ℝ => (1 - z.1, z.2)) {z | z.1 < 1 ∧ 0 < z.2} :=
    (continuousOn_const.sub continuousOn_fst).prodMk continuousOn_snd
  have hq := (continuousOn_qKernel hθ).comp harg (fun z hz => sub_pos.2 hz.1)
  have hG := (continuousOn_sizeTailKernel hθ).comp harg
    (fun z hz => ⟨sub_pos.2 hz.1, hz.2⟩)
  exact (continuousOn_const.mul hq).div hG
    (fun z hz => (sizeTailKernel_pos hθ (sub_pos.2 hz.1) hz.2).ne')

/-- **Measurability** of `Γ` jointly in `(a, x)`. -/
theorem measurable_gammaA (θ : ℝ) : Measurable (fun z : ℝ × ℝ => gammaA θ z.1 z.2) := by
  have harg : Measurable (fun z : ℝ × ℝ => (1 - z.1, z.2)) :=
    (measurable_const.sub measurable_fst).prodMk measurable_snd
  exact (measurable_const.mul ((measurable_qKernel θ).comp harg)).div
    ((measurable_sizeTailKernel_aux θ).comp harg)

/-- **Defining identity** of `Γ`: `Γ_a(x) G_{1-a}(x) = θ q_{1-a}(x)` when `G_{1-a}(x) > 0`. -/
theorem gammaA_mul_sizeTail {θ a x : ℝ} (h : 0 < sizeTailKernel θ (1 - a) x) :
    gammaA θ a x * sizeTailKernel θ (1 - a) x = θ * qKernel θ (1 - a) x := by
  unfold gammaA
  exact div_mul_cancel₀ _ h.ne'

/-- **Nonnegativity of `Γ_a(x)`** for `a < 1`, `x > 0`. -/
theorem gammaA_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    0 ≤ gammaA θ a x := by
  exact div_nonneg
    (mul_nonneg (by linarith [hθ.1]) (qKernel_nonneg hθ (sub_pos.2 ha) hx.le))
    (sizeTailKernel_pos hθ (sub_pos.2 ha) hx).le

end BGW.StableTrees
