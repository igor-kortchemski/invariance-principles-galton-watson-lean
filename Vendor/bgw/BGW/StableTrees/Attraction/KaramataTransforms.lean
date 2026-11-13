/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.SlowVariation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Restricted Laplace–Stieltjes Karamata theorem

`RegularlyVarying U ρ` means eventual strict positivity and convergence of
`U (c*x) / U x` to `c^ρ` at infinity, for every `c > 0`.  The reciprocal
parameterization `x ↦ F (1/x)` will be used for variation at zero.

The cumulative function includes the atom at zero. All transforms are restricted
to the nonnegative half line; mass on the negative half line is irrelevant.

`laplace_karamata` proves both directions for `0 ≤ ρ < 1`;
`laplace_karamata_normalization` gives the exact Gamma constant.
The Abelian proof uses monotonicity, doubling, and an exponential majorant.
The Tauberian proof exponentially tilts and compactifies, uses polynomial
approximation, and sandwiches the bounded discontinuous cutoff between
continuous functions. The index-zero limit is an atom and is handled separately.
Ported from `BGWLeaves/StableAnalysis/KaramataTransforms.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.KaramataTransforms

/-- Function regular variation at infinity, including eventual positivity. -/
def RegularlyVarying (U : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < U x) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => U (c * x) / U x) atTop (𝓝 (c ^ ρ))

/-- Regular variation at zero through reciprocal parameterization. Equivalently,
the ratios `F (c*s) / F s` converge to `c^κ` as `s` decreases to zero. -/
def RegularlyVaryingAtZero (F : ℝ → ℝ) (κ : ℝ) : Prop :=
  RegularlyVarying (fun x => F (1 / x)) (-κ)

/-- The cumulative mass, including the possible atom at zero. -/
noncomputable def cumulative (M : Measure ℝ) (x : ℝ) : ℝ := M.real (Icc 0 x)

/-- The Laplace–Stieltjes transform on the nonnegative half line. Its use as a
finite transform requires integrability, not just a value of this total integral. -/
noncomputable def laplace (M : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ y in Ici 0, Real.exp (-s * y) ∂M

theorem regularlyVarying_zero_iff {U : ℝ → ℝ} :
    RegularlyVarying U 0 ↔ (∀ᶠ x in atTop, 0 < U x) ∧ BGW.StableTrees.SlowlyVarying U := by
  simp [RegularlyVarying, BGW.StableTrees.SlowlyVarying]

theorem cumulative_nonneg (M : Measure ℝ) (x : ℝ) : 0 ≤ cumulative M x :=
  ENNReal.toReal_nonneg

theorem cumulative_monotone (M : Measure ℝ) [IsLocallyFiniteMeasure M] :
    Monotone (cumulative M) := by
  intro x y hxy
  exact ENNReal.toReal_mono (isCompact_Icc.measure_lt_top.ne)
    (measure_mono (Icc_subset_Icc_right hxy))

/-- Below index one, doubling can eventually be bounded by the factor two.
This bound is intentionally coarse: it gives exponential domination directly. -/
theorem RegularlyVarying.eventually_doubling_le {U : ℝ → ℝ} {ρ : ℝ}
    (h : RegularlyVarying U ρ) (hρ : ρ < 1) :
    ∀ᶠ x in atTop, U (2 * x) ≤ 2 * U x := by
  have hp : (2 : ℝ) ^ ρ < 2 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hρ
  filter_upwards [h.1, (h.2 2 (by norm_num)).eventually (gt_mem_nhds hp)] with x hx hr
  exact (div_lt_iff₀ hx).1 hr |>.le

/-- Monotonicity and a doubling bound give a single integrable exponential
majorant for the Abelian rescaling. -/
theorem ratio_le_exp_of_doubling {U : ℝ → ℝ} (hmono : Monotone U)
    {X x : ℝ} (hdouble : ∀ y, X ≤ y → U (2 * y) ≤ 2 * U y)
    (hxX : X ≤ x) (hx : 0 < x) (hUx : 0 < U x) {t : ℝ} (ht : 0 ≤ t) :
    U (t * x) / U x ≤ Real.exp (Real.log 2 * t) := by
  have hn : ∀ n : ℕ, U (((n : ℝ) + 1) * x) ≤ (2 : ℝ) ^ n * U x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hbase : X ≤ ((n : ℝ) + 1) * x := by
        have := Nat.cast_nonneg (α := ℝ) n
        nlinarith
      have hm : U ((((n + 1 : ℕ) : ℝ) + 1) * x) ≤
          U (2 * (((n : ℝ) + 1) * x)) := by
        apply hmono
        push_cast
        have := Nat.cast_nonneg (α := ℝ) n
        nlinarith
      calc
        _ ≤ 2 * U (((n : ℝ) + 1) * x) := hm.trans (hdouble _ hbase)
        _ ≤ 2 * ((2 : ℝ) ^ n * U x) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (n + 1) * U x := by rw [pow_succ]; ring
  have hb : U (t * x) ≤ (2 : ℝ) ^ ⌊t⌋₊ * U x :=
    (hmono (mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one t).le hx.le)).trans (hn _)
  have he : (2 : ℝ) ^ ⌊t⌋₊ ≤ Real.exp (Real.log 2 * t) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Nat.floor_le ht)
      (Real.log_nonneg (by norm_num)))
  exact (div_le_iff₀ hUx).2 (hb.trans (mul_le_mul_of_nonneg_right he hUx.le))

/-- Abelian dominated convergence for the cumulative integral. This includes
`ρ = 0`; the limiting integrand is then just the exponential density. -/
theorem cumulative_integral_limit {U : ℝ → ℝ} {ρ : ℝ}
    (hnonneg : ∀ x, 0 ≤ U x) (hmono : Monotone U)
    (h : RegularlyVarying U ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun x : ℝ => ∫ t in Ioi (0 : ℝ),
      Real.exp (-t) * (U (t * x) / U x)) atTop (𝓝 (Real.Gamma (1 + ρ))) := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 (h.eventually_doubling_le hρ1)
  have hlog : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1; norm_num
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 0 ≤ t →
      ‖Real.exp (-t) * (U (t * x) / U x)‖ ≤
        Real.exp ((Real.log 2 - 1) * t) := by
    filter_upwards [eventually_ge_atTop X, eventually_gt_atTop (0 : ℝ), h.1] with x hx hx0 hxU t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (div_nonneg (hnonneg _) hxU.le))]
    calc
      _ ≤ Real.exp (-t) * Real.exp (Real.log 2 * t) :=
        mul_le_mul_of_nonneg_left (ratio_le_exp_of_doubling hmono hX hx hx0 hxU ht)
          (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (fun t => Real.exp ((Real.log 2 - 1) * t))
    (Eventually.of_forall fun x =>
      ((Real.measurable_exp.comp measurable_neg).mul
        ((hmono.measurable.comp (measurable_id.mul_const x)).div_const (U x))).aestronglyMeasurable)
    (hbound.mono fun x hx => (ae_restrict_mem measurableSet_Ioi).mono fun t ht => hx t ht.le)
    (integrableOn_exp_mul_Ioi (by linarith) 0)
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
      (h.2 t ht).const_mul (Real.exp (-t)))
  simpa only [Function.comp_def, Pi.mul_apply,
    Real.Gamma_eq_integral (by linarith : 0 < 1 + ρ), add_sub_cancel_left, id_eq] using hlim

/-- Fubini's cumulative-integral formula, with the atom at zero retained. -/
theorem laplace_eq_cumulative_integral (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {s : ℝ} (hs : 0 < s)
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M) :
    laplace M s = s * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * cumulative M t := by
  let μ := M.restrict (Ici 0)
  let ν := volume.restrict (Ici (0 : ℝ))
  let k : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then Real.exp (-s * p.2) else 0
  have hkm : Measurable k :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).ite
      (measurableSet_le measurable_fst measurable_snd) measurable_const
  have hi : Integrable (fun t => Real.exp (-s * t)) ν :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0)
  have hslice (y : ℝ) : Integrable (fun t => k (y, t)) ν := by
    exact (hi.indicator (measurableSet_Ici (a := y)))
  have hsliceeq (y : ℝ) (hy : 0 ≤ y) :
      (∫ t, k (y, t) ∂ν) = Real.exp (-s * y) / s := by
    change (∫ t, (Ici y).indicator (fun t => Real.exp (-s * t)) t ∂ν) = _
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    rw [show Ici y ∩ Ici (0 : ℝ) = Ici y from inter_eq_left.2 (Ici_subset_Ici.2 hy)]
    rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_of_pos hs)]
    ring
  have hki : Integrable k (μ.prod ν) := by
    apply (integrable_prod_iff hkm.aestronglyMeasurable).2
    refine ⟨Eventually.of_forall hslice, ?_⟩
    apply (hfinite.div_const s).congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    rw [show (fun t => ‖k (y, t)‖) = fun t => k (y, t) from funext fun t => by
      dsimp [k]; split_ifs <;> simp]
    exact (hsliceeq y hy).symm
  have hswap := integral_integral_swap (f := fun y t => k (y, t)) hki
  have hleft : (∫ y, ∫ t, k (y, t) ∂ν ∂μ) = laplace M s / s := by
    rw [laplace, ← integral_div]
    exact integral_congr_ae ((ae_restrict_mem measurableSet_Ici).mono fun y hy => hsliceeq y hy)
  have hright : (∫ t, ∫ y, k (y, t) ∂μ ∂ν) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * cumulative M t := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    change (∫ y, (Iic t).indicator (fun _ => Real.exp (-s * t)) y ∂μ) = _
    rw [integral_indicator_const _ measurableSet_Iic]
    rw [measureReal_restrict_apply measurableSet_Iic, Iic_inter_Ici, smul_eq_mul, mul_comm]
    rfl
  rw [hleft, hright] at hswap
  exact (div_eq_iff hs.ne').1 hswap |>.trans (mul_comm _ _)

/-- Change of variables in the cumulative-integral formula. -/
theorem laplace_reciprocal_eq (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {x : ℝ} (hx : 0 < x)
    (hfinite : IntegrableOn (fun y => Real.exp (-(1 / x) * y)) (Ici 0) M) :
    laplace M (1 / x) = ∫ t in Ioi (0 : ℝ), Real.exp (-t) * cumulative M (t * x) := by
  rw [laplace_eq_cumulative_integral M (one_div_pos.2 hx) hfinite]
  have hsub := integral_comp_mul_left_Ioi
    (fun t => Real.exp (-(1 / x) * t) * cumulative M t) 0 hx
  simp only [mul_zero, smul_eq_mul, ← one_div] at hsub
  rw [← hsub]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp
    field_simp

/-- Abelian half of the restricted Laplace–Stieltjes Karamata theorem,
including its exact Gamma constant and the endpoint index zero. -/
theorem laplace_abelian_ratio (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hU : RegularlyVarying (cumulative M) ρ) :
    Tendsto (fun x => laplace M (1 / x) / cumulative M x) atTop
      (𝓝 (Real.Gamma (1 + ρ))) := by
  apply (cumulative_integral_limit (cumulative_nonneg M) (cumulative_monotone M)
    hU hρ0 hρ1).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [laplace_reciprocal_eq M hx (hfinite _ (one_div_pos.2 hx)), ← integral_div]
  congr 1
  funext t
  ring

/-- Regular variation is preserved by a strictly positive asymptotic multiplier. -/
theorem RegularlyVarying.of_ratio {U V : ℝ → ℝ} {ρ C : ℝ}
    (hU : RegularlyVarying U ρ) (hC : 0 < C)
    (hVU : Tendsto (fun x => V x / U x) atTop (𝓝 C)) :
    RegularlyVarying V ρ := by
  have hV : ∀ᶠ x in atTop, 0 < V x := by
    filter_upwards [hU.1, hVU.eventually (lt_mem_nhds hC)] with x hx hr
    exact (div_pos_iff.1 hr).resolve_right (by intro hh; linarith [hh.2]) |>.1
  refine ⟨hV, fun c hc => ?_⟩
  have hscale : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hlim := ((hVU.comp hscale).mul (hU.2 c hc)).div hVU hC.ne'
  have heq : C * c ^ ρ / C = c ^ ρ := by field_simp
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards [hU.1, hscale.eventually hU.1, hV] with x hx hcx hv
  dsimp
  field_simp

/-- The Abelian regular-variation conclusion at zero. -/
theorem laplace_abelian (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hU : RegularlyVarying (cumulative M) ρ) :
    RegularlyVaryingAtZero (laplace M) (-ρ) := by
  rw [RegularlyVaryingAtZero, neg_neg]
  exact hU.of_ratio (Real.Gamma_pos_of_pos (by linarith))
    (laplace_abelian_ratio M hρ0 hρ1 hfinite hU)

/-- Exact normalization, in the ratio-one form of asymptotic equivalence. -/
theorem laplace_abelian_normalization (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hU : RegularlyVarying (cumulative M) ρ) :
    Tendsto (fun x => cumulative M x / (laplace M (1 / x) / Real.Gamma (1 + ρ)))
      atTop (𝓝 1) := by
  have hG : 0 < Real.Gamma (1 + ρ) := Real.Gamma_pos_of_pos (by linarith)
  have hlim := (laplace_abelian_ratio M hρ0 hρ1 hfinite hU).inv₀ hG.ne'
  have hlim' := hlim.const_mul (Real.Gamma (1 + ρ))
  rw [mul_inv_cancel₀ hG.ne'] at hlim'
  apply hlim'.congr (fun x => ?_)
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The polynomial-approximation step of the Tauberian argument. Uniformly
bounded linear functionals on a compact real set converge on every continuous
function as soon as they converge on all monomials. -/
theorem tendsto_functional_of_monomials {ι : Type*} {l : Filter ι}
    {K : Set ℝ} [CompactSpace K]
    (L : ι → C(K, ℝ) →L[ℝ] ℝ) (L₀ : C(K, ℝ) →L[ℝ] ℝ)
    (hbound : ∀ i, ‖L i‖ ≤ 1)
    (hmom : ∀ n : ℕ, Tendsto (fun i => L i ((ContinuousMap.restrict K (.id ℝ)) ^ n))
      l (𝓝 (L₀ ((ContinuousMap.restrict K (.id ℝ)) ^ n))))
    (f : C(K, ℝ)) : Tendsto (fun i => L i f) l (𝓝 (L₀ f)) := by
  have hequi : Equicontinuous (fun i (g : C(K, ℝ)) => L i g) := by
    intro g
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun q hq i => ?_⟩
    calc
      dist (L i g) (L i q) ≤ ‖L i‖ * dist g q := (L i).dist_le_opNorm _ _
      _ ≤ 1 * dist g q := mul_le_mul_of_nonneg_right (hbound i) dist_nonneg
      _ < ε := by simpa only [one_mul, dist_comm] using hq
  have hclosed := hequi.isClosed_setOfPred_tendsto (l := l) L₀.continuous
  have hdense : f ∈ closure (polynomialFunctions K : Set C(K, ℝ)) := by
    change f ∈ (polynomialFunctions K).topologicalClosure
    rw [polynomialFunctions.topologicalClosure]
    trivial
  apply (closure_minimal (t := {g | Tendsto (fun i => L i g) l (𝓝 (L₀ g))}) ?_ hclosed) hdense
  intro g hg
  rw [polynomialFunctions_coe] at hg
  obtain ⟨p, rfl⟩ := hg
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Set.mem_ofPred_eq, map_add] using hp.add hq
  | monomial n a =>
    have heq : Polynomial.toContinuousMapOnAlgHom K (Polynomial.monomial n a) =
        a • ((ContinuousMap.restrict K (.id ℝ)) ^ n) := by
      ext x
      simp
    rw [heq]
    simpa only [Set.mem_ofPred_eq, map_smul, smul_eq_mul] using (hmom n).const_mul a

/-- Monomials after exponential tilting are Laplace transforms at integer
multiples of the parameter. This identity does not require a limiting argument. -/
theorem tilted_monomial_integral (M : Measure ℝ) (s : ℝ) (n : ℕ) :
    (∫ y in Ici (0 : ℝ), Real.exp (-s * y) * Real.exp (-s * y) ^ n ∂M) =
      laplace M (((n : ℝ) + 1) * s) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring

/-- Transform regular variation supplies all moments needed after exponential
tilting and the substitution `t = exp (-y/x)`. -/
theorem tilted_monomial_limit (M : Measure ℝ) {ρ : ℝ}
    (hF : RegularlyVaryingAtZero (laplace M) (-ρ)) (n : ℕ) :
    Tendsto (fun x : ℝ =>
      (∫ y in Ici (0 : ℝ), Real.exp (-(1 / x) * y) *
        Real.exp (-(1 / x) * y) ^ n ∂M) / laplace M (1 / x))
      atTop (𝓝 ((1 / ((n : ℝ) + 1)) ^ ρ)) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have h := hF.2 (1 / ((n : ℝ) + 1)) (one_div_pos.2 hn)
  simp only [neg_neg] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [tilted_monomial_integral]
  congr 2
  field_simp

/-- Exponential compactification. The extension to negative arguments makes
this a continuous map on the whole real line. On nonnegative arguments it is
exactly `y ↦ exp (-y)`. -/
noncomputable def expUnit (y : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-max 0 y), (Real.exp_pos _).le,
    Real.exp_le_one_iff.2 (neg_nonpos.2 (le_max_left _ _))⟩

@[fun_prop] theorem continuous_expUnit : Continuous expUnit := by
  apply Continuous.subtype_mk
  exact Real.continuous_exp.comp (continuous_const.max continuous_id).neg

theorem expUnit_coe {y : ℝ} (hy : 0 ≤ y) : (expUnit y : ℝ) = Real.exp (-y) := by
  simp [expUnit, max_eq_right hy]

private theorem tilted_test_norm_bound (s y : ℝ) (f : C(Icc (0 : ℝ) 1, ℝ)) :
    ‖Real.exp (-s * y) * f (expUnit (s * y))‖ ≤ ‖f‖ * Real.exp (-s * y) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le

theorem tilted_test_integrable (M : Measure ℝ) {s : ℝ}
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (f : C(Icc (0 : ℝ) 1, ℝ)) :
    IntegrableOn (fun y => Real.exp (-s * y) * f (expUnit (s * y))) (Ici 0) M := by
  apply (hfinite.const_mul ‖f‖).mono'
  · have hc : Continuous (fun y : ℝ => Real.exp (-s * y) * f (expUnit (s * y))) := by
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Eventually.of_forall fun y => tilted_test_norm_bound s y f

/-- The normalized exponentially tilted integral, as a bounded linear
functional on the compact interval. -/
noncomputable def tiltedFunctional (M : Measure ℝ) {s : ℝ}
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hpos : 0 < laplace M s) : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => (∫ y in Ici (0 : ℝ),
          Real.exp (-s * y) * f (expUnit (s * y)) ∂M) / laplace M s
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, mul_add]
        rw [integral_add (tilted_test_integrable M hfinite f)
          (tilted_test_integrable M hfinite g), add_div]
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm (Real.exp (-s * _)) a]
        rw [integral_const_mul]
        ring }
    1 (fun f => by
      change ‖(∫ y in Ici (0 : ℝ), Real.exp (-s * y) * f (expUnit (s * y)) ∂M) /
        laplace M s‖ ≤ 1 * ‖f‖
      simp only [one_mul, norm_div, Real.norm_eq_abs, abs_of_pos hpos]
      apply (div_le_iff₀ hpos).2
      calc
        _ ≤ ∫ y in Ici (0 : ℝ), ‖f‖ * Real.exp (-s * y) ∂M :=
          norm_integral_le_of_norm_le (hfinite.const_mul ‖f‖)
            (Eventually.of_forall fun y => tilted_test_norm_bound s y f)
        _ = ‖f‖ * laplace M s := integral_const_mul _ _)

theorem tiltedFunctional_apply (M : Measure ℝ) {s : ℝ}
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hpos : 0 < laplace M s) (f : C(Icc (0 : ℝ) 1, ℝ)) :
    tiltedFunctional M hfinite hpos f = (∫ y in Ici (0 : ℝ),
      Real.exp (-s * y) * f (expUnit (s * y)) ∂M) / laplace M s := rfl

theorem tiltedFunctional_norm_le (M : Measure ℝ) {s : ℝ}
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hpos : 0 < laplace M s) : ‖tiltedFunctional M hfinite hpos‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem tiltedFunctional_nonneg (M : Measure ℝ) {s : ℝ}
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hpos : 0 < laplace M s) {f : C(Icc (0 : ℝ) 1, ℝ)} (hf : ∀ t, 0 ≤ f t) :
    0 ≤ tiltedFunctional M hfinite hpos f := by
  rw [tiltedFunctional_apply]
  exact div_nonneg (integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (hf _)) hpos.le

theorem tiltedFunctional_mono (M : Measure ℝ) {s : ℝ}
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hpos : 0 < laplace M s) {f g : C(Icc (0 : ℝ) 1, ℝ)} (hfg : ∀ t, f t ≤ g t) :
    tiltedFunctional M hfinite hpos f ≤ tiltedFunctional M hfinite hpos g := by
  have hh := tiltedFunctional_nonneg M hfinite hpos
    (f := g - f) (fun t => sub_nonneg.2 (hfg t))
  rw [map_sub] at hh
  exact sub_nonneg.1 hh

theorem tiltedFunctional_monomial (M : Measure ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hfinite : IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hpos : 0 < laplace M s) (n : ℕ) :
    tiltedFunctional M hfinite hpos ((ContinuousMap.restrict (Icc (0 : ℝ) 1) (.id ℝ)) ^ n) =
      laplace M (((n : ℝ) + 1) * s) / laplace M s := by
  rw [tiltedFunctional_apply, ← tilted_monomial_integral M s n]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  simp only [ContinuousMap.pow_apply, ContinuousMap.restrict_apply, ContinuousMap.id_apply,
    expUnit_coe (mul_nonneg hs hy), neg_mul]

/-- The Gamma model has exactly the tilted moments prescribed by transform
regular variation. The index-zero model is instead the atom at `1`. -/
theorem gamma_monomial_integral {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    (∫ y in Ioi (0 : ℝ),
      (Real.exp (-y) * Real.exp (-y) ^ n * y ^ (ρ - 1)) / Real.Gamma ρ) =
      (1 / ((n : ℝ) + 1)) ^ ρ := by
  rw [integral_div]
  have heq : (fun y : ℝ => Real.exp (-y) * Real.exp (-y) ^ n * y ^ (ρ - 1)) =
      fun y => y ^ (ρ - 1) * Real.exp (-(((n : ℝ) + 1) * y)) := by
    funext y
    rw [← Real.exp_nat_mul, ← Real.exp_add, mul_comm]
    congr 2
    ring
  rw [heq, Real.integral_rpow_mul_exp_neg_mul_Ioi hρ (by positivity)]
  exact mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hρ).ne'

/-- The value of the de-tilted Gamma cutoff, including its normalization. -/
theorem gamma_cutoff_integral {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ y in Icc (0 : ℝ) 1, y ^ (ρ - 1) / Real.Gamma ρ) =
      1 / Real.Gamma (1 + ρ) := by
  rw [integral_div, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith : -1 < ρ - 1))]
  simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hρ.ne', sub_zero]
  rw [show 1 + ρ = ρ + 1 by ring, Real.Gamma_add_one hρ.ne']
  ring

/-- A universal constant for the index-zero cutoff estimate. -/
noncomputable def cutoffBound : ℝ :=
  max (Real.exp 1) (1 / (1 - Real.exp (-1)))

private theorem cutoffBound_pos : 0 < cutoffBound :=
  (Real.exp_pos 1).trans_le (le_max_left _ _)

private theorem cutoff_bound {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    |(if Real.exp (-1) ≤ w then (1 : ℝ) else 0) - w| ≤ cutoffBound * (w - w ^ 2) := by
  have ha0 : 0 < 1 - Real.exp (-1) := by
    have := Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0)
    linarith
  by_cases ha : Real.exp (-1) ≤ w
  · rw [ite_eq_left ha, abs_of_nonneg (by linarith)]
    have hcw : 1 ≤ cutoffBound * w := by
      calc
        1 = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
        _ ≤ cutoffBound * w :=
          mul_le_mul (le_max_left _ _) ha (Real.exp_pos _).le cutoffBound_pos.le
    nlinarith [mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hcw)]
  · rw [ite_eq_right ha, zero_sub, abs_neg, abs_of_pos hw]
    have hc : 1 / (1 - Real.exp (-1)) ≤ cutoffBound := le_max_right _ _
    have hcw : 1 ≤ cutoffBound * (1 - w) := by
      have hca : 1 ≤ cutoffBound * (1 - Real.exp (-1)) := (div_le_iff₀ ha0).1 hc
      have haw : w ≤ Real.exp (-1) := (lt_of_not_ge ha).le
      nlinarith [mul_nonneg cutoffBound_pos.le (sub_nonneg.2 haw)]
    nlinarith [mul_nonneg hw.le (sub_nonneg.2 hcw)]

/-- A quantitative Tauberian estimate at index zero: the cumulative mass is
controlled by the first two Laplace transforms. -/
theorem cumulative_laplace_bound (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {x : ℝ} (hx : 0 < x)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M) :
    |cumulative M x - laplace M (1 / x)| ≤
      cutoffBound * (laplace M (1 / x) - laplace M (2 * (1 / x))) := by
  let μ := M.restrict (Ici 0)
  let a : ℝ → ℝ := (Iic x).indicator (fun _ => 1)
  let w : ℝ → ℝ := fun y => Real.exp (-(1 / x) * y)
  have hi : Integrable a μ := by
    apply (integrable_indicator_iff measurableSet_Iic).2
    exact integrableOn_const (C := (1 : ℝ)) (by
      rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ici]
      exact isCompact_Icc.measure_lt_top.ne)
  have hw : Integrable w μ := hfinite _ (one_div_pos.2 hx)
  have hw2 := hfinite (2 * (1 / x)) (by positivity)
  have heq (y : ℝ) : Real.exp (-(2 * (1 / x)) * y) = w y ^ 2 := by
    change Real.exp (-(2 * (1 / x)) * y) = Real.exp (-(1 / x) * y) ^ 2
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hb : ∀ᵐ y ∂μ, ‖a y - w y‖ ≤ cutoffBound *
      (w y - Real.exp (-(2 * (1 / x)) * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    have hwy : w y ≤ 1 := Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (one_div_pos.2 hx).le) hy)
    have ht : Real.exp (-1) ≤ w y ↔ y ≤ x := by
      change Real.exp (-1) ≤ Real.exp (-(1 / x) * y) ↔ y ≤ x
      rw [Real.exp_le_exp, show -(1 / x) * y = -(y / x) by ring,
        neg_le_neg_iff, div_le_one hx]
    rw [heq, Real.norm_eq_abs]
    change |(if y ≤ x then 1 else 0) - w y| ≤ cutoffBound * (w y - w y ^ 2)
    have hbw := cutoff_bound (Real.exp_pos (-(1 / x) * y)) hwy
    change |(if Real.exp (-1) ≤ w y then 1 else 0) - w y| ≤ cutoffBound * (w y - w y ^ 2) at hbw
    simpa only [ht] using hbw
  have hnorm := norm_integral_le_of_norm_le ((hw.sub hw2).const_mul cutoffBound) hb
  rw [integral_sub hi hw, integral_const_mul] at hnorm
  simp only [Pi.sub_apply] at hnorm
  rw [integral_sub hw hw2] at hnorm
  have ha : (∫ y, a y ∂μ) = cumulative M x := by
    rw [integral_indicator_const _ measurableSet_Iic,
      measureReal_restrict_apply measurableSet_Iic, Iic_inter_Ici, smul_eq_mul, mul_one]
    rfl
  simpa only [ha, Real.norm_eq_abs, laplace, μ, w] using hnorm

/-- The Tauberian ratio theorem at the boundary index zero. Concentration of
the tilted law follows from its first moment, so no Gamma density is needed. -/
theorem laplace_tauberian_zero_ratio (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) 0) :
    Tendsto (fun x => cumulative M x / laplace M (1 / x)) atTop (𝓝 1) := by
  have htwo : Tendsto (fun x : ℝ => laplace M (2 * (1 / x)) / laplace M (1 / x))
      atTop (𝓝 1) := by
    have hh := hF.2 (1 / 2) (by norm_num)
    simp only [neg_zero, Real.rpow_zero] at hh
    apply hh.congr (fun x => ?_)
    congr 2
    ring
  have hlim : Tendsto (fun x : ℝ => cutoffBound *
      (1 - laplace M (2 * (1 / x)) / laplace M (1 / x))) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub htwo).const_mul cutoffBound
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ), hF.1] with x hx hFx
  have hb := (div_le_div_of_nonneg_right (cumulative_laplace_bound M hx hfinite) hFx.le)
  have heq : cumulative M x / laplace M (1 / x) - 1 =
      (cumulative M x - laplace M (1 / x)) / laplace M (1 / x) := by
    field_simp
  rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hFx]
  convert hb using 1
  field_simp

/-- The Tauberian regular-variation conclusion at index zero. -/
theorem laplace_tauberian_zero (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) 0) :
    RegularlyVarying (cumulative M) 0 := by
  have hF' : RegularlyVarying (fun x => laplace M (1 / x)) 0 := by
    simpa only [RegularlyVaryingAtZero, neg_zero] using hF
  exact hF'.of_ratio zero_lt_one (laplace_tauberian_zero_ratio M hfinite hF)

/-- Both directions of the Laplace–Stieltjes Karamata theorem at index zero. -/
theorem laplace_karamata_zero (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M) :
    RegularlyVaryingAtZero (laplace M) 0 ↔ RegularlyVarying (cumulative M) 0 := by
  refine ⟨laplace_tauberian_zero M hfinite, fun hU => ?_⟩
  simpa only [neg_zero] using laplace_abelian M le_rfl zero_lt_one hfinite hU

/-- Continuous-test convergence for exponentially tilted laws, once the model
functional with Gamma moments has been specified. The model is a bounded linear
functional, not an assumption about the cumulative function or its limit. -/
theorem tilted_continuous_test_limit (M : Measure ℝ) {ρ : ℝ}
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) (-ρ))
    (L₀ : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ)
    (hmodel : ∀ n : ℕ, L₀ ((ContinuousMap.restrict (Icc (0 : ℝ) 1) (.id ℝ)) ^ n) =
      (1 / ((n : ℝ) + 1)) ^ ρ)
    (f : C(Icc (0 : ℝ) 1, ℝ)) :
    Tendsto (fun x : ℝ => (∫ y in Ici (0 : ℝ),
      Real.exp (-(1 / x) * y) * f (expUnit ((1 / x) * y)) ∂M) / laplace M (1 / x))
      atTop (𝓝 (L₀ f)) := by
  classical
  let L : ℝ → C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ := fun x =>
    if h : 0 < x ∧ 0 < laplace M (1 / x) then
      tiltedFunctional M (hfinite _ (one_div_pos.2 h.1)) h.2 else 0
  have hbound : ∀ x : ℝ, ‖L x‖ ≤ 1 := by
    intro x
    dsimp only [L]
    split_ifs with hx
    · exact tiltedFunctional_norm_le _ _ _
    · rw [ContinuousLinearMap.opNorm_zero]
      exact zero_le_one
  have hmom : ∀ n : ℕ, Tendsto
      (fun x => L x ((ContinuousMap.restrict (Icc (0 : ℝ) 1) (.id ℝ)) ^ n))
      atTop (𝓝 (L₀ ((ContinuousMap.restrict (Icc (0 : ℝ) 1) (.id ℝ)) ^ n))) := by
    intro n
    rw [hmodel]
    apply (tilted_monomial_limit M hF n).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hF.1] with x hx hp
    rw [show L x = tiltedFunctional M (hfinite _ (one_div_pos.2 hx)) hp by
      dsimp only [L]
      rw [dite_eq_left (show 0 < x ∧ 0 < laplace M (1 / x) from ⟨hx, hp⟩)]]
    rw [tiltedFunctional_monomial M (one_div_pos.2 hx).le, tilted_monomial_integral]
  apply (tendsto_functional_of_monomials L L₀ hbound hmom f).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hF.1] with x hx hp
  rw [show L x = tiltedFunctional M (hfinite _ (one_div_pos.2 hx)) hp by
    dsimp only [L]
    rw [dite_eq_left (show 0 < x ∧ 0 < laplace M (1 / x) from ⟨hx, hp⟩)]]
  rfl

/-- The power-law model measure, whose Laplace transform is `s^(-ρ)`.
Only its nonnegative restriction is used. -/
noncomputable def powerMeasure (ρ : ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (y ^ (ρ - 1) / Real.Gamma ρ))

private theorem measurable_powerWeight (ρ : ℝ) :
    Measurable (fun y : ℝ => ENNReal.ofReal (y ^ (ρ - 1) / Real.Gamma ρ)) :=
  (measurable_id.pow_const _ |>.div_const _).ennreal_ofReal

theorem powerMeasure_integrable {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) :
    IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) (powerMeasure ρ) := by
  rw [IntegrableOn, powerMeasure, restrict_withDensity measurableSet_Ici,
    integrable_withDensity_iff (measurable_powerWeight ρ)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hi : IntegrableOn (fun y : ℝ => y ^ (ρ - 1) * Real.exp (-s * y)) (Ici 0) := by
    apply Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (by linarith : -1 < ρ - 1) zero_lt_one hs
  apply (hi.div_const (Real.Gamma ρ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hy _) (Real.Gamma_pos_of_pos hρ).le)]
  ring

theorem laplace_powerMeasure {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) :
    laplace (powerMeasure ρ) s = (1 / s) ^ ρ := by
  rw [laplace, powerMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (measurable_powerWeight ρ).aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Ici]
  have heq : (∫ y in Ici (0 : ℝ),
      (ENNReal.ofReal (y ^ (ρ - 1) / Real.Gamma ρ)).toReal • Real.exp (-s * y)) =
      (∫ y in Ici (0 : ℝ), y ^ (ρ - 1) * Real.exp (-(s * y))) / Real.Gamma ρ := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    rw [ENNReal.toReal_ofReal
      (div_nonneg (Real.rpow_nonneg hy _) (Real.Gamma_pos_of_pos hρ).le), smul_eq_mul]
    simp only [neg_mul]
    ring
  rw [heq, integral_Ici_eq_integral_Ioi, Real.integral_rpow_mul_exp_neg_mul_Ioi hρ hs]
  exact mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hρ).ne'

/-- The Gamma model functional for a strictly positive index. -/
noncomputable def gammaFunctional {ρ : ℝ} (hρ : 0 < ρ) : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ :=
  tiltedFunctional (powerMeasure ρ) (powerMeasure_integrable hρ zero_lt_one)
    (by rw [laplace_powerMeasure hρ zero_lt_one]; norm_num)

theorem gammaFunctional_monomial {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    gammaFunctional hρ ((ContinuousMap.restrict (Icc (0 : ℝ) 1) (.id ℝ)) ^ n) =
      (1 / ((n : ℝ) + 1)) ^ ρ := by
  rw [gammaFunctional, tiltedFunctional_monomial _ zero_le_one,
    laplace_powerMeasure hρ (by positivity), laplace_powerMeasure hρ zero_lt_one]
  simp

/-- The positive-index Tauberian argument up to continuous test functions:
the tilted laws converge to the explicit Gamma model. -/
theorem tilted_gamma_limit (M : Measure ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) (-ρ))
    (f : C(Icc (0 : ℝ) 1, ℝ)) :
    Tendsto (fun x : ℝ => (∫ y in Ici (0 : ℝ),
      Real.exp (-(1 / x) * y) * f (expUnit ((1 / x) * y)) ∂M) / laplace M (1 / x))
      atTop (𝓝 (gammaFunctional hρ f)) :=
  tilted_continuous_test_limit M hfinite hF (gammaFunctional hρ)
    (gammaFunctional_monomial hρ) f

private noncomputable def cutoffApprox (n : ℕ) (b : ℝ) : C(Icc (0 : ℝ) 1, ℝ) where
  toFun t := min 1 (max 0 ((n : ℝ) * ((t : ℝ) - Real.exp (-1)) + b)) /
    max (Real.exp (-1)) (t : ℝ)
  continuous_toFun := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _))

private noncomputable def cutoffTest (t : ℝ) : ℝ :=
  if Real.exp (-1) ≤ t then 1 / t else 0

private theorem cutoffApprox_nonneg (n : ℕ) (b : ℝ) (t : Icc (0 : ℝ) 1) :
    0 ≤ cutoffApprox n b t :=
  div_nonneg (le_min zero_le_one (le_max_left _ _))
    ((Real.exp_pos _).le.trans (le_max_left _ _))

private theorem cutoffApprox_le (n : ℕ) (b : ℝ) (t : Icc (0 : ℝ) 1) :
    cutoffApprox n b t ≤ 1 / Real.exp (-1) := by
  calc
    _ ≤ 1 / max (Real.exp (-1)) (t : ℝ) :=
      div_le_div_of_nonneg_right (min_le_left _ _)
        ((Real.exp_pos _).le.trans (le_max_left _ _))
    _ ≤ _ := one_div_le_one_div_of_le (Real.exp_pos _) (le_max_left _ _)

private theorem cutoffApprox_sandwich (n : ℕ) (t : Icc (0 : ℝ) 1) :
    cutoffApprox n 0 t ≤ cutoffTest t ∧ cutoffTest t ≤ cutoffApprox n 1 t := by
  by_cases ht : Real.exp (-1) ≤ (t : ℝ)
  · have hn : 0 ≤ (n : ℝ) * ((t : ℝ) - Real.exp (-1)) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 ht)
    simp only [cutoffTest, ite_eq_left ht, cutoffApprox, ContinuousMap.coe_mk,
      max_eq_right ht]
    constructor
    · exact div_le_div_of_nonneg_right (min_le_left _ _) ((Real.exp_pos _).le.trans ht)
    · rw [max_eq_right (by linarith : 0 ≤ (n : ℝ) * ((t : ℝ) - Real.exp (-1)) + 1),
        min_eq_left (by linarith)]
  · have hn : (n : ℝ) * ((t : ℝ) - Real.exp (-1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.2 (not_le.1 ht).le)
    constructor
    · simp only [cutoffTest, ite_eq_right ht, cutoffApprox, ContinuousMap.coe_mk,
        add_zero, max_eq_left hn, min_eq_right zero_le_one, zero_div, le_refl]
    · simpa only [cutoffTest, ite_eq_right ht] using cutoffApprox_nonneg n 1 t

private theorem cutoffApprox_tendsto (b : ℝ) (t : Icc (0 : ℝ) 1)
    (ht : (t : ℝ) ≠ Real.exp (-1)) :
    Tendsto (fun n => cutoffApprox n b t) atTop (𝓝 (cutoffTest t)) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  by_cases hgt : Real.exp (-1) < (t : ℝ)
  · have hh := tendsto_atTop_add_const_right atTop b
      (hnat.atTop_mul_const (sub_pos.2 hgt))
    apply tendsto_const_nhds.congr'
    filter_upwards [hh.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    simp only [cutoffApprox, ContinuousMap.coe_mk, cutoffTest, ite_eq_left hgt.le,
      max_eq_right hgt.le]
    rw [max_eq_right (by linarith : 0 ≤ (n : ℝ) * ((t : ℝ) - Real.exp (-1)) + b),
      min_eq_left hn]
  · have hlt : (t : ℝ) < Real.exp (-1) := lt_of_le_of_ne (not_lt.1 hgt) ht
    have hh := tendsto_atBot_add_const_right atTop b
      (hnat.atTop_mul_const_of_neg (sub_neg.2 hlt))
    apply tendsto_const_nhds.congr'
    filter_upwards [hh.eventually (eventually_le_atBot (0 : ℝ))] with n hn
    simp only [cutoffApprox, ContinuousMap.coe_mk, cutoffTest, ite_eq_right (not_le.2 hlt),
      max_eq_left hn, min_eq_right zero_le_one, zero_div]

private theorem weighted_cutoff_eq {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    Real.exp (-(1 / x) * y) * cutoffTest (expUnit ((1 / x) * y)) =
      (Iic x).indicator (fun _ : ℝ => 1) y := by
  have ht : Real.exp (-1) ≤ Real.exp (-(1 / x) * y) ↔ y ≤ x := by
    rw [Real.exp_le_exp, show -(1 / x) * y = -(y / x) by ring,
      neg_le_neg_iff, div_le_one hx]
  simp only [neg_mul] at ht
  rw [cutoffTest, expUnit_coe (mul_nonneg (one_div_pos.2 hx).le hy)]
  simp only [neg_mul, ht, indicator_apply, mem_Iic]
  split_ifs <;> simp [Real.exp_ne_zero]

private theorem gammaFunctional_apply {ρ : ℝ} (hρ : 0 < ρ)
    (f : C(Icc (0 : ℝ) 1, ℝ)) :
    gammaFunctional hρ f = ∫ y in Ici (0 : ℝ),
      Real.exp (-y) * f (expUnit y) ∂powerMeasure ρ := by
  rw [gammaFunctional, tiltedFunctional_apply, laplace_powerMeasure hρ zero_lt_one]
  simp

private theorem model_cutoff_integral {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ y in Ici (0 : ℝ), Real.exp (-y) * cutoffTest (expUnit y) ∂powerMeasure ρ) =
      1 / Real.Gamma (1 + ρ) := by
  have heq : (∫ y in Ici (0 : ℝ), Real.exp (-y) * cutoffTest (expUnit y) ∂powerMeasure ρ) =
      ∫ y in Icc (0 : ℝ) 1, (1 : ℝ) ∂powerMeasure ρ := by
    calc
      _ = ∫ y in Ici (0 : ℝ), (Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) y ∂powerMeasure ρ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
        simpa only [one_div_one, neg_one_mul, one_mul] using weighted_cutoff_eq zero_lt_one hy
      _ = _ := by rw [integral_indicator measurableSet_Iic,
        Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ici]
  rw [heq, powerMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (measurable_powerWeight ρ).aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Icc]
  rw [← gamma_cutoff_integral hρ]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hy.1 _) (Real.Gamma_pos_of_pos hρ).le)]
  simp

private theorem cutoffApprox_model_limit {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    Tendsto (fun n => gammaFunctional hρ (cutoffApprox n b)) atTop
      (𝓝 (1 / Real.Gamma (1 + ρ))) := by
  have hne : ∀ᵐ y ∂powerMeasure ρ, y ≠ (1 : ℝ) := by
    apply ae_iff.2
    have hz : powerMeasure ρ {1} = 0 :=
      withDensity_absolutelyContinuous volume _ (measure_singleton (1 : ℝ))
    simpa only [not_not, ofPred_eq_eq_singleton] using hz
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := (powerMeasure ρ).restrict (Ici 0))
    (fun y : ℝ => (1 / Real.exp (-1)) * Real.exp (-y))
    (fun n => by
      have hc : Continuous (fun y : ℝ =>
          Real.exp (-y) * cutoffApprox n b (expUnit y)) := by fun_prop
      exact hc.aestronglyMeasurable)
    (by
      simpa only [neg_one_mul] using
        (powerMeasure_integrable hρ zero_lt_one).const_mul (1 / Real.exp (-1)))
    (fun n => Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
        abs_of_nonneg (cutoffApprox_nonneg n b _)]
      exact
        (mul_le_mul_of_nonneg_left (cutoffApprox_le n b _) (Real.exp_pos _).le).trans_eq
          (mul_comm _ _))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ici, ae_restrict_of_ae hne] with y hy hne
      have ht : (expUnit y : ℝ) ≠ Real.exp (-1) := by
        rw [expUnit_coe hy, ne_eq, Real.exp_eq_exp, neg_inj]
        exact hne
      exact (cutoffApprox_tendsto b (expUnit y) ht).const_mul (Real.exp (-y)))
  simpa only [← gammaFunctional_apply hρ, model_cutoff_integral hρ] using hlim

private theorem tendsto_of_sandwich_limits {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {v w : ℕ → ι → ℝ} {a b : ℕ → ℝ} {c : ℝ}
    (hv : ∀ n, Tendsto (v n) l (𝓝 (a n))) (hw : ∀ n, Tendsto (w n) l (𝓝 (b n)))
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 c))
    (hbound : ∀ n, ∀ᶠ x in l, v n x ≤ u x ∧ u x ≤ w n x) :
    Tendsto u l (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro r hr
    obtain ⟨n, hn⟩ := (ha.eventually (lt_mem_nhds hr)).exists
    filter_upwards [(hv n).eventually (lt_mem_nhds hn), hbound n] with x hx hb
    exact hx.trans_le hb.1
  · intro r hr
    obtain ⟨n, hn⟩ := (hb.eventually (gt_mem_nhds hr)).exists
    filter_upwards [(hw n).eventually (gt_mem_nhds hn), hbound n] with x hx hb
    exact hb.2.trans_lt hx

/-- The positive-index Tauberian ratio theorem. The continuous approximations
to the exponentially compactified cutoff are squeezed against the Gamma law. -/
theorem laplace_tauberian_pos_ratio (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ : 0 < ρ)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) (-ρ)) :
    Tendsto (fun x => cumulative M x / laplace M (1 / x)) atTop
      (𝓝 (1 / Real.Gamma (1 + ρ))) := by
  let v : ℕ → ℝ → ℝ := fun n x =>
    (∫ y in Ici (0 : ℝ), Real.exp (-(1 / x) * y) *
      cutoffApprox n 0 (expUnit ((1 / x) * y)) ∂M) / laplace M (1 / x)
  let w : ℕ → ℝ → ℝ := fun n x =>
    (∫ y in Ici (0 : ℝ), Real.exp (-(1 / x) * y) *
      cutoffApprox n 1 (expUnit ((1 / x) * y)) ∂M) / laplace M (1 / x)
  apply tendsto_of_sandwich_limits
    (v := v) (w := w)
    (fun n => tilted_gamma_limit M hρ hfinite hF (cutoffApprox n 0))
    (fun n => tilted_gamma_limit M hρ hfinite hF (cutoffApprox n 1))
    (cutoffApprox_model_limit hρ 0) (cutoffApprox_model_limit hρ 1)
  intro n
  filter_upwards [eventually_gt_atTop (0 : ℝ), hF.1] with x hx hFx
  let μ := M.restrict (Ici 0)
  let a : ℝ → ℝ := (Iic x).indicator (fun _ => 1)
  have hi : Integrable a μ := by
    apply (integrable_indicator_iff measurableSet_Iic).2
    exact integrableOn_const (C := (1 : ℝ)) (by
      rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ici]
      exact isCompact_Icc.measure_lt_top.ne)
  have ha : (∫ y, a y ∂μ) = cumulative M x := by
    rw [integral_indicator_const _ measurableSet_Iic,
      measureReal_restrict_apply measurableSet_Iic, Iic_inter_Ici, smul_eq_mul, mul_one]
    rfl
  have hb : ∀ᵐ y ∂μ,
      Real.exp (-(1 / x) * y) * cutoffApprox n 0 (expUnit ((1 / x) * y)) ≤ a y ∧
      a y ≤ Real.exp (-(1 / x) * y) * cutoffApprox n 1 (expUnit ((1 / x) * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    have hh := cutoffApprox_sandwich n (expUnit ((1 / x) * y))
    dsimp only [a]
    rw [← weighted_cutoff_eq hx hy]
    exact ⟨mul_le_mul_of_nonneg_left hh.1 (Real.exp_pos _).le,
      mul_le_mul_of_nonneg_left hh.2 (Real.exp_pos _).le⟩
  have hl := integral_mono_ae (tilted_test_integrable M (hfinite _ (one_div_pos.2 hx))
    (cutoffApprox n 0)) hi (hb.mono fun _ h => h.1)
  have hu := integral_mono_ae hi (tilted_test_integrable M (hfinite _ (one_div_pos.2 hx))
    (cutoffApprox n 1)) (hb.mono fun _ h => h.2)
  rw [ha] at hl hu
  exact ⟨div_le_div_of_nonneg_right hl hFx.le, div_le_div_of_nonneg_right hu hFx.le⟩

/-- Tauberian ratio theorem for every nonnegative index, including the atom
which arises in the Gamma-model limit at index zero. -/
theorem laplace_tauberian_ratio (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) (-ρ)) :
    Tendsto (fun x => cumulative M x / laplace M (1 / x)) atTop
      (𝓝 (1 / Real.Gamma (1 + ρ))) := by
  rcases eq_or_lt_of_le hρ with heq | hpos
  · subst ρ
    simp only [neg_zero] at hF
    simpa only [neg_zero, add_zero, Real.Gamma_one, div_one] using
      laplace_tauberian_zero_ratio M hfinite hF
  · exact laplace_tauberian_pos_ratio M hpos hfinite hF

/-- Tauberian regular variation of the cumulative mass. -/
theorem laplace_tauberian (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) (-ρ)) :
    RegularlyVarying (cumulative M) ρ := by
  have hF' : RegularlyVarying (fun x => laplace M (1 / x)) ρ := by
    simpa only [RegularlyVaryingAtZero, neg_neg] using hF
  exact hF'.of_ratio (one_div_pos.2 (Real.Gamma_pos_of_pos (by linarith)))
    (laplace_tauberian_ratio M hρ hfinite hF)

/-- Restricted Laplace–Stieltjes Karamata theorem. In reciprocal coordinates
both functions have index `ρ` at infinity; the transform itself has index `-ρ`
at zero. Eventual positivity in the regular-variation predicates excludes the
zero measure on the nonnegative half line. -/
theorem laplace_karamata (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M) :
    RegularlyVaryingAtZero (laplace M) (-ρ) ↔ RegularlyVarying (cumulative M) ρ :=
  ⟨laplace_tauberian M hρ0 hfinite, laplace_abelian M hρ0 hρ1 hfinite⟩

/-- The asymptotic normalization under the transform-side hypothesis. -/
theorem laplace_karamata_normalization (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hF : RegularlyVaryingAtZero (laplace M) (-ρ)) :
    Tendsto (fun x => cumulative M x / (laplace M (1 / x) / Real.Gamma (1 + ρ)))
      atTop (𝓝 1) :=
  laplace_abelian_normalization M hρ0 hρ1 hfinite (laplace_tauberian M hρ0 hfinite hF)

end BGW.StableTrees.Attraction.KaramataTransforms
