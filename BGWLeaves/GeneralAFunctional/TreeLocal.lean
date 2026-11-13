module

public import BGWLeaves.GeneralAFunctional.TreeEvents
public import BGWLeaves.LocalEstimates.NormRatios

/-! Marked-forest local estimates and admissible denominator asymptotics. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeLocal

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.GeneralA
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents
open scoped ENNReal Topology

/-- Canonical exploration scale at marked count `n`. -/
noncomputable def markScale (μ : PMF ℕ) (A : Set ℕ) (θ : ℝ) (n : ℕ) : ℝ :=
  norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊

theorem markScale_atTop {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Tendsto (markScale μ A θ) atTop atTop := by
  obtain ⟨hp, _, _⟩ := GeneralAInf.BlockStable.blockStep_firstMoment hc hA
  let := hp
  exact TransformConvergence.tendsto_atTop (blockStep μ A)
    (GeneralAInf.BlockStable.blockStep_isStableAttracted hc hne hDA hA)

theorem admissible_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} {n : ℕ} (hn : ZetaAAdmissible μ A n) :
    (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1 := by
  by_contra hd
  exact (admissible_iff μ hc hne A n).mp hn
    (MarkedLaw.zetaA_eq_zero_of_not_dvd A hc hne n hd)

/-- The corrected uniform LLT on the finite-forest event used by prefix completion. -/
theorem forest_local {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j →
      (j : ℝ) ≤ α * norming (stepLaw μ) θ n →
      |(n : ℝ) * ((Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          (markedForestEvent A j n)).toReal -
        (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - j then
          (arithFactor μ A : ℝ) * q₁ θ (j / markScale μ A θ n) else 0)| ≤ ε := by
  obtain ⟨N, hN⟩ := GeneralAInf.BlockLocal.eq_gen_corrected hc hne hDA hA hα hε
  refine ⟨N, fun n hn j hj hjb => ?_⟩
  rw [measure_congr (markedForestEvent_ae μ hc hne A j n)]
  exact hN n hn j hj hjb

/-- Moving-parameter form of the forest LLT, with normalized endpoint convergence.
The range condition can be obtained from regular variation when the endpoint
and remaining marked count range over compact subsets of the positive quadrant. -/
theorem moving_forest_local {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {u j : ℕ → ℕ} (hu : Tendsto u atTop atTop) {α y : ℝ} (hα : 0 < α)
    (hj : ∀ᶠ k in atTop, 1 ≤ j k ∧ (j k : ℝ) ≤ α * norming (stepLaw μ) θ (u k))
    (hres : ∀ᶠ k in atTop, (arithFactor μ A : ℤ) ∣ (u k : ℤ) - j k)
    (hy : Tendsto (fun k => (j k : ℝ) / markScale μ A θ (u k)) atTop (𝓝 y)) :
    Tendsto (fun k => (u k : ℝ) *
      ((Measure.pi fun _ : Fin (j k) => bienaymeLaw μ.toMeasure)
        (markedForestEvent A (j k) (u k))).toReal) atTop
      (𝓝 ((arithFactor μ A : ℝ) * q₁ θ y)) := by
  obtain ⟨a, ha⟩ := hDA
  have herr : Tendsto (fun k => (u k : ℝ) *
      ((Measure.pi fun _ : Fin (j k) => bienaymeLaw μ.toMeasure)
        (markedForestEvent A (j k) (u k))).toReal -
        (arithFactor μ A : ℝ) * q₁ θ ((j k : ℝ) / markScale μ A θ (u k)))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := forest_local hc hne ⟨a, ha⟩ hA hα (half_pos hε)
    filter_upwards [hu.eventually_ge_atTop N, hj, hres] with k hk hjk hrk
    rw [Real.dist_eq, sub_zero]
    have hh := hN (u k) hk (j k) hjk.1 hjk.2
    rw [ite_eq_left hrk] at hh
    exact hh.trans_lt (half_lt_self hε)
  have hcont : Continuous (q₁ θ) := by
    unfold q₁
    exact continuous_id.mul ((Scalar.continuous_stableDensity ha.alpha_mem).comp continuous_neg)
  have ht := herr.add ((hcont.tendsto y).comp hy |>.const_mul (arithFactor μ A : ℝ))
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using ht

/-- Re-expressing a moving LLT with a different reference count. -/
theorem moving_forest_reference {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {u j v : ℕ → ℕ} (hu : Tendsto u atTop atTop) {α y s : ℝ} (hα : 0 < α) (hs : 0 < s)
    (hj : ∀ᶠ k in atTop, 1 ≤ j k ∧ (j k : ℝ) ≤ α * norming (stepLaw μ) θ (u k))
    (hres : ∀ᶠ k in atTop, (arithFactor μ A : ℤ) ∣ (u k : ℤ) - j k)
    (hy : Tendsto (fun k => (j k : ℝ) / markScale μ A θ (u k)) atTop (𝓝 y))
    (hsu : Tendsto (fun k => (u k : ℝ) / v k) atTop (𝓝 s)) :
    Tendsto (fun k => (v k : ℝ) *
      ((Measure.pi fun _ : Fin (j k) => bienaymeLaw μ.toMeasure)
        (markedForestEvent A (j k) (u k))).toReal) atTop
      (𝓝 ((arithFactor μ A : ℝ) * q₁ θ y / s)) := by
  have ht := (moving_forest_local hc hne hDA hA hu hα hj hres hy).div hsu hs.ne'
  apply ht.congr'
  filter_upwards [hu.eventually_ne_atTop 0, hsu.eventually (eventually_gt_nhds hs)] with k huk hvk
  have hu0 : (u k : ℝ) ≠ 0 := by exact_mod_cast huk
  have hv0 : (v k : ℝ) ≠ 0 := by
    intro hv
    rw [hv, div_zero] at hvk
    exact (lt_irrefl _ hvk)
  dsimp only [Pi.div_apply]
  field_simp

/-- Exact one-tree block identity, normalized in real mass. -/
theorem n_mul_markedMass {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * markedMass μ A n = intWalkProb (blockStep μ A) n (-1) := by
  rw [markedMass_eq_zetaAProb μ hc hne]
  change (n : ℝ) * (bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)}).toReal = _
  have he : n = (n - 1) + 1 := by omega
  rw [he, MarkedSeries.zetaA_blockLaw hc hne A (n - 1),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  change ((n - 1 + 1 : ℕ) : ℝ) * (((n - 1 + 1 : ℕ) : ℝ)⁻¹ *
    intWalkProb (blockStep μ A) (n - 1 + 1) (-1)) = _
  have hn0 : ((n - 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- The marked denominator on every admissible sequence, at the exploration scale. -/
theorem normalized_markedMass_tendsto {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (q k : ℝ) * markScale μ A θ (q k) * markedMass μ A (q k)) atTop
      (𝓝 ((arithFactor μ A : ℝ) * Scalar.stableDensity θ 0)) := by
  let ν := blockStep μ A
  obtain ⟨hp, hi, hm⟩ := GeneralAInf.BlockStable.blockStep_firstMoment hc hA
  let := hp
  change mean ν = 0 at hm
  have hattr : IsStableAttracted ν θ (mean ν) (markScale μ A θ) := by
    rw [hm]
    exact GeneralAInf.BlockStable.blockStep_isStableAttracted hc hne hDA hA
  have hmono := GeneralAInf.BlockStable.monotone_norming_floor hc hne hDA hA
  obtain ⟨hspan, hsupp⟩ := MarkedSpan.blockLaw_span hc hne hA
  have herr : Tendsto (fun k => markScale μ A θ (q k) * intWalkProb ν (q k) (-1) -
      (arithFactor μ A : ℝ) * Scalar.stableDensity θ (-1 / markScale μ A θ (q k)))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := LeafMass.YLaw.llt_lattice_abstract ν hi hspan (-1) hsupp hmono hattr (half_pos hε)
    filter_upwards [hqtop.eventually_ge_atTop N] with k hk
    have hd : (arithFactor μ A : ℤ) ∣ (-1 : ℤ) - (q k : ℤ) * (-1) := by
      convert admissible_dvd hc hne (hq k) using 1
      ring
    have hh := hN (q k) hk (-1)
    simp only [hm, mul_zero, sub_zero, ite_eq_left hd, Int.cast_neg, Int.cast_one] at hh
    rw [Real.dist_eq, sub_zero]
    exact hh.trans_lt (half_lt_self hε)
  have harg : Tendsto (fun k => (-1 : ℝ) / markScale μ A θ (q k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((markScale_atTop hc hne hDA hA).comp hqtop)
  have ht := herr.add (((Scalar.continuous_stableDensity hattr.alpha_mem).tendsto 0).comp harg
    |>.const_mul (arithFactor μ A : ℝ))
  simp only [Function.comp_def, sub_add_cancel, zero_add] at ht
  apply ht.congr'
  filter_upwards [hqtop.eventually_ge_atTop 1] with k hk
  rw [← n_mul_markedMass hc hne A hk]
  ring

end BGWLeaves.GeneralAFunctional.TreeLocal
