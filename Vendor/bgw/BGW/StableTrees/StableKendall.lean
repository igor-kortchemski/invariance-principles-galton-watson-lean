/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.WalkPassage
public import BGW.StableTrees.StablePassageSubordinator
public import BGW.StableTrees.StableDensityAPI
public import BGW.StableTrees.Scalar.LocalLimit
public import BGW.StableTrees.Scalar.Lattice
public import BGW.StableTrees.Scalar.Normalization
public import BGW.StableTrees.StableKendallLocal
public import BGW.StableTrees.StableKendallRiemann
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Kendall's identity for stable passage times

This module deduces the density of the stable first-passage time from the discrete
Kemperman identity, the lattice local limit theorem, and convergence of the rescaled
walk passage laws. The lattice factor in the local limit cancels against the mesh of
the arithmetic-progression Riemann sums.

References: (D. G. Kendall, Some problems in the theory of dams, J. Roy. Statist. Soc. Ser. B 19
(1957), 207–212; A. A. Borovkov, *Stochastic Processes in Queueing Theory*, Springer, 1976; J.
Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII, Corollary 3; local limit
theorem: B. V. Gnedenko and A. N. Kolmogorov, *Limit Distributions for Sums of Independent Random
Variables*, Addison-Wesley, 1954, §50).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- Off the residue class `k ≡ ℓ (mod d)` the first-hit mass vanishes (Kemperman + LLT support). -/
theorem walkHitTime_mass_eq_zero_of_not_dvd {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {k : ℕ}
    (hk : ¬ (Scalar.latticeSpan μ : ℤ) ∣ (k : ℤ) - ℓ) :
    (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
      {w | walkHitTime ℓ w = (k : ℕ∞)} = 0 := by
  by_cases hk0 : k = 0
  · subst k
    rw [measureReal_def, walkHitTime_mass_eq_forestWeight μ hℓ]
    have hzero : BGW.forestWeight μ ℓ 0 = 0 :=
      BGW.forestWeight_eq_zero_of_lt μ (by omega)
    rw [hzero]
    rfl
  · rw [walkHitTime_mass_toReal hℓ (Nat.one_le_iff_ne_zero.mpr hk0),
      Scalar.walkProb_eq_zero_of_not_dvd h (by simpa [sub_eq_add_neg, add_comm] using hk), mul_zero]

/-- The mass of the walk passage law as a series over the hitting time (`ℓ ≥ 1`):
`∫ g d(walkPassageLaw) = Σ_k g(k/n) P(hit = k)` for bounded `g` vanishing on `(-∞, 0]`. -/
theorem integral_walkPassageLaw_eq_tsum {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {n : ℕ} (hn : 1 ≤ n) (g : BoundedContinuousFunction ℝ ℝ)
    (hg : ∀ t ≤ 0, g t = 0) :
    ∫ t, g t ∂(walkPassageLaw μ ℓ n) =
      ∑' k : ℕ, g ((k : ℝ) / n) *
        (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
          {w | walkHitTime ℓ w = (k : ℕ∞)} := by
  have _hℓ := hℓ  -- keeps the hypothesis used (unused-variable linter)
  have _hn := hn  -- keeps the hypothesis used (unused-variable linter)
  have _hg := hg  -- keeps the hypothesis used (unused-variable linter)
  let P : Measure (ℕ → ℝ) := iidLaw (realOffspringStepLaw μ)
  let E : ℕ → Set (ℕ → ℝ) := fun k => {w | walkHitTime ℓ w = (k : ℕ∞)}
  have hP : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hmeas : Measurable (fun w : ℕ → ℝ => (((walkHitTime ℓ w).toNat : ℝ) / n)) := by
    have htoNat : Measurable (fun w : ℕ → ℝ => (walkHitTime ℓ w).toNat) :=
      (measurable_of_countable ENat.toNat).comp (measurable_walkHitTime ℓ)
    exact (((by fun_prop : Measurable (fun k : ℕ => (k : ℝ))).comp htoNat).div_const n)
  rw [walkPassageLaw, integral_map hmeas.aemeasurable g.continuous.aestronglyMeasurable]
  have htop : ∀ᵐ w ∂P, walkHitTime ℓ w ≠ ⊤ := ae_walkHitTime_ne_top h ℓ
  have hunion : ∀ᵐ w ∂P, w ∈ ⋃ k, E k := by
    filter_upwards [htop] with w hw
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hw
    exact Set.mem_iUnion.mpr ⟨k, hk.symm⟩
  have hwhole : ∫ w, g (((walkHitTime ℓ w).toNat : ℝ) / n) ∂P =
      ∫ w in ⋃ k, E k, g (((walkHitTime ℓ w).toNat : ℝ) / n) ∂P := by
    rw [← integral_indicator (MeasurableSet.iUnion fun k =>
      measurableSet_eq_fun (measurable_walkHitTime ℓ) measurable_const)]
    apply integral_congr_ae
    filter_upwards [hunion] with w hw
    exact (Set.indicator_of_mem hw
      (fun w : ℕ → ℝ => g (((walkHitTime ℓ w).toNat : ℝ) / n))).symm
  rw [hwhole]
  have hm : ∀ k, MeasurableSet (E k) := fun k =>
    measurableSet_eq_fun (measurable_walkHitTime ℓ) measurable_const
  have hd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left, E]
    rintro w hi hj
    change walkHitTime ℓ w = (i : ℕ∞) at hi
    change walkHitTime ℓ w = (j : ℕ∞) at hj
    rw [hi] at hj
    exact hij (by exact_mod_cast hj)
  rw [integral_iUnion hm hd]
  · congr 1
    funext k
    have heq : ∀ w ∈ E k, ((walkHitTime ℓ w).toNat : ℝ) / n = (k : ℝ) / n := by
      intro w hw
      change walkHitTime ℓ w = (k : ℕ∞) at hw
      simp [hw]
    have heq' : (fun w => g (((walkHitTime ℓ w).toNat : ℝ) / n)) =ᵐ[P.restrict (E k)]
        fun _ => g ((k : ℝ) / n) :=
      ae_restrict_iff' (hm k) |>.mpr (.of_forall fun w hw => congrArg g (heq w hw))
    rw [integral_congr_ae heq', setIntegral_const, smul_eq_mul, mul_comm]
  · exact (Integrable.of_bound (g.continuous.measurable.comp hmeas).aestronglyMeasurable
      ‖g‖ (.of_forall fun w => g.norm_coe_le_norm _)).integrableOn

/-- **Uniform integrability / tightness near `0`** needed to pass from local densities on compacts
to the full law: no mass of `walkPassageLaw` escapes to `0` or `∞` (follows from the weak
convergence of walk passage laws (`tendsto_walkPassageLaw`) and `passageLaw_Iic_zero`; no
`walkHitTime` tail bound is assumed). -/
theorem walkPassageLaw_tight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {x : ℝ≥0} (hx : 0 < x) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 (x : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ R : ℝ, δ < R ∧ ∀ᶠ n in atTop,
      walkPassageLaw μ (ℓ n) n (Iio δ) + walkPassageLaw μ (ℓ n) n (Ioi R) ≤ ENNReal.ofReal ε := by
  let P : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨walkPassageLaw μ (ℓ n) n, walkPassageLaw_isProbabilityMeasure h (ℓ n) n⟩
  let Q : ProbabilityMeasure ℝ := ⟨passageLaw θ x, passageLaw_isProbabilityMeasure h.alpha_mem x⟩
  have hlim : Tendsto P atTop (𝓝 Q) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
    (tendsto_walkPassageLaw h hx hℓ hscale)
  let _ : IsProbabilityMeasure (passageLaw θ x) := passageLaw_isProbabilityMeasure h.alpha_mem x
  let η : ℝ≥0∞ := ENNReal.ofReal (ε / 4)
  have hη : 0 < η := ENNReal.ofReal_pos.2 (by positivity)
  have hleft_limit : Tendsto (fun j : ℕ => passageLaw θ x (Iic (1 / (j + 1 : ℝ)))) atTop
      (𝓝 (passageLaw θ x (Iic 0))) := by
    have hinter : (⋂ j : ℕ, Iic (1 / (j + 1 : ℝ))) = Iic (0 : ℝ) := by
      ext t
      simp only [Set.mem_iInter, Set.mem_Iic]
      constructor
      · intro ht
        by_contra hpos
        have htpos : 0 < t := lt_of_not_ge hpos
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt htpos
        exact (not_le_of_gt hj) (ht j)
      · intro ht j
        exact ht.trans (by positivity)
    rw [← hinter]
    apply tendsto_measure_iInter_atTop (fun j => measurableSet_Iic.nullMeasurableSet) _
      ⟨0, measure_ne_top _ _⟩
    intro i j hij
    exact Iic_subset_Iic.2 (by
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      apply one_div_le_one_div_of_le (by positivity)
      linarith)
  rw [passageLaw_Iic_zero h.alpha_mem hx] at hleft_limit
  obtain ⟨j, hj⟩ := (hleft_limit.eventually (gt_mem_nhds hη)).exists
  let δ : ℝ := 1 / (j + 1 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hleft_limsup :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim (F := Iic δ) isClosed_Iic
  have hleft_event : ∀ᶠ n in atTop, walkPassageLaw μ (ℓ n) n (Iic δ) < η := by
    have hsmall : passageLaw θ x (Iic δ) < η := by simpa [δ] using hj
    exact ((Filter.limsup_le_iff).mp hleft_limsup η hsmall).mono (fun n hn => hn)
  obtain ⟨K, hK, hQK⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := (passageLaw θ x : Measure ℝ))) η hη
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.bddAbove
  let R := max R₀ (δ + 1) + 1
  have hKR : K ⊆ Iio R := by
    intro t ht
    have ht' : t ≤ max R₀ (δ + 1) := (hR₀ ht).trans (le_max_left _ _)
    exact lt_of_le_of_lt ht' (by dsimp [R]; linarith)
  have hQR : passageLaw θ x (Ici R) ≤ η := by
    have hle : passageLaw θ x (Ici R) ≤ passageLaw θ x Kᶜ := by
      apply measure_mono
      intro t ht hKt
      have htR : t < R := hKR hKt
      exact (not_le_of_gt htR) ht
    have hsmall := hQK (passageLaw θ x) (by rfl)
    exact hle.trans hsmall
  have hright_limsup :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim (F := Ici R) isClosed_Ici
  have hright_event : ∀ᶠ n in atTop, walkPassageLaw μ (ℓ n) n (Ici R) < 2 * η :=
    (Filter.limsup_le_iff).mp hright_limsup (2 * η) (hQR.trans_lt (by
      rw [two_mul]
      exact ENNReal.lt_add_right (by finiteness) hη.ne')) |>.mono (fun n hn => hn)
  have hsub : δ + 1 ≤ R := by
    apply (le_max_right R₀ (δ + 1)).trans
    dsimp [R]
    linarith
  refine ⟨δ, hδ, R, lt_of_lt_of_le (lt_add_one δ) hsub, ?_⟩
  filter_upwards [hleft_event, hright_event] with n hnleft hnright
  calc
    walkPassageLaw μ (ℓ n) n (Iio δ) + walkPassageLaw μ (ℓ n) n (Ioi R) ≤
        walkPassageLaw μ (ℓ n) n (Iic δ) + walkPassageLaw μ (ℓ n) n (Ici R) :=
      add_le_add (measure_mono Iio_subset_Iic_self) (measure_mono Ioi_subset_Ici_self)
    _ ≤ η + 2 * η := add_le_add hnleft.le hnright.le
    _ ≤ ENNReal.ofReal ε := by
      change ENNReal.ofReal (ε / 4) + 2 * ENNReal.ofReal (ε / 4) ≤ ENNReal.ofReal ε
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 4)
        (by positivity : 0 ≤ 2 * (ε / 4))]
      exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Weak limit against compactly supported tests.** The density limit is compared with the weak
convergence of walk passage laws (`tendsto_walkPassageLaw`):
`∫ g d(walkPassageLaw (ℓ n) n) → ∫ g(s) (x/s) p_s(-x) ds` for `g` continuous with compact support
in `(0,∞)`. -/
theorem tendsto_integral_walkPassageLaw_kendall {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x : ℝ} (hx : 0 < x) {ℓ : ℕ → ℕ}
    (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 x)) {g : ℝ → ℝ}
    (hg : Continuous g) (hsupp : HasCompactSupport g) (hpos : tsupport g ⊆ Ioi 0) :
    Tendsto (fun n : ℕ => ∫ t, g t ∂(walkPassageLaw μ (ℓ n) n)) atTop
      (𝓝 (∫ s in Ioi 0, g s * kendallKernel θ x s)) := by
  have _hx := hx  -- keeps the hypothesis used (unused-variable linter)
  have hzero : ∀ t ≤ 0, g t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (not_le_of_gt (hpos hmem)) ht
  have hopen : IsOpen (tsupport g)ᶜ := hsupp.isClosed.isOpen_compl
  have hnot : 0 ∉ tsupport g := by
    intro hmem
    exact lt_irrefl 0 (hpos hmem)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen 0 hnot
  let a := η / 2
  have ha : 0 < a := half_pos hη
  have hbelow : ∀ t ∈ tsupport g, a ≤ t := by
    intro t ht
    have hdist : η ≤ dist t 0 := by
      by_contra hlt
      exact hball (by simpa [Real.dist_eq, abs_of_pos (hpos ht)] using lt_of_not_ge hlt) ht
    have htpos := hpos ht
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos] at hdist
    dsimp [a]
    linarith
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuousOn continuousOn_id
  let b := max C a
  have hab : a ≤ b := le_max_right _ _
  have habove : ∀ t ∈ tsupport g, t ≤ b := by
    intro t ht
    have ht' : |t| ≤ C := by simpa using hC t ht
    rw [abs_of_pos (hpos ht)] at ht'
    exact ht'.trans (le_max_left _ _)
  have hHcont : Continuous (fun s => g s * kendallKernel θ x s) := by
    apply continuous_of_tsupport
    intro s hs
    exact hg.continuousAt.mul ((continuousOn_kendallKernel_time h.alpha_mem x).continuousAt
      (Ioi_mem_nhds (hpos (tsupport_mul_subset_left hs))))
  have hHsupp : HasCompactSupport (fun s => g s * kendallKernel θ x s) := by
    change HasCompactSupport (g * (fun s => kendallKernel θ x s))
    exact hsupp.mul_right
  have hHpos : tsupport (fun s => g s * kendallKernel θ x s) ⊆ Ioi 0 :=
    (tsupport_mul_subset_left).trans hpos
  have hInt : (∫ s, g s * kendallKernel θ x s) =
      ∫ s in Ioi 0, g s * kendallKernel θ x s := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with s
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hs]
    · have hz : g s = 0 := hzero s (by simpa using hs)
      rw [Set.indicator_of_notMem hs, hz, zero_mul]
  have hR := tendsto_progression_riemann_sum (Scalar.latticeSpan_pos h.critical h.nondegenerate)
    ℓ hHcont hHsupp hHpos
  rw [hInt] at hR
  let hgB : BoundedContinuousFunction ℝ ℝ := ofCompactSupport g hg hsupp
  have hnorm : 0 ≤ ‖hgB‖ := norm_nonneg _
  have hdiff : Tendsto (fun n : ℕ =>
      (∑' k : ℕ, g ((k : ℝ) / n) *
        (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
          {w | walkHitTime (ℓ n) w = (k : ℕ∞)}) -
      ∑' k : ℕ, if (Scalar.latticeSpan μ : ℤ) ∣ (k : ℤ) - ℓ n then
        (Scalar.latticeSpan μ : ℝ) / n * (g ((k : ℝ) / n) *
          kendallKernel θ x ((k : ℝ) / n)) else 0) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let C₀ := (b + 2) * (‖hgB‖ + 1)
    have hC₀ : 0 < C₀ := by positivity
    let δ := ε / C₀
    have hδ : 0 < δ := div_pos hε hC₀
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (tendsto_local_walkHitTime_mass h hx hℓ hscale ha hab hδ)
    have htop : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (eventually_ge_atTop 2)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hℓ
    refine ⟨max N₀ (max N₁ N₂), fun n hn => ?_⟩
    have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn12 : max N₁ N₂ ≤ n := (le_max_right N₀ (max N₁ N₂)).trans hn
    have hn1 : N₁ ≤ n := (le_max_left N₁ N₂).trans hn12
    have hn2 : N₂ ≤ n := (le_max_right N₁ N₂).trans hn12
    have hnp : 0 < n := by have := hN₁ n hn1; omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnp
    let N := ⌈b * n⌉₊
    let F : ℕ → ℝ := fun k => g ((k : ℝ) / n) *
      (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
        {w | walkHitTime (ℓ n) w = (k : ℕ∞)}
    let Rf : ℕ → ℝ := fun k => if (Scalar.latticeSpan μ : ℤ) ∣ (k : ℤ) - ℓ n then
      (Scalar.latticeSpan μ : ℝ) / n * (g ((k : ℝ) / n) *
        kendallKernel θ x ((k : ℝ) / n)) else 0
    let E : ℕ → ℝ := fun k => F k - Rf k
    let M : ℕ → ℝ := fun k => if k ≤ N then δ * (‖hgB‖ + 1) / n else 0
    have hcut {k : ℕ} (hk : N < k) : g ((k : ℝ) / n) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hN : b * n ≤ (N : ℝ) := Nat.le_ceil _
      have hk' : b * n < (k : ℝ) := hN.trans_lt (by exact_mod_cast hk)
      have hle := habove _ hmem
      have hgt : b < (k : ℝ) / n := (lt_div_iff₀ hnR).2 hk'
      linarith
    have hzero_large {k : ℕ} (hk : N < k) : E k = 0 := by
      dsimp [E, F, Rf]
      simp [hcut hk]
    have hFs : Summable F := by
      apply summable_of_hasFiniteSupport
      apply (Set.finite_le_nat N).subset
      intro k hk
      by_contra hkn
      exact hk (by dsimp [F]; simp [hcut (lt_of_not_ge hkn)])
    have hRs : Summable Rf := by
      apply summable_of_hasFiniteSupport
      apply (Set.finite_le_nat N).subset
      intro k hk
      by_contra hkn
      exact hk (by dsimp [Rf]; simp [hcut (lt_of_not_ge hkn)])
    have hEs : Summable E := hFs.sub hRs
    have hMs : Summable M := by
      apply summable_of_hasFiniteSupport
      apply (Set.finite_le_nat N).subset
      intro k hk
      by_contra hkn
      have hkN : ¬k ≤ N := hkn
      simp [M, hkN] at hk
    have hbound (k : ℕ) : ‖E k‖ ≤ M k := by
      by_cases hk : k ≤ N
      · dsimp [M]
        simp only [hk, ↓reduceIte]
        by_cases hgk : g ((k : ℝ) / n) = 0
        · dsimp [E, F, Rf]
          simp [hgk]
          positivity
        · have hkmem : (k : ℝ) / n ∈ tsupport g := subset_tsupport _ hgk
          have hak : a * (n : ℝ) ≤ k := (le_div_iff₀ hnR).1 (hbelow _ hkmem)
          have hkb : (k : ℝ) ≤ b * n := (div_le_iff₀ hnR).1 (habove _ hkmem)
          by_cases hd : (Scalar.latticeSpan μ : ℤ) ∣ (k : ℤ) - ℓ n
          · have hm := hN₀ n hn0 k hak hkb hd
            have heq : E k = (1 / n) * g ((k : ℝ) / n) *
                ((n : ℝ) * (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
                  {w | walkHitTime ((ℓ n)) w = (k : ℕ∞)} -
                  Scalar.latticeSpan μ * kendallKernel θ x ((k : ℝ) / n)) := by
              dsimp [E, F, Rf]
              simp only [hd, ↓reduceIte]
              field_simp
            have hgnorm : |g ((k : ℝ) / n)| ≤ ‖hgB‖ + 1 := by
              change ‖g ((k : ℝ) / n)‖ ≤ ‖hgB‖ + 1
              rw [← show hgB ((k : ℝ) / n) = g ((k : ℝ) / n) by simp [hgB, ofCompactSupport]]
              exact (hgB.norm_coe_le_norm _).trans (le_add_of_nonneg_right zero_le_one)
            rw [heq, abs_mul, abs_mul, abs_of_pos (one_div_pos.2 hnR)]
            calc
              1 / n * |g ((k : ℝ) / n)| *
                  |(n : ℝ) * (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
                    {w | walkHitTime ((ℓ n)) w = (k : ℕ∞)} -
                    Scalar.latticeSpan μ * kendallKernel θ x ((k : ℝ) / n)|
                  ≤ (1 / n * |g ((k : ℝ) / n)|) * δ :=
                mul_le_mul_of_nonneg_left hm (by positivity)
              _ ≤ (1 / n * (‖hgB‖ + 1)) * δ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hgnorm (by positivity)) hδ.le
              _ = δ * (‖hgB‖ + 1) / n := by ring
          · dsimp [E, F, Rf]
            simp only [hd, ↓reduceIte, sub_zero]
            rw [walkHitTime_mass_eq_zero_of_not_dvd h (hN₂ n hn2) hd]
            norm_num
            positivity
      · dsimp [M]
        simp only [hk, ↓reduceIte]
        simp [hzero_large (lt_of_not_ge hk)]
    have hM_eval : ∑' k, M k = (N + 1 : ℕ) * (δ * (‖hgB‖ + 1) / n) := by
      rw [tsum_eq_sum (s := Finset.range (N + 1))]
      · calc
          ∑ k ∈ Finset.range (N + 1), M k =
              ∑ _k ∈ Finset.range (N + 1), δ * (‖hgB‖ + 1) / n := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkN := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
            simp [M, hkN]
          _ = (N + 1 : ℕ) * (δ * (‖hgB‖ + 1) / n) := by simp
      · intro k hk
        have hkn : N < k := by
          simp only [Finset.mem_range, not_lt] at hk
          omega
        simp [M, not_le.mpr hkn]
    have herr := hEs.hasSum.norm_le_of_bounded (hM_eval ▸ hMs.hasSum) hbound
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    rw [← hFs.tsum_sub hRs]
    change ‖∑' k, E k‖ < ε
    apply herr.trans_lt
    have hNlt : (N : ℝ) < b * n + 1 := Nat.ceil_lt_add_one (by positivity)
    have hmul : ((N + 1 : ℕ) : ℝ) * (δ * (‖hgB‖ + 1) / n) < δ * C₀ := by
      have hNbound : ((N + 1 : ℕ) : ℝ) / n < b + 2 := by
        apply (div_lt_iff₀ hnR).2
        have hnNat2 : 2 ≤ (n : ℝ) := by exact_mod_cast hN₁ n hn1
        calc
          ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; rfl
          _ < (b * n + 1) + 1 := by linarith [hNlt]
          _ ≤ (b + 2) * n := by nlinarith
      have hpos' : 0 ≤ δ * (‖hgB‖ + 1) := by positivity
      dsimp [C₀]
      calc
        ((N + 1 : ℕ) : ℝ) * (δ * (‖hgB‖ + 1) / n) =
            (((N + 1 : ℕ) : ℝ) / n) * (δ * (‖hgB‖ + 1)) := by ring
        _ < (b + 2) * (δ * (‖hgB‖ + 1)) :=
          mul_lt_mul_of_pos_right hNbound (by positivity)
        _ = δ * ((b + 2) * (‖hgB‖ + 1)) := by ring
    have hcancel : δ * C₀ = ε := by
      dsimp [δ]
      field_simp
    rw [hcancel] at hmul
    exact hmul
  have H := hR.add hdiff
  rw [add_zero] at H
  have Heq : ∀ᶠ n in atTop, (∫ t, g t ∂walkPassageLaw μ (ℓ n) n) =
      ∑' k : ℕ, g ((k : ℝ) / n) *
        (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
          {w | walkHitTime (ℓ n) w = (k : ℕ∞)} := by
    filter_upwards [hℓ, eventually_ge_atTop 1] with n hnℓ hn
    have hfun : (hgB : ℝ → ℝ) = g := by simp [hgB, ofCompactSupport]
    rw [← hfun]
    apply integral_walkPassageLaw_eq_tsum h hnℓ hn hgB
    intro t ht
    change g t = 0
    exact hzero t ht
  exact H.congr' (Heq.mono fun n hn => by rw [← hn]; ring)

/-- **Kendall, tested against compactly supported continuous functions.** Combining the previous
statement with `tendsto_walkPassageLaw` and uniqueness of weak limits. -/
theorem integral_passageLaw_eq_kendall {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x)
    {g : ℝ → ℝ} (hg : Continuous g) (hsupp : HasCompactSupport g) (hpos : tsupport g ⊆ Ioi 0) :
    ∫ t, g t ∂(passageLaw θ x) = ∫ s in Ioi 0, g s * kendallKernel θ (x : ℝ) s := by
  obtain ⟨μ, B, h⟩ := exists_stableDomain hθ
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  let ℓ : ℕ → ℕ := fun n => ⌊(x : ℝ) * B n⌋₊ + 1
  have hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n := .of_forall fun n => by simp [ℓ]
  have hxB : Tendsto (fun n : ℕ => (x : ℝ) * B n) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hxR).2 (Scalar.tendsto_atTop h)
  have hfloor : Tendsto (fun n : ℕ => ((⌊(x : ℝ) * B n⌋₊ : ℕ) : ℝ) /
      ((x : ℝ) * B n)) atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp hxB
  have hone : Tendsto (fun n : ℕ => 1 / B n) atTop (𝓝 0) := by
    have hBtop : Tendsto B atTop atTop := Scalar.tendsto_atTop h
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hBtop.eventually (Ioi_mem_atTop (1 / ε)))
    refine ⟨N, fun n hn => ?_⟩
    have hBn : 1 / ε < B n := hN n hn
    have hBp : 0 < B n := (one_div_pos.2 hε).trans hBn
    rw [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.2 hBp)]
    simpa only [one_div, inv_inv] using one_div_lt_one_div_of_lt (one_div_pos.2 hε) hBn

  have hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 (x : ℝ)) := by
    have H := (hfloor.mul_const (x : ℝ)).add hone
    simp only [one_mul, add_zero] at H
    refine H.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hB : B n ≠ 0 := (h.pos n hn).ne'
    dsimp [ℓ]
    push_cast
    field_simp [hB, hxR.ne']
  let f : BoundedContinuousFunction ℝ ℝ := ofCompactSupport g hg hsupp
  have h1 := tendsto_walkPassageLaw h hx hℓ hscale f
  have h2 := tendsto_integral_walkPassageLaw_kendall h hxR hℓ hscale hg hsupp hpos
  exact tendsto_nhds_unique (by simpa [f, ofCompactSupport] using h1) h2

private lemma map_comap_passageLaw_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    ((passageLaw θ x).comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).map Subtype.val = passageLaw θ x := by
  rw [map_comap_subtype_coe measurableSet_Ioi]
  apply Measure.restrict_eq_self_of_ae_mem
  have hnull := passageLaw_Iic_zero hθ hx
  filter_upwards [(measure_eq_zero_iff_ae_notMem).1 hnull] with t ht
  simpa only [Set.mem_Iic, not_le, Set.mem_Ioi] using ht

private lemma map_comap_kendall_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} :
    ((Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume).withDensity
      (fun s => ENNReal.ofReal (kendallKernel θ (x : ℝ) (s : ℝ)))).map Subtype.val =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (x / s * stableDensityAt θ s (-(x : ℝ)))) := by
  have _hθ := hθ  -- keeps the hypothesis used (unused-variable linter)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_subtype_coe hA, withDensity_apply _ hA,
    withDensity_apply _ (hA.preimage measurable_subtype_coe)]
  rw [setLIntegral_subtype measurableSet_Ioi (Subtype.val ⁻¹' A)
    (fun s => ENNReal.ofReal (kendallKernel θ (x : ℝ) s))]
  have hset : (Subtype.val : Ioi (0 : ℝ) → ℝ) ''
      (Subtype.val ⁻¹' A) = A ∩ Ioi (0 : ℝ) := by
    ext t
    simp [and_comm]
  rw [hset, Measure.restrict_restrict hA]
  rfl

/-- **Kendall's identity** for EVERY `x > 0` (not just a.e. `x`):
the law of `T_x = inf{t | X_t < -x}` on real time has density `(x/s) p_s(-x)` on `(0, ∞)`. -/
theorem kendall {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    passageLaw θ x =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (x / s * stableDensityAt θ s (-(x : ℝ)))) := by
  let P : Measure (Ioi (0 : ℝ)) := (passageLaw θ x).comap Subtype.val
  let V : Measure (Ioi (0 : ℝ)) :=
    (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume).withDensity
    (fun s => ENNReal.ofReal (kendallKernel θ (x : ℝ) (s : ℝ)))
  have heq : P = V := by
    dsimp [P, V]
    let _ : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
    let K : ℕ → Set (Ioi (0 : ℝ)) := fun n => Subtype.val ⁻¹'
      Set.Icc (1 / (n + 1 : ℝ)) (n + 1)
    let _ : SigmaCompactSpace (Ioi (0 : ℝ)) :=
      SigmaCompactSpace_iff_exists_compact_covering.2 ⟨K, (fun n => by
        apply (isOpen_Ioi.isOpenEmbedding_subtypeVal).isInducing.isCompact_preimage' isCompact_Icc
        intro t ht
        exact ⟨⟨t, (one_div_pos.2 (by positivity)).trans_le ht.1⟩, rfl⟩), by
        ext s
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        have hs : 0 < (s : ℝ) := s.property
        obtain ⟨n₁, hn₁⟩ := exists_nat_gt (1 / (s : ℝ))
        obtain ⟨n₂, hn₂⟩ := exists_nat_gt (s : ℝ)
        let N := max (n₁ + 1) (n₂ + 1)
        refine ⟨N, ?_, ?_⟩
        · have hNg : 1 / (s : ℝ) < (N : ℝ) := hn₁.trans_le (by
            exact_mod_cast (show n₁ ≤ N from le_trans (Nat.le_succ n₁) (le_max_left _ _)))
          have hNpos : 0 < (N : ℝ) := (one_div_pos.2 hs).trans hNg
          have hstep : (1 : ℝ) / (N + 1) < 1 / N :=
            one_div_lt_one_div_of_lt hNpos (by linarith)
          have hrec : (1 : ℝ) / N < s := by
            simpa only [one_div, inv_inv] using one_div_lt_one_div_of_lt
              (one_div_pos.2 hs) hNg
          exact (hstep.trans hrec).le
        · have hN₂ : (n₂ : ℝ) ≤ (N : ℝ) + 1 := by
            have hle : n₂ ≤ N + 1 :=
              (show n₂ ≤ N from le_trans (Nat.le_succ n₂) (le_max_right _ _)) |>.trans
                (Nat.le_succ N)
            exact_mod_cast hle
          exact hn₂.le.trans hN₂⟩
    let _ : IsProbabilityMeasure (passageLaw θ x) := passageLaw_isProbabilityMeasure hθ x
    let _ : (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (passageLaw θ x)).Regular :=
      Measure.Regular.comap' (passageLaw θ x) isOpen_Ioi.isOpenEmbedding_subtypeVal
    let _ : IsLocallyFiniteMeasure (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) :=
      ⟨fun s => by
        let U : Set (Ioi (0 : ℝ)) := Subtype.val ⁻¹'
          Set.Ioo ((s : ℝ) / 2) ((s : ℝ) + 1)
        have hs : 0 < (s : ℝ) := s.property
        have hU : IsOpen U := isOpen_Ioo.preimage continuous_subtype_val
        refine ⟨U, hU.mem_nhds ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith [hs])
          · exact (by linarith [hs] : (s : ℝ) < (s : ℝ) + 1)
        · rw [(isOpen_Ioi.isOpenEmbedding_subtypeVal).measurableEmbedding.comap_apply]
          have himage : (Subtype.val : Ioi (0 : ℝ) → ℝ) '' U =
              Set.Ioo ((s : ℝ) / 2) ((s : ℝ) + 1) := by
            ext t
            simp [U]
            intro ht ht'
            linarith [hs]
          rw [himage, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top
      ⟩
    let _ : (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume).Regular :=
      Measure.Regular.comap' volume isOpen_Ioi.isOpenEmbedding_subtypeVal
    let hcont : Continuous (fun s : Ioi (0 : ℝ) => kendallKernel θ (x : ℝ) (s : ℝ)) :=
      (continuousOn_kendallKernel_time hθ (x : ℝ)).domRestrict
    let _ : IsLocallyFiniteMeasure V := IsLocallyFiniteMeasure.withDensity_ofReal hcont
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    let F : ℝ → ℝ := Subtype.val.extend f.1 0
    have hFc : Continuous F := by
      exact HasCompactSupport.continuous_extend_zero isOpen_Ioi f.continuous f.hasCompactSupport
    have hFs : HasCompactSupport F := by
      exact f.hasCompactSupport.extend_zero continuous_subtype_val
    have hFpos : tsupport F ⊆ Ioi 0 := by
      have hsub := f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val
      intro s hs
      have hmem : s ∈ Subtype.val '' tsupport (f : Ioi (0 : ℝ) → ℝ) := hsub hs
      exact Set.mem_of_mem_of_subset hmem (Subtype.coe_image_subset _ _)
    calc
      ∫ s, f s ∂P = ∫ s in Ioi 0, F s ∂passageLaw θ x := by
        rw [← integral_subtype_comap measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards [] with s
        simp [F]
      _ = ∫ s, F s ∂passageLaw θ x := by
        rw [Measure.restrict_eq_self_of_ae_mem (by
          filter_upwards [(measure_eq_zero_iff_ae_notMem).1 (passageLaw_Iic_zero hθ hx)] with t ht
          simpa only [Set.mem_Iic, not_le, Set.mem_Ioi] using ht)]
      _ = ∫ s in Ioi 0, F s * kendallKernel θ (x : ℝ) s :=
        integral_passageLaw_eq_kendall hθ hx hFc hFs hFpos
      _ = ∫ s, f s ∂V := by
        have hmeas : Measurable (fun s : Ioi (0 : ℝ) =>
            ENNReal.ofReal (kendallKernel θ (x : ℝ) (s : ℝ))) :=
          (ENNReal.measurable_ofReal.comp
      ((continuousOn_kendallKernel_time hθ (x : ℝ)).domRestrict).measurable)
        simp only [V]
        rw [integral_withDensity_eq_integral_toReal_smul hmeas (by simp)]
        rw [← integral_subtype_comap measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards [] with s
        have hs : 0 < (s : ℝ) := s.property
        have hK : 0 ≤ kendallKernel θ (x : ℝ) s :=
          kendallKernel_nonneg hθ (by positivity) hs
        simp [F, hK, mul_comm]

  calc
    passageLaw θ x = P.map Subtype.val := (map_comap_passageLaw_Ioi hθ hx).symm
    _ = V.map Subtype.val := congrArg (Measure.map Subtype.val) heq
    _ = _ := map_comap_kendall_Ioi hθ

/-- Corollary: total mass one of the Kendall density. -/
theorem lintegral_kendallKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (kendallKernel θ (x : ℝ) s) = 1 := by
  let _ : IsProbabilityMeasure (passageLaw θ x) := passageLaw_isProbabilityMeasure hθ x
  have hm := congrArg (fun m : Measure ℝ => m Set.univ) (kendall hθ hx)
  rw [withDensity_apply _ MeasurableSet.univ] at hm
  simpa [Measure.restrict_apply_univ, kendallKernel] using hm.symm

end BGW.StableTrees
