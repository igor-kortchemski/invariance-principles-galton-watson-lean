module

public import BGWLeaves.GeneralAInf.Defs
public import BGWLeaves.GeneralA.MarkedTime
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The A-time step law is in the domain of attraction

The characteristic-function route to the domain of attraction of the A-time step law `ν = blockStep μ A`: `blockStep_firstMoment`, `blockStep_charFun_identity`, `blockStep_isStableAttracted` (the only new analytic ingredient: `φ_ν = φ_α / (1 - φ_W + φ_α)`, Lévy continuity), and the time-changed norming `b_n = B_{⌊n/μ(A)⌋}`: `monotone_norming_floor`, `norming_floor_ratio`.  The theorems are those stated in
`BGWLeaves.GeneralAInf`; they are exported in namespace `BGWLeaves.GeneralAInf.BlockStable` with exactly the types
stated there.
-/

@[expose] public section

namespace BGWLeaves.GeneralAInf.BlockStable

/- The logarithm helpers below resolve the complex phase using compactness and
an anchored continuous logarithm on an interval. The first-order defect then
transfers through the block CF identity and the floor time change. -/


open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees
open BGWLeaves.StableAnalysis BGWLeaves.GeneralA
open MarkedWalk Regroup MarkedTime Moments
open scoped ENNReal Topology

private instance walk_probability (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n).conv ν))

private theorem walk_firstMoment_bound (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : ℤ => (z : ℝ)) ν) (k : ℕ) :
    Integrable (fun z : ℤ => (z : ℝ)) (intWalk ν k) ∧
    mean (intWalk ν k) = k * mean ν ∧
    (∫ z : ℤ, ‖(z : ℝ)‖ ∂intWalk ν k) ≤ k * (∫ z : ℤ, ‖(z : ℝ)‖ ∂ν) := by
  induction k with
  | zero => simp [intWalk, mean, integrable_dirac]
  | succ k ih =>
    obtain ⟨h, hm⟩ := conv_firstMoment (intWalk ν k) ν ih.1 hi
    refine ⟨h, ?_, ?_⟩
    · change mean ((intWalk ν k).conv ν) = _
      rw [hm, ih.2.1, Nat.cast_succ]
      ring
    · rw [intWalk, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
      have hl : Integrable (fun p : ℤ × ℤ => ‖(p.1 : ℝ) + (p.2 : ℝ)‖)
          ((intWalk ν k).prod ν) := ((ih.1.comp_fst ν).add (hi.comp_snd (intWalk ν k))).norm
      have hr : Integrable (fun p : ℤ × ℤ => ‖(p.1 : ℝ)‖ + ‖(p.2 : ℝ)‖)
          ((intWalk ν k).prod ν) := (ih.1.norm.comp_fst ν).add (hi.norm.comp_snd (intWalk ν k))
      have hb := integral_mono hl hr (fun p => norm_add_le (p.1 : ℝ) (p.2 : ℝ))
      rw [integral_add (ih.1.norm.comp_fst ν) (hi.norm.comp_snd (intWalk ν k)),
        integral_fun_fst (fun z : ℤ => ‖(z : ℝ)‖),
        integral_fun_snd (fun z : ℤ => ‖(z : ℝ)‖)] at hb
      simp only [probReal_univ, one_smul] at hb
      simp only [Int.cast_add]
      push_cast
      linarith [ih.2.2]

/-- First moments of geometric sums, without any second-moment assumption. -/
theorem geometricLaw_firstMoment_of_integrable {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q ≤ 1)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) :
    Integrable (fun z : ℤ => (z : ℝ)) (geometricLaw q ν) ∧
      mean (geometricLaw q ν) = (1 - q.toReal) / q.toReal * mean ν := by
  have hqtop : q ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hq1 ENNReal.one_lt_top)
  have hq : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hr : 0 ≤ 1 - q.toReal := sub_nonneg.mpr
    (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hq1)
  have hrat : ‖1 - q.toReal‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
  let ρ := fun k : ℕ => (q * (1 - q) ^ k) • intWalk ν k
  have hi : ∀ k, Integrable (fun z : ℤ => (z : ℝ)) (ρ k) := by
    intro k
    apply (walk_firstMoment_bound ν hint k).1.smul_measure
    have : 1 - q ≠ ⊤ := by finiteness
    finiteness
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one hrat).summable.mul_left
    (q.toReal * (∫ z : ℤ, ‖(z : ℝ)‖ ∂ν))
  have hsumNorm : Summable (fun k => ∫ z : ℤ, ‖(z : ℝ)‖ ∂ρ k) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) _ hsum
    intro k
    dsimp only [ρ]
    rw [integral_smul_measure]
    simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_one]
    calc
      _ ≤ (q.toReal * (1 - q.toReal) ^ k) *
          ((k : ℝ) * (∫ z : ℤ, ‖(z : ℝ)‖ ∂ν)) :=
        mul_le_mul_of_nonneg_left (walk_firstMoment_bound ν hint k).2.2 (by positivity)
      _ = _ := by ring
  have hm : Integrable (fun z : ℤ => (z : ℝ)) (Measure.sum ρ) :=
    integrable_sum_measure hi hsumNorm
  refine ⟨hm, ?_⟩
  rw [mean, geometricLaw, integral_sum_measure hm]
  have hw (k : ℕ) := (walk_firstMoment_bound ν hint k).2.1
  change (∑' k : ℕ, ∫ z : ℤ, (z : ℝ) ∂((q * (1 - q) ^ k) • intWalk ν k)) = _
  simp_rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_one]
  change (∑' k : ℕ, q.toReal * (1 - q.toReal) ^ k * mean (intWalk ν k)) = _
  simp_rw [hw]
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hrat).mul_left (q.toReal * mean ν)
  have he : q.toReal * mean ν * ((1 - q.toReal) / (1 - (1 - q.toReal)) ^ 2) =
      (1 - q.toReal) / q.toReal * mean ν := by
    rw [show 1 - (1 - q.toReal) = q.toReal by ring]
    field_simp
  rw [he] at hs
  convert hs.tsum_eq using 1
  apply tsum_congr
  intro k
  ring

theorem blockStep_firstMoment {μ : PMF ℕ} (hc : IsCritical μ) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) :
    IsProbabilityMeasure (blockStep μ A) ∧ Integrable (fun z : ℤ => (z : ℝ)) (blockStep μ A) ∧
      mean (blockStep μ A) = 0 := by
  let α := markedStep (fun k => μ k) A
  let β := unmarkedStep (fun k => μ k) A
  have : IsFiniteMeasure α := by dsimp [α]; rw [markedStep_eq_map_restrict]; infer_instance
  have : IsFiniteMeasure β := by dsimp [β, unmarkedStep]; rw [markedStep_eq_map_restrict]; infer_instance
  let τ := normalized α
  let ρ := normalized β
  let q := μ.toMeasure A
  have := normalized_probability α
  have := normalized_probability β
  have hqtop : q ≠ ⊤ := measure_ne_top _ _
  have hqle : q ≤ 1 := prob_le_one
  have hq : 0 < q.toReal := ENNReal.toReal_pos hA hqtop
  have hr : 1 - q ≠ ⊤ := by finiteness
  have hα : q • τ = α := by simpa only [α, markedStep_mass] using mass_smul_normalized α
  have hβmass : β Set.univ = 1 - q := by
    dsimp [β, unmarkedStep, q]
    rw [markedStep_mass, prob_compl_eq_one_sub MeasurableSet.of_discrete]
  have hβ : (1 - q) • ρ = β := by rw [← hβmass]; exact mass_smul_normalized β
  have hstep : stepLaw μ = α + β := stepLaw_decomposition μ A
  have hnorm : stepLaw μ = q • τ + (1 - q) • ρ := by rw [hα, hβ]; exact hstep
  have hαle : α ≤ stepLaw μ := by rw [hstep]; exact Measure.le_add_right le_rfl
  have hβle : β ≤ stepLaw μ := by rw [hstep]; exact Measure.le_add_left le_rfl
  have hτ := integrable_normalized α (fun z : ℤ => (z : ℝ)) ((integrable_stepLaw hc).mono_measure hαle)
  have hρ := integrable_normalized β (fun z : ℤ => (z : ℝ)) ((integrable_stepLaw hc).mono_measure hβle)
  have hmean : q.toReal * mean τ + (1 - q.toReal) * mean ρ = 0 := by
    have h := mean_stepLaw hc
    rw [mean, hnorm, integral_add_measure (hτ.smul_measure hqtop) (hρ.smul_measure hr),
      integral_smul_measure, integral_smul_measure] at h
    simpa only [smul_eq_mul, ENNReal.toReal_sub_of_le hqle ENNReal.one_ne_top,
      ENNReal.toReal_one, mean] using h
  let H := geometricLaw q ρ
  have := geometricLaw_probability hA hqle ρ
  obtain ⟨hH, hHM⟩ := geometricLaw_firstMoment_of_integrable hA hqle ρ hρ
  obtain ⟨hν, hνM⟩ := conv_firstMoment τ H hτ hH
  refine ⟨blockLaw_probability hA, ?_⟩
  change Integrable _ (blockLaw α β) ∧ mean (blockLaw α β) = 0
  rw [blockLaw_eq_normalized]
  refine ⟨hν, ?_⟩
  rw [hνM, hHM]
  apply (mul_eq_zero.mp ?_).resolve_left hq.ne'
  calc
    q.toReal * (mean τ + (1 - q.toReal) / q.toReal * mean ρ) =
        q.toReal * mean τ + (1 - q.toReal) * mean ρ := by field_simp
    _ = 0 := hmean

private theorem blockLaw_renewal (α β : Measure ℤ) [SFinite α] [SFinite β] :
    blockLaw α β = α + (blockLaw α β).conv β := by
  have hw : ∀ k, SFinite (intWalk β k) := by
    intro k
    induction k with
    | zero => simp only [intWalk]; infer_instance
    | succ k ih => simp only [intWalk]; infer_instance
  let := hw
  rw [blockLaw, conv_sum_right, conv_sum_left]
  have hshift : (Measure.sum fun k => α.conv (intWalk β k)) =
      α.conv (intWalk β 0) + Measure.sum (fun k => α.conv (intWalk β (k + 1))) := by
    ext s hs
    simp only [Measure.sum_apply _ hs, Measure.add_apply]
    exact tsum_eq_zero_add' ENNReal.summable
  rw [hshift]
  simp only [intWalk, Measure.conv_dirac, add_zero, Measure.map_id']
  congr 1
  congr 1
  funext k
  exact (Measure.conv_assoc α (intWalk β k) β).symm

private theorem charFun_cast_add (α β : Measure ℤ) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (t : ℝ) :
    charFun ((α + β).map (fun z : ℤ => (z : ℝ))) t =
      charFun (α.map (fun z : ℤ => (z : ℝ))) t +
      charFun (β.map (fun z : ℤ => (z : ℝ))) t := by
  rw [Measure.map_add _ _ (by fun_prop), charFun_apply_real, charFun_apply_real, charFun_apply_real]
  apply integral_add_measure <;>
    exact Integrable.of_bound (by fun_prop) 1 (by filter_upwards [] with x; simp [Complex.norm_exp])

private theorem charFun_cast_conv (α β : Measure ℤ) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (t : ℝ) :
    charFun ((α.conv β).map (fun z : ℤ => (z : ℝ))) t =
      charFun (α.map (fun z : ℤ => (z : ℝ))) t *
      charFun (β.map (fun z : ℤ => (z : ℝ))) t := by
  let L : ℤ →+ ℝ := Int.castAddHom ℝ
  rw [show (fun z : ℤ => (z : ℝ)) = L from rfl,
    Measure.map_conv_addMonoidHom L (by fun_prop), charFun_conv]

theorem blockStep_charFun_identity {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) (t : ℝ) :
    charFun ((blockStep μ A).map (fun z : ℤ => (z : ℝ))) t *
        (1 - charFun ((stepLaw μ).map (fun z : ℤ => (z : ℝ))) t +
          charFun ((markedStep (fun k => μ k) A).map (fun z : ℤ => (z : ℝ))) t) =
      charFun ((markedStep (fun k => μ k) A).map (fun z : ℤ => (z : ℝ))) t := by
  let α := markedStep (fun k => μ k) A
  let β := unmarkedStep (fun k => μ k) A
  have : IsFiniteMeasure α := by dsimp [α]; rw [markedStep_eq_map_restrict]; infer_instance
  have : IsFiniteMeasure β := by dsimp [β, unmarkedStep]; rw [markedStep_eq_map_restrict]; infer_instance
  have := blockLaw_probability hA
  have h : charFun ((blockStep μ A).map (fun z : ℤ => (z : ℝ))) t =
      charFun (α.map (fun z : ℤ => (z : ℝ))) t +
      charFun ((blockStep μ A).map (fun z : ℤ => (z : ℝ))) t *
        charFun (β.map (fun z : ℤ => (z : ℝ))) t := by
    conv_lhs => rw [show blockStep μ A = α + (blockStep μ A).conv β from blockLaw_renewal α β]
    rw [charFun_cast_add, charFun_cast_conv]
  rw [stepLaw_decomposition μ A, charFun_cast_add]
  dsimp only [α, β] at h
  linear_combination h

set_option linter.unusedVariables false in
theorem monotone_norming_floor {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Monotone (fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) := by
  obtain ⟨a, ha⟩ := hDA
  have hm := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨a, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted ha⟩).1
  intro i j hij
  apply hm
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by exact_mod_cast hij) ENNReal.toReal_nonneg)

set_option linter.unusedVariables false in
theorem norming_floor_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Tendsto (fun n : ℕ => norming (stepLaw μ) θ n /
        norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ))) := by
  obtain ⟨a, ha⟩ := hDA
  have hattr := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨a, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted ha⟩
  have hm : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have ht := TransformConvergence.regularlyVaryingSeq (stepLaw μ) hattr
    ((μ.toMeasure A).toReal)⁻¹ (inv_pos.mpr hm)
  have ht' := ht.inv₀ (Real.rpow_pos_of_pos (inv_pos.mpr hm) (1 / θ)).ne'
  simpa only [inv_div, div_eq_mul_inv, mul_comm, mul_inv_rev, Real.inv_rpow hm.le, inv_inv] using ht'

/- Compactness upgrades moving-frequency convergence to eventual uniform membership
in an open set. This is the only compact-uniform convergence fact needed below. -/
private theorem eventually_on_Icc_of_moving {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hmove : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ (s : ℕ → ℝ) (u : ℝ),
      Tendsto s atTop (𝓝 u) → Tendsto (fun n => F (j n) (s n)) atTop (𝓝 (f u)))
    (R : ℝ) {U : Set ℂ} (hU : IsOpen U) (hf : ∀ u ∈ Set.Icc (-R) R, f u ∈ U) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (-R) R, F n t ∈ U := by
  classical
  by_contra h
  have hbad : ∀ k : ℕ, ∃ n ≥ k, ∃ t ∈ Set.Icc (-R) R, F n t ∉ U := by
    simpa only [eventually_atTop, not_exists, not_forall, not_imp, exists_prop] using h
  choose j hj s hs hnot using hbad
  have hjtop : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  obtain ⟨u, hu, a, ha, hsu⟩ := isCompact_Icc.tendsto_subseq hs
  have he := (hmove (fun n => j (a n)) (hjtop.comp ha.tendsto_atTop)
    (fun n => s (a n)) u hsu).eventually (hU.mem_nhds (hf u hu))
  obtain ⟨n, hn⟩ := he.exists
  exact hnot (a n) hn

/- An anchored continuous logarithm cannot leave the principal strip while its
exponential stays in the right half-plane. -/
private theorem anchored_log_eq {R : ℝ} (hR : 0 ≤ R) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc (-R) R)) (h0 : g 0 = 0)
    (hpos : ∀ t ∈ Set.Icc (-R) R, 0 < (Complex.exp (g t)).re)
    {t : ℝ} (ht : t ∈ Set.Icc (-R) R) : g t = Complex.log (Complex.exp (g t)) := by
  have hz : (0 : ℝ) ∈ Set.Icc (-R) R := ⟨by linarith, hR⟩
  have hπ (x : ℝ) (hx : x ∈ Set.Icc (-R) R) : (g x).im ≠ Real.pi := by
    intro he
    have hp := hpos x hx
    rw [Complex.exp_re, he, Real.cos_pi] at hp
    nlinarith [Real.exp_pos (g x).re]
  have hnπ (x : ℝ) (hx : x ∈ Set.Icc (-R) R) : (g x).im ≠ -Real.pi := by
    intro he
    have hp := hpos x hx
    rw [Complex.exp_re, he, Real.cos_neg, Real.cos_pi] at hp
    nlinarith [Real.exp_pos (g x).re]
  have hu : (g t).im < Real.pi := by
    by_contra h
    have hm : Real.pi ∈ Set.Icc (g 0).im (g t).im := by
      rw [h0]; simp only [Complex.zero_im]; exact ⟨Real.pi_pos.le, le_of_not_gt h⟩
    obtain ⟨x, hx, he⟩ := isPreconnected_Icc.intermediate_value hz ht (Complex.continuous_im.comp_continuousOn hg) hm
    exact hπ x hx he
  have hl : -Real.pi < (g t).im := by
    by_contra h
    have hm : -Real.pi ∈ Set.Icc (g t).im (g 0).im := by
      rw [h0]; simp only [Complex.zero_im]; exact ⟨le_of_not_gt h, by linarith [Real.pi_pos]⟩
    obtain ⟨x, hx, he⟩ := isPreconnected_Icc.intermediate_value ht hz (Complex.continuous_im.comp_continuousOn hg) hm
    exact hnπ x hx he
  exact (Complex.log_exp hl hu.le).symm

private theorem log_dslope_limit {z : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 1)) :
    Tendsto (fun n => dslope Complex.log 1 (z n)) atTop (𝓝 1) := by
  have hc : ContinuousAt (dslope Complex.log 1) 1 :=
    continuousAt_dslope_same.mpr (Complex.differentiableAt_log (by simp))
  simpa only [Function.comp_def, dslope_same, Complex.deriv_log (by simp : (1 : ℂ) ∈ Complex.slitPlane), inv_one]
    using hc.tendsto.comp hz

private theorem defect_of_log_limit {z : ℕ → ℂ} {L : ℂ}
    (hz : Tendsto z atTop (𝓝 1))
    (hl : Tendsto (fun n : ℕ => (n : ℂ) * Complex.log (z n)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℂ) * (z n - 1)) atTop (𝓝 L) := by
  have hd := log_dslope_limit hz
  have hne := hd.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  have ht := hl.div hd (by norm_num : (1 : ℂ) ≠ 0)
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [hne] with n hn
  have hid := sub_smul_dslope Complex.log 1 (z n)
  simp only [smul_eq_mul, Complex.log_one, sub_zero] at hid
  apply (div_eq_iff hn).2
  linear_combination -(n : ℂ) * hid

private theorem powers_of_defect_limit {z : ℕ → ℂ} {L : ℂ}
    (hz : Tendsto z atTop (𝓝 1))
    (hd : Tendsto (fun n : ℕ => (n : ℂ) * (z n - 1)) atTop (𝓝 L)) :
    Tendsto (fun n => z n ^ n) atTop (𝓝 (Complex.exp L)) := by
  have ht := hd.mul (log_dslope_limit hz)
  simp only [mul_one] at ht
  have hl : Tendsto (fun n : ℕ => (n : ℂ) * Complex.log (z n)) atTop (𝓝 L) := by
    apply ht.congr
    intro n
    have hid := sub_smul_dslope Complex.log 1 (z n)
    simp only [smul_eq_mul, Complex.log_one, sub_zero] at hid
    linear_combination (n : ℂ) * hid
  have hne := hz.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  apply (Complex.continuous_exp.tendsto L |>.comp hl).congr'
  filter_upwards [hne] with n hn
  change Complex.exp ((n : ℂ) * Complex.log (z n)) = z n ^ n
  rw [Complex.exp_nat_mul, Complex.exp_log hn]

private theorem log_limit_of_moving_powers {F : ℕ → ℝ → ℂ} {E : ℝ → ℂ}
    (hF : ∀ n, Continuous (F n)) (hF0 : ∀ n, F n 0 = 1)
    (hE : Continuous E) (hE0 : E 0 = 0)
    (hbase : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ (s : ℕ → ℝ) (u : ℝ),
      Tendsto s atTop (𝓝 u) → Tendsto (fun n => F (j n) (s n)) atTop (𝓝 1))
    (hpow : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ (s : ℕ → ℝ) (u : ℝ),
      Tendsto s atTop (𝓝 u) →
        Tendsto (fun n => F (j n) (s n) ^ j n) atTop (𝓝 (Complex.exp (E u))))
    (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * Complex.log (F n t)) atTop (𝓝 (E t)) := by
  let G := fun n t => F n t ^ n / Complex.exp (E t)
  have hGmove : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ (s : ℕ → ℝ) (u : ℝ),
      Tendsto s atTop (𝓝 u) → Tendsto (fun n => G (j n) (s n)) atTop (𝓝 1) := by
    intro j hj s u hs
    have ht := (hpow j hj s u hs).div ((hE.cexp.tendsto u).comp hs) (Complex.exp_ne_zero _)
    change Tendsto (fun n => F (j n) (s n) ^ j n / Complex.exp (E (s n)))
      atTop (𝓝 (Complex.exp (E u) / Complex.exp (E u))) at ht
    simpa only [G, div_self (Complex.exp_ne_zero _)] using ht
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU1 : (1 : ℂ) ∈ U := by norm_num [U]
  have hb := eventually_on_Icc_of_moving (f := fun _ => 1) hbase (|t|) hU (fun _ _ => hU1)
  have hp := eventually_on_Icc_of_moving hGmove (|t|) hU (fun _ _ => hU1)
  have htmem : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  have heq : ∀ᶠ n : ℕ in atTop,
      (n : ℂ) * Complex.log (F n t) - E t = Complex.log (G n t) := by
    filter_upwards [hb, hp] with n hbn hpn
    let g := fun u => (n : ℂ) * Complex.log (F n u) - E u
    have hslit : ∀ u ∈ Set.Icc (-|t|) |t|, F n u ∈ Complex.slitPlane := by
      intro u hu
      exact Or.inl (hbn u hu)
    have hg : ContinuousOn g (Set.Icc (-|t|) |t|) :=
      (continuousOn_const.mul ((hF n).continuousOn.clog hslit)).sub hE.continuousOn
    have h0 : g 0 = 0 := by simp [g, hF0, hE0]
    have hExp (u : ℝ) (hu : u ∈ Set.Icc (-|t|) |t|) : Complex.exp (g u) = G n u := by
      dsimp [g, G]
      rw [Complex.exp_sub, Complex.exp_nat_mul,
        Complex.exp_log (Complex.slitPlane_ne_zero (hslit u hu))]
    have hh := anchored_log_eq (abs_nonneg t) hg h0
      (fun u hu => by rw [hExp u hu]; exact hpn u hu) htmem
    simpa only [hExp t htmem] using hh
  have hGt := hGmove (fun n => n) tendsto_id (fun _ => t) t tendsto_const_nhds
  have hl := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp hGt
  simp only [Complex.log_one] at hl
  have hdiff := hl.congr' (heq.mono fun _ h => h.symm)
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const (E t)

/-- Stable attraction of the marked-time walk via the complex characteristic-function defect. -/
theorem blockStep_isStableAttracted {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    IsStableAttracted (blockStep μ A) θ 0
      (fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) := by
  have _ := hne
  obtain ⟨a, ha⟩ := hDA
  have hW := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨a, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted ha⟩
  rw [mean_stepLaw hc] at hW
  let B := norming (stepLaw μ) θ
  let m := (μ.toMeasure A).toReal
  let k := fun n : ℕ => ⌊(n : ℝ) / m⌋₊
  let b := fun n => B (k n)
  let ν := blockStep μ A
  have hprob : IsProbabilityMeasure ν := (blockStep_firstMoment hc hA).1
  let := hprob
  have : IsFiniteMeasure (markedStep (fun k => μ k) A) := by
    rw [markedStep_eq_map_restrict]
    infer_instance
  have hm : 0 < m := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hBtop : Tendsto B atTop atTop := TransformConvergence.tendsto_atTop (stepLaw μ) hW
  have hktop : Tendsto k atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hm)
  obtain ⟨Q, hQL, hQ⟩ := hW.tendsto_centeredScaledWalkProb
  let E := fun t : ℝ => (-((t : ℂ) * Complex.I)) ^ (θ : ℂ)
  have hθ : 0 < θ := by linarith [hW.alpha_mem.1]
  have hE : Continuous E := by
    apply continuous_iff_continuousAt.2
    intro t
    exact (Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
      (by simpa using hθ)).comp (by fun_prop)
  have hE0 : E 0 = 0 := by simp [E, Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hθ.ne')]
  let F := fun n t => TransformConvergence.stepCharFun (stepLaw μ) (t / B n)
  have hF : ∀ n, Continuous (F n) := by
    intro n
    exact (continuous_charFun (μ := (stepLaw μ).map (fun z : ℤ => (z : ℝ)))).comp
      (continuous_id.div_const (B n))
  have hF0 : ∀ n, F n 0 = 1 := by intro n; simp [F, TransformConvergence.stepCharFun]
  have hbase : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ (s : ℕ → ℝ) (u : ℝ),
      Tendsto s atTop (𝓝 u) → Tendsto (fun n => F (j n) (s n)) atTop (𝓝 1) := by
    intro j hj s u hs
    have ht := (continuous_charFun (μ := (stepLaw μ).map (fun z : ℤ => (z : ℝ)))).continuousAt.tendsto.comp
      (hs.div_atTop (hBtop.comp hj))
    simpa [F, TransformConvergence.stepCharFun, Function.comp_def] using ht
  have hpow : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ (s : ℕ → ℝ) (u : ℝ),
      Tendsto s atTop (𝓝 u) →
        Tendsto (fun n => F (j n) (s n) ^ j n) atTop (𝓝 (Complex.exp (E u))) := by
    intro j hj s u hs
    have hQj : Tendsto (fun n => TransformConvergence.centeredScaledWalkProb (stepLaw μ) 0 B (j n))
        atTop (𝓝 Q) := by
      simpa only [Function.comp_def] using hQ.comp hj
    have ht := Scalar.tendsto_charFun_moving hQj hs
    change Tendsto (fun n => charFun
      (TransformConvergence.centeredScaledWalk (stepLaw μ) 0 (B (j n)) (j n)) (s n))
      atTop (𝓝 (charFun (Q : Measure ℝ) u)) at ht
    rw [Scalar.charFun_eq_stableCF hθ hQL] at ht
    simpa only [F, E, Scalar.stableCF, TransformConvergence.centeredScaledWalk_charFun,
      mul_zero, zero_div, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] using ht
  have hdef (t : ℝ) : Tendsto (fun n : ℕ => (n : ℂ) * (F n t - 1)) atTop (𝓝 (E t)) :=
    defect_of_log_limit (hbase (fun n => n) tendsto_id (fun _ => t) t tendsto_const_nhds)
      (log_limit_of_moving_powers hF hF0 hE hE0 hbase hpow t)
  have hkn : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 m⁻¹) := by
    simpa [k, div_eq_mul_inv, mul_comm, Function.comp_def] using
      ((tendsto_nat_floor_mul_div_atTop (R := ℝ) (inv_pos.mpr hm).le).comp tendsto_natCast_atTop_atTop)
  have hnk : Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop (𝓝 m) := by
    simpa only [inv_div, inv_inv] using hkn.inv₀ (inv_ne_zero hm.ne')
  have hbpos : ∀ᶠ n : ℕ in atTop, 0 < b n :=
    hktop.eventually (eventually_atTop.2 hW.pos)
  have hweak : Tendsto (TransformConvergence.centeredScaledWalkProb ν 0 b) atTop (𝓝 Q) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have hs : Tendsto (fun n => t / b n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hBtop.comp hktop)
    let W := fun n => charFun ((stepLaw μ).map (fun z : ℤ => (z : ℝ))) (t / b n)
    let H := fun n => charFun ((markedStep (fun k => μ k) A).map (fun z : ℤ => (z : ℝ))) (t / b n)
    let Z := fun n => charFun (ν.map (fun z : ℤ => (z : ℝ))) (t / b n)
    let D := fun n => 1 - W n + H n
    have hWlim : Tendsto W atTop (𝓝 1) := by
      simpa [W, Function.comp_def] using (continuous_charFun (μ := (stepLaw μ).map (fun z : ℤ => (z : ℝ)))).continuousAt.tendsto.comp hs
    have hH0 : charFun ((markedStep (fun k => μ k) A).map (fun z : ℤ => (z : ℝ))) 0 = (m : ℂ) := by
      rw [charFun_zero, Measure.real, Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simp [m, markedStep_mass]
    have hHlim : Tendsto H atTop (𝓝 (m : ℂ)) := by
      simpa only [H, Function.comp_def, hH0] using
        (continuous_charFun (μ := (markedStep (fun k => μ k) A).map (fun z : ℤ => (z : ℝ)))).continuousAt.tendsto.comp hs
    have hD : Tendsto D atTop (𝓝 (m : ℂ)) := by
      simpa only [D, sub_self, zero_add] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hWlim).add hHlim
    have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    have hz : Tendsto Z atTop (𝓝 1) := by
      simpa [Z, Function.comp_def] using (continuous_charFun (μ := ν.map (fun z : ℤ => (z : ℝ)))).continuousAt.tendsto.comp hs
    have hwdef : Tendsto (fun n => (k n : ℂ) * (W n - 1)) atTop (𝓝 (E t)) :=
      (hdef t).comp hktop
    have hlim := (hnk.ofReal.mul hwdef).div hD hmC
    have hconst : (m : ℂ) * E t / (m : ℂ) = E t := by field_simp
    rw [hconst] at hlim
    have hnz : ∀ᶠ n : ℕ in atTop, (k n : ℂ) ≠ 0 := by
      filter_upwards [hktop.eventually (eventually_ne_atTop 0)] with n hn
      exact_mod_cast hn
    have hdz := hD.eventually_ne hmC
    have hd : Tendsto (fun n : ℕ => (n : ℂ) * (Z n - 1)) atTop (𝓝 (E t)) := by
      apply hlim.congr'
      filter_upwards [hnz, hdz] with n hkn0 hdn0
      have hid : Z n * D n = H n := blockStep_charFun_identity hA (t / b n)
      have he : Z n - 1 = (W n - 1) / D n := by
        apply (eq_div_iff hdn0).2
        dsimp only [D] at hid ⊢
        linear_combination hid
      change (((n : ℝ) / (k n : ℝ) : ℝ) : ℂ) * ((k n : ℂ) * (W n - 1)) / D n =
        (n : ℂ) * (Z n - 1)
      rw [he]
      push_cast
      field_simp [hkn0, hdn0]
    have hp := powers_of_defect_limit hz hd
    rw [Scalar.charFun_eq_stableCF hθ hQL]
    simpa [Z, E, Scalar.stableCF, TransformConvergence.centeredScaledWalkProb,
      TransformConvergence.centeredScaledWalk_charFun, TransformConvergence.stepCharFun] using hp
  refine ⟨hW.alpha_mem, eventually_atTop.1 hbpos, (Q : Measure ℝ), inferInstance, hQL, ?_⟩
  intro f
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak f
  simpa [TransformConvergence.centeredScaledWalkProb, TransformConvergence.centeredScaledWalk_eq_map] using ht

end BGWLeaves.GeneralAInf.BlockStable
