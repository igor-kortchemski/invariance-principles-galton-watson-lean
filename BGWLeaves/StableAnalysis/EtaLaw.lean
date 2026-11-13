module

public import BGWLeaves.StableAnalysis.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis.EtaLaw

open BGW.StableTrees
open BGWLeaves.StableAnalysis

private lemma eta_event_mass (μ : PMF ℕ) :
    μ.toMeasure (Set.Ici 1) = 1 - (μ 0 : ℝ≥0∞) := by
  have hs : (Set.Ici 1 : Set ℕ) = ({0}ᶜ) := by
    ext k
    simp only [Set.mem_Ici, Set.mem_compl_iff, Set.mem_singleton_iff]
    omega
  rw [hs, prob_compl_eq_one_sub (measurableSet_singleton 0),
    PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)]

private lemma eta_event_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    μ.toMeasure (Set.Ici 1) ≠ 0 := by
  obtain ⟨j, hj, hjμ⟩ := hc.exists_two_le_ne_zero hne
  have hpos : 0 < μ.toMeasure {j} := by
    rw [PMF.toMeasure_apply_singleton μ j (measurableSet_singleton j)]
    exact_mod_cast (pos_iff_ne_zero.mpr hjμ)
  have hle : μ.toMeasure {j} ≤ μ.toMeasure (Set.Ici 1) :=
    measure_mono (by
      intro k hk
      simp only [Set.mem_singleton_iff] at hk
      subst k
      exact Set.mem_Ici.mpr (by omega))
  exact (ne_of_gt (lt_of_lt_of_le hpos hle))

private lemma eta_event_real (μ : PMF ℕ) :
    (μ.toMeasure (Set.Ici 1)).toReal = 1 - (μ 0).toReal := by
  rw [eta_event_mass]
  have hle : (μ 0 : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast μ.coe_le_one 0
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top]
  simp

private lemma eta_scale (μ : PMF ℕ) :
    ((μ.toMeasure (Set.Ici 1))⁻¹).toReal = (1 - (μ 0).toReal)⁻¹ := by
  rw [ENNReal.toReal_inv, eta_event_real]

private lemma eta_integral (μ : PMF ℕ) (f : ℤ → ℝ) :
    ∫ z, f z ∂etaLaw μ =
      ((μ.toMeasure (Set.Ici 1))⁻¹).toReal *
        ∫ k in Set.Ici 1, f ((k : ℤ) - 1) ∂μ.toMeasure := by
  rw [etaLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]

private lemma eta_integrable_sq {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (etaLaw μ) := by
  have hμ : Integrable ((fun z : ℤ => (z : ℝ) ^ 2) ∘
      (fun k : ℕ => (k : ℤ) - 1)) μ.toMeasure := by
    have hm := (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mp (by simpa only [stepLaw] using h)
    exact hm
  have hrestrict' : Integrable ((fun z : ℤ => (z : ℝ) ^ 2) ∘
      (fun k : ℕ => (k : ℤ) - 1)) (μ.toMeasure.restrict (Set.Ici 1)) := hμ.mono_measure
        Measure.restrict_le_self
  have hc0 : (μ.toMeasure (Set.Ici 1))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  have hctop : (μ.toMeasure (Set.Ici 1))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (eta_event_ne_zero hc hne)
  rw [etaLaw, integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  rw [ProbabilityTheory.cond]
  exact (integrable_smul_measure hc0 hctop).2 hrestrict'

private lemma eta_event_first_moment {μ : PMF ℕ} (hc : IsCritical μ) :
    ∫ k in Set.Ici 1, (((k : ℤ) - 1 : ℝ)) ∂μ.toMeasure = (μ 0).toReal := by
  let f : ℕ → ℝ := fun k => ((k : ℤ) - 1 : ℝ)
  have hf : Integrable f μ.toMeasure := by
    have hf' : Integrable (fun k : ℕ => (k : ℝ) - 1) μ.toMeasure :=
      (integrable_offspring hc).sub (integrable_const 1)
    simpa only [f, Int.cast_sub, Int.cast_natCast, Int.cast_one] using hf'
  have htotal : ∫ k, f k ∂μ.toMeasure = 0 := by
    calc
      ∫ k, f k ∂μ.toMeasure = ∫ k, (k : ℝ) - 1 ∂μ.toMeasure := by
        congr 1
      _ = 0 := by
        rw [integral_sub (integrable_offspring hc) (integrable_const 1),
          Scalar.offspring_integral_eq_one hc]
        simp
  have hzero : ∫ k in ({0} : Set ℕ), f k ∂μ.toMeasure = -(μ 0).toReal := by
    rw [integral_singleton]
    simp [f, measureReal_def, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)]
  have hcomp : (Set.Ici 1 : Set ℕ)ᶜ = ({0} : Set ℕ) := by
    ext k
    simp only [Set.mem_compl_iff, Set.mem_Ici, Set.mem_singleton_iff]
    omega
  have hsplit := integral_add_compl (μ := μ.toMeasure) (s := Set.Ici 1)
    measurableSet_Ici hf
  rw [hcomp, htotal, hzero] at hsplit
  have hres : ∫ k in Set.Ici 1, f k ∂μ.toMeasure = (μ 0).toReal := by linarith
  simpa [f] using hres

private lemma eta_event_second_moment {μ : PMF ℕ} (hc : IsCritical μ)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    ∫ k in Set.Ici 1, ((k : ℝ) - 1) ^ 2 ∂μ.toMeasure =
      variance (stepLaw μ) - (μ 0).toReal := by
  let f : ℕ → ℝ := (fun z : ℤ => (z : ℝ) ^ 2) ∘ (fun k : ℕ => (k : ℤ) - 1)
  have hμ : Integrable f μ.toMeasure := by
    have hm := (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mp (by simpa only [stepLaw] using h)
    change Integrable f μ.toMeasure
    exact hm
  have htotal : ∫ k, f k ∂μ.toMeasure = variance (stepLaw μ) := by
    have hmap : ∫ k, f k ∂μ.toMeasure = ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ := by
      rw [stepLaw, integral_map (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]
      simp [f, Function.comp_apply]
    have hvar : ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ = variance (stepLaw μ) := by
      rw [variance, mean_stepLaw hc]
      simp only [sub_zero]
    exact hmap.trans hvar
  have hzero : ∫ k in ({0} : Set ℕ), f k ∂μ.toMeasure = (μ 0).toReal := by
    rw [integral_singleton]
    simp [f, measureReal_def, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)]
  have hcomp : (Set.Ici 1 : Set ℕ)ᶜ = ({0} : Set ℕ) := by
    ext k
    simp only [Set.mem_compl_iff, Set.mem_Ici, Set.mem_singleton_iff]
    omega
  have hsplit := integral_add_compl (μ := μ.toMeasure) (s := Set.Ici 1)
    measurableSet_Ici hμ
  rw [hcomp, htotal, hzero] at hsplit
  have hres : ∫ k in Set.Ici 1, f k ∂μ.toMeasure =
      variance (stepLaw μ) - (μ 0).toReal := by linarith
  simpa [f, Function.comp_apply, Int.cast_sub, Int.cast_natCast, Int.cast_one] using hres

private lemma integrable_cast_of_integrable_sq {ν : Measure ℤ}
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Integrable (fun z : ℤ => (z : ℝ)) ν := by
  apply Integrable.mono' h (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with z
  simp only [Real.norm_eq_abs]
  have hbound : |(z : ℝ)| ≤ (z : ℝ) ^ 2 := by
    by_cases hz : z = 0
    · simp [hz]
    have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by
      have hz' : 0 < |z| := abs_pos.mpr hz
      have hz'' : 1 ≤ |z| := by omega
      exact_mod_cast hz''
    nlinarith [sq_abs (z : ℝ)]
  exact hbound

private lemma etaLaw_isProbability {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    IsProbabilityMeasure (etaLaw μ) := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ.toMeasure (Set.Ici 1)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (eta_event_ne_zero hc hne)
      (measure_ne_top _ _)
  change IsProbabilityMeasure (Measure.map _ _)
  infer_instance

private lemma eta_second_moment {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    ∫ z, (z : ℝ) ^ 2 ∂etaLaw μ =
      (variance (stepLaw μ) - (μ 0).toReal) / (1 - (μ 0).toReal) := by
  rw [eta_integral, eta_scale μ]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  rw [eta_event_second_moment hc h]
  have hp : 0 < (μ.toMeasure (Set.Ici 1)).toReal :=
    ENNReal.toReal_pos (eta_event_ne_zero hc hne) (measure_ne_top _ _)
  rw [eta_event_real] at hp
  have hden : 1 - (μ 0).toReal ≠ 0 := ne_of_gt hp
  field_simp [hden]

private lemma step_variance_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    0 < variance (stepLaw μ) := by
  have hvar : variance (stepLaw μ) = ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ := by
    rw [variance, mean_stepLaw hc]
    simp only [sub_zero]
  rw [hvar]
  have hnonneg : 0 ≤ ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ :=
    integral_nonneg fun z => sq_nonneg (z : ℝ)
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : ℤ => sq_nonneg (z : ℝ)) h).1 hzero.symm
  have hm := ae_iff.1 hae
  have hsub : ({-1} : Set ℤ) ⊆ {z : ℤ | ¬ (z : ℝ) ^ 2 = 0} := by
    intro z hz
    simp only [mem_singleton_iff] at hz
    subst z
    norm_num
  have heq : stepLaw μ {-1} = 0 := measure_mono_null hsub hm
  rw [stepLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)] at heq
  have hp : (fun j : ℕ => (j : ℤ) - 1) ⁻¹' ({-1} : Set ℤ) = {0} := by
    ext j
    simp only [mem_preimage, mem_singleton_iff, mem_singleton_iff]
    omega
  rw [hp, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] at heq
  exact (hc.apply_zero_ne_zero hne) heq

/-- `E[Y] = μ₀/(1-μ₀)` for `Y = K - 1` conditioned on `K ≥ 1`. -/
theorem mean_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (_hne : μ 1 ≠ 1) :
    mean (etaLaw μ) = (μ 0).toReal / (1 - (μ 0).toReal) := by
  rw [mean, eta_integral]
  rw [eta_scale μ]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  have hfirst := eta_event_first_moment hc
  have hfirst' : ∫ k in Set.Ici 1, ((k : ℝ) - 1) ∂μ.toMeasure = (μ 0).toReal := by
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one] using hfirst
  rw [hfirst']
  ring

/-- Finite second moment of `μ` gives a finite second moment for its conditioned excess law. -/
theorem integrable_sq_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (etaLaw μ) :=
  eta_integrable_sq hc hne h

/-- The variance of `Y` is `σ²/(1-μ₀) - μ₀/(1-μ₀)²`. -/
theorem variance_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    variance (etaLaw μ) =
      variance (stepLaw μ) / (1 - (μ 0).toReal) - (μ 0).toReal / (1 - (μ 0).toReal) ^ 2 := by
  let m : ℝ := (μ 0).toReal / (1 - (μ 0).toReal)
  have hηsq := eta_integrable_sq hc hne h
  have hηlin := integrable_cast_of_integrable_sq hηsq
  have hηmean : mean (etaLaw μ) = m := by
    simpa [m] using mean_etaLaw hc hne
  have hηsecond := eta_second_moment hc hne h
  let : IsProbabilityMeasure (etaLaw μ) := etaLaw_isProbability hc hne
  have hB : Integrable (fun z : ℤ => (2 * m) * (z : ℝ)) (etaLaw μ) :=
    hηlin.const_mul (2 * m)
  have hC : Integrable (fun _ : ℤ => m ^ 2) (etaLaw μ) := integrable_const _
  have hpoly : variance (etaLaw μ) =
      (∫ z, (z : ℝ) ^ 2 ∂etaLaw μ) -
        (2 * m) * (∫ z, (z : ℝ) ∂etaLaw μ) + m ^ 2 := by
    rw [variance, hηmean]
    calc
      ∫ z, ((z : ℝ) - m) ^ 2 ∂etaLaw μ =
          ∫ z, (z : ℝ) ^ 2 - (2 * m) * (z : ℝ) + m ^ 2 ∂etaLaw μ := by
            congr 1
            funext z
            ring
      _ = (∫ z, (z : ℝ) ^ 2 ∂etaLaw μ) -
          (2 * m) * (∫ z, (z : ℝ) ∂etaLaw μ) + m ^ 2 := by
            calc
              ∫ z, (z : ℝ) ^ 2 - (2 * m) * (z : ℝ) + m ^ 2 ∂etaLaw μ =
                  ∫ z, ((fun z : ℤ => (z : ℝ) ^ 2) -
                    (fun z : ℤ => (2 * m) * (z : ℝ))) z + (fun _ : ℤ => m ^ 2) z
                    ∂etaLaw μ := by
                      apply integral_congr_ae
                      exact Eventually.of_forall fun z => by
                        simp only [Pi.sub_apply]
              _ = (∫ z, (z : ℝ) ^ 2 ∂etaLaw μ) -
                  (2 * m) * (∫ z, (z : ℝ) ∂etaLaw μ) + m ^ 2 := by
                    have hadd := integral_add (hηsq.sub hB) hC
                    have hsub := integral_sub hηsq hB
                    have hsub' :
                        (∫ z, ((fun z : ℤ => (z : ℝ) ^ 2) -
                          (fun z : ℤ => (2 * m) * (z : ℝ))) z ∂etaLaw μ) =
                        (∫ z, (z : ℝ) ^ 2 ∂etaLaw μ) -
                          ∫ z, (2 * m) * (z : ℝ) ∂etaLaw μ := by
                      simpa only [Pi.sub_apply] using hsub
                    calc
                      _ = (∫ z, ((fun z : ℤ => (z : ℝ) ^ 2) -
                          (fun z : ℤ => (2 * m) * (z : ℝ))) z ∂etaLaw μ) +
                          ∫ z, (fun _ : ℤ => m ^ 2) z ∂etaLaw μ := by
                            simpa only [Pi.add_apply, Pi.sub_apply] using hadd
                      _ = ((∫ z, (z : ℝ) ^ 2 ∂etaLaw μ) -
                          ∫ z, (2 * m) * (z : ℝ) ∂etaLaw μ) +
                          ∫ z, (fun _ : ℤ => m ^ 2) z ∂etaLaw μ := by
                            rw [hsub']
                      _ = (∫ z, (z : ℝ) ^ 2 ∂etaLaw μ) -
                          (2 * m) * (∫ z, (z : ℝ) ∂etaLaw μ) + m ^ 2 := by
                            rw [integral_const_mul, integral_const]
                            simp [smul_eq_mul]
  rw [hpoly, ← mean, hηmean, hηsecond]
  have hp : 0 < (μ.toMeasure (Set.Ici 1)).toReal :=
    ENNReal.toReal_pos (eta_event_ne_zero hc hne) (measure_ne_top _ _)
  rw [eta_event_real] at hp
  have hden : 1 - (μ 0).toReal ≠ 0 := ne_of_gt hp
  dsimp [m]
  field_simp [hden]
  ring

/-- The finite-variance norming ratio at the index `⌊n/μ₀⌋`. -/
theorem finiteVariance_norming_ratio_eta {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) 2 n / norming (stepLaw μ) 2 ⌊n / (μ 0).toReal⌋₊)
      atTop (𝓝 (Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) /
        Real.sqrt (variance (stepLaw μ)))) := by
  let m : ℝ := (μ 0).toReal
  let x : ℕ → ℝ := fun n => (n : ℝ) / m
  have hm : 0 < m := by
    dsimp [m]
    exact ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hx : Tendsto x atTop atTop := by
    dsimp [x]
    exact tendsto_natCast_atTop_atTop.atTop_div_const hm
  have hfloor : Tendsto
      (fun n : ℕ => (⌊(n : ℝ) / m⌋₊ : ℝ) / x n) atTop (𝓝 1) := by
    change Tendsto ((fun y : ℝ => (⌊y⌋₊ : ℝ) / y) ∘ x) atTop (𝓝 1)
    exact (tendsto_nat_floor_div_atTop (R := ℝ)).comp hx
  have hfloor_pos : ∀ᶠ n : ℕ in atTop, 0 < ⌊(n : ℝ) / m⌋₊ := by
    filter_upwards [hx.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    exact Nat.floor_pos.mpr hn
  have hsqrt_floor : Tendsto
      (fun n : ℕ => Real.sqrt (⌊(n : ℝ) / m⌋₊ : ℝ) / Real.sqrt (x n)) atTop (𝓝 1) := by
    have h := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hfloor
    have hEq : (fun n : ℕ => Real.sqrt ((⌊(n : ℝ) / m⌋₊ : ℝ) / x n)) =ᶠ[atTop]
        (fun n => Real.sqrt (⌊(n : ℝ) / m⌋₊ : ℝ) / Real.sqrt (x n)) :=
      Eventually.of_forall fun n => Real.sqrt_div
        (by positivity : 0 ≤ (⌊(n : ℝ) / m⌋₊ : ℝ)) (x n)
    simpa using Tendsto.congr' hEq h
  let c : ℝ := Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ))
  have hstepvar : 0 < variance (stepLaw μ) := step_variance_pos hc hne h
  have hsqrtvar : Real.sqrt (variance (stepLaw μ)) ≠ 0 :=
    (Real.sqrt_pos.2 hstepvar).ne'
  have hdiv : Tendsto
      (fun n : ℕ => Real.sqrt m /
        (Real.sqrt (⌊(n : ℝ) / m⌋₊ : ℝ) / Real.sqrt (x n))) atTop
      (𝓝 (Real.sqrt m)) := by
    convert tendsto_const_nhds.div hsqrt_floor (by norm_num : (1 : ℝ) ≠ 0) using 1; simp
  have hlim : Tendsto
      (fun n : ℕ => c * (Real.sqrt m /
        (Real.sqrt (⌊(n : ℝ) / m⌋₊ : ℝ) / Real.sqrt (x n)))) atTop
      (𝓝 (c * Real.sqrt m)) :=
    by convert tendsto_const_nhds.mul hdiv using 1
  have hηsq := eta_integrable_sq hc hne h
  have hratio : (fun n : ℕ => norming (etaLaw μ) 2 n /
      norming (stepLaw μ) 2 ⌊(n : ℝ) / m⌋₊) =ᶠ[atTop]
      (fun n : ℕ => c * (Real.sqrt m /
        (Real.sqrt (⌊(n : ℝ) / m⌋₊ : ℝ) / Real.sqrt (x n)))) := by
    filter_upwards [hfloor_pos] with n hn
    have hq : 0 < (⌊(n : ℝ) / m⌋₊ : ℝ) := by exact_mod_cast hn
    have hxpos : 0 < x n := by
      dsimp [x]
      exact lt_of_lt_of_le zero_lt_one (Nat.floor_pos.mp hn)
    have hqdiv : Real.sqrt ((⌊(n : ℝ) / m⌋₊ : ℝ) / 2) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      positivity
    have hsqrt_ratio : Real.sqrt ((n : ℝ) / 2) /
        Real.sqrt ((⌊(n : ℝ) / m⌋₊ : ℝ) / 2) =
        Real.sqrt m /
          (Real.sqrt (⌊(n : ℝ) / m⌋₊ : ℝ) / Real.sqrt (x n)) := by
      have hquot : (n : ℝ) / (⌊(n : ℝ) / m⌋₊ : ℝ) =
          m / ((⌊(n : ℝ) / m⌋₊ : ℝ) / x n) := by
        by_cases hq0 : (⌊(n : ℝ) / m⌋₊ : ℝ) = 0
        · simp [hq0]
        · have hnval : (n : ℝ) = m * x n := by
            dsimp [x]
            field_simp [hm.ne']
          rw [hnval]
          field_simp [hm.ne', hq0, hxpos.ne']
      calc
        _ = Real.sqrt ((n : ℝ) / (⌊(n : ℝ) / m⌋₊ : ℝ)) := by
          rw [← Real.sqrt_div (by positivity : 0 ≤ (n : ℝ) / 2)]
          congr 1
          field_simp [hq.ne']
        _ = Real.sqrt (m / ((⌊(n : ℝ) / m⌋₊ : ℝ) / x n)) := by rw [hquot]
        _ = Real.sqrt m / Real.sqrt ((⌊(n : ℝ) / m⌋₊ : ℝ) / x n) :=
          Real.sqrt_div hm.le _
        _ = Real.sqrt m /
              (Real.sqrt (⌊(n : ℝ) / m⌋₊ : ℝ) / Real.sqrt (x n)) := by
          rw [Real.sqrt_div (by positivity : 0 ≤ (⌊(n : ℝ) / m⌋₊ : ℝ))]
    rw [norming_of_integrable_sq hηsq 2 n,
      norming_of_integrable_sq h 2 ⌊(n : ℝ) / m⌋₊]
    dsimp [c]
    rw [← hsqrt_ratio]
    field_simp [hsqrtvar, hqdiv]
  have htarget : c * Real.sqrt m =
      Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) /
        Real.sqrt (variance (stepLaw μ)) := by
    dsimp [c, m]
    ring
  simpa only [htarget] using Tendsto.congr' hratio.symm hlim

end BGWLeaves.StableAnalysis.EtaLaw

end
