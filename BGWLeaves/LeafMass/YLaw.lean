module

public import BGWLeaves.LeafMass.Defs
public import BGWLeaves.StableAnalysis.EtaTransfer
public import BGWLeaves.StableAnalysis.CanonicalAttraction
public import BGWLeaves.StableAnalysis.DomainCriterion
public import BGWLeaves.StableAnalysis.LemHhp
public import BGWLeaves.StableAnalysis.Consequences

/-!
# The conditioned excess law and its local limit theorem

The stable index is transferred by the exact tail and truncated-moment identities.
Finite variance uses the general integer-law CLT and two distinct positive offspring
atoms. The lattice LLT is proved by affine rescaling of the convolution powers;
the rescaled norming is `a / d`, which accounts for the lattice factor `d`.
-/

@[expose] public section

namespace BGWLeaves.LeafMass.YLaw

open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-- Integrability survives conditioning on positive offspring and translation. -/
theorem integrable_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    Integrable (fun z : ℤ => (z : ℝ)) (etaLaw μ) := by
  have hμ : Integrable ((fun z : ℤ => (z : ℝ)) ∘
      (fun k : ℕ => (k : ℤ) - 1)) μ.toMeasure := by
    have hf : Integrable (fun k : ℕ => (k : ℝ) - 1) μ.toMeasure :=
      (integrable_offspring hc).sub (integrable_const 1)
    simpa only [Function.comp_def, Int.cast_sub, Int.cast_natCast, Int.cast_one] using hf
  rw [etaLaw, integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable, ProbabilityTheory.cond]
  exact (integrable_smul_measure
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (EtaTransfer.offspring_pos_ne_zero hc hne))).2
    (hμ.mono_measure Measure.restrict_le_self)

/-- The atom corresponding to a positive offspring count. -/
theorem etaLaw_real_singleton_of_nat (μ : PMF ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (etaLaw μ).real {((k : ℤ) - 1)} = (μ k).toReal / (1 - (μ 0).toReal) := by
  have hs : Set.Ici 1 ∩ (fun j : ℕ => (j : ℤ) - 1) ⁻¹' {((k : ℤ) - 1)} = {k} := by
    ext j
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, hj⟩; omega
    · rintro rfl; exact ⟨hk, rfl⟩
  rw [measureReal_def, EtaTransfer.etaLaw_apply, hs, ENNReal.toReal_mul,
    ENNReal.toReal_inv, EtaTransfer.offspring_pos_real,
    PMF.toMeasure_apply_singleton μ k (measurableSet_singleton k), inv_mul_eq_div]

/-- The explicit law of `Y` at an arbitrary integer. -/
theorem etaLaw_real_singleton (μ : PMF ℕ) (z : ℤ) :
    (etaLaw μ).real {z} =
      if 0 ≤ z then (μ (z + 1).toNat).toReal / (1 - (μ 0).toReal) else 0 := by
  by_cases hz : 0 ≤ z
  · rw [ite_eq_left hz]
    have hk : 1 ≤ (z + 1).toNat := by omega
    have heq : z = (((z + 1).toNat : ℕ) : ℤ) - 1 := by omega
    conv_lhs => rw [heq]
    exact etaLaw_real_singleton_of_nat μ hk
  · rw [ite_eq_right hz, measureReal_def]
    have hm : etaLaw μ {z} = 0 := measure_mono_null
      (by simpa using (show z < 0 from lt_of_not_ge hz)) (EtaTransfer.etaLaw_lt_zero μ)
    simp [hm]

/-- Every positive offspring atom remains a nonzero atom after conditioning. -/
theorem etaLaw_atom_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (hμ : μ k ≠ 0) : etaLaw μ {((k : ℤ) - 1)} ≠ 0 := by
  have hp : 0 < (etaLaw μ).real {((k : ℤ) - 1)} := by
    rw [etaLaw_real_singleton_of_nat μ hk]
    exact div_pos (ENNReal.toReal_pos hμ (μ.apply_ne_top k))
      (EtaTransfer.one_sub_apply_zero_pos hc hne)
  intro hz
  simp [measureReal_def, hz] at hp

/-- Two distinct positive offspring atoms give strictly positive variance for `Y`. -/
theorem variance_etaLaw_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hS : ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (etaLaw μ)) :
    0 < variance (etaLaw μ) := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hL2 := (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).2 hsq
  have hi : Integrable (fun z : ℤ => ((z : ℝ) - mean (etaLaw μ)) ^ 2) (etaLaw μ) :=
    (hL2.sub (memLp_const _)).integrable_sq
  have hn : 0 ≤ variance (etaLaw μ) := integral_nonneg fun _ => sq_nonneg _
  apply lt_of_le_of_ne hn
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg (fun z : ℤ => sq_nonneg ((z : ℝ) - mean (etaLaw μ))) hi).1 hz.symm
  obtain ⟨k₁, k₂, hk₁, hk₂, hμ₁, hμ₂⟩ := hS
  have h₁ := (ae_iff_of_countable.1 he) _ (etaLaw_atom_ne_zero hc hne hk₁ hμ₁)
  have h₂ := (ae_iff_of_countable.1 he) _ (etaLaw_atom_ne_zero hc hne (by omega) hμ₂)
  simp only [Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero, Int.cast_sub, Int.cast_natCast,
    Int.cast_one] at h₁ h₂
  have : (k₁ : ℝ) < k₂ := by exact_mod_cast hk₂
  linarith

/-- Conditioning away the atom at `-1` preserves the stable index. -/
theorem etaLaw_isStableAttracted {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hS : ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0)
    (hDA : ∃ a, StableDomain μ θ a) :
    ∃ b : ℕ → ℝ, IsStableAttracted (etaLaw μ) θ (mean (etaLaw μ)) b := by
  have := isProbabilityMeasure_stepLaw μ
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  obtain ⟨a, ha⟩ := hDA
  have hb : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) a := by
    rw [mean_stepLaw hc]
    exact stableDomain_isStableAttracted ha
  refine ⟨norming (etaLaw μ) θ, ?_⟩
  by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
  · have hθ := DomainCriterion.index_eq_two_of_integrable_sq hb (integrable_stepLaw hc) hfin
    subst θ
    exact CanonicalAttraction.isStableAttracted_of_finiteVariance (integrable_etaLaw hc hne)
      (integrable_sq_etaLaw hc hne hfin)
      (variance_etaLaw_pos hc hne hS (integrable_sq_etaLaw hc hne hfin))
  · by_cases hθ : θ < 2
    · have hT := DomainCriterion.rightTail_regularlyVarying hb (stepLaw_lt_neg_one μ)
        (integrable_stepLaw hc) hfin hθ
      apply CanonicalAttraction.isStableAttracted_of_regVary_tail
        (EtaTransfer.etaLaw_lt_neg_one μ) (integrable_etaLaw hc hne) hb.alpha_mem.1 hθ
      intro c hc'
      have hq := (EtaTransfer.one_sub_apply_zero_pos hc hne).ne'
      apply (hT c hc').congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [EtaTransfer.etaLaw_tail_eq μ hx,
        EtaTransfer.etaLaw_tail_eq μ (mul_nonneg hc'.le hx), div_div_div_cancel_right₀ hq]
    · have hθeq : θ = 2 := le_antisymm hb.alpha_mem.2 (le_of_not_gt hθ)
      subst θ
      obtain ⟨hK, hKinf⟩ := DomainCriterion.truncSecondMoment_slowlyVarying_unbounded hb
        (integrable_stepLaw hc) hfin
      exact CanonicalAttraction.isStableAttracted_of_slowlyVarying_moment
        (EtaTransfer.etaLaw_lt_neg_one μ) (integrable_etaLaw hc hne)
        (LemHhp.slowlyVarying_K_eta hc hne hK hKinf) (LemHhp.tendsto_K_eta hc hne hKinf)

/-- Canonical norming and its slowly varying factor for `Y`. -/
theorem etaLaw_norming {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hS : ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0)
    (hDA : ∃ a, StableDomain μ θ a) :
    IsStableAttracted (etaLaw μ) θ (mean (etaLaw μ)) (norming (etaLaw μ) θ) ∧
      Monotone (norming (etaLaw μ) θ) ∧
      SlowlyVarying (fun x : ℝ => norming (etaLaw μ) θ ⌊x⌋₊ / x ^ (1 / θ)) := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have h := etaLaw_isStableAttracted hc hne hS hDA
  exact ⟨locallimit_i _ (EtaTransfer.etaLaw_lt_neg_one μ) (integrable_etaLaw hc hne) h,
    locallimit_ii _ (EtaTransfer.etaLaw_lt_neg_one μ) (integrable_etaLaw hc hne) h⟩

/-- The centered uniform local limit theorem for the non-lattice law of `Y`. -/
theorem llt_etaLaw_nonlattice {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hS : ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0)
    (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming (etaLaw μ) θ n * intWalkProb (etaLaw μ) n k -
          Scalar.stableDensity θ
            (((k : ℝ) - n * ((μ 0).toReal / (1 - (μ 0).toReal))) / norming (etaLaw μ) θ n)| ≤ ε := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  simpa only [mean_etaLaw hc hne] using locallimit_iii (etaLaw μ)
    (EtaTransfer.etaLaw_lt_neg_one μ) (integrable_etaLaw hc hne) hnl
    (etaLaw_isStableAttracted hc hne hS hDA) hε

private instance walk_probability (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n).conv ν))

/-- Affine maps of integer increments commute with convolution powers, with the
translation multiplied by the number of increments. -/
theorem intWalk_map_affine (ρ : Measure ℤ) [IsProbabilityMeasure ρ] (d r : ℤ) (n : ℕ) :
    intWalk (ρ.map (fun z => d * z + r)) n =
      (intWalk ρ n).map (fun z => d * z + n * r) := by
  induction n with
  | zero => simp [intWalk]
  | succ n ih =>
    rw [intWalk, ih]
    simp only [intWalk]
    unfold Measure.conv
    rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, Nat.cast_add, Nat.cast_one]
    ring

/-- A point has nonzero `etaLaw` mass precisely when it comes from positive offspring. -/
theorem etaLaw_support {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (z : ℤ) :
    etaLaw μ {z} ≠ 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ μ k ≠ 0 ∧ z = (k : ℤ) - 1 := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  constructor
  · intro hz
    have hnonneg : 0 ≤ z := by
      by_contra h
      exact hz (measure_mono_null (by simpa using (show z < 0 from lt_of_not_ge h))
        (EtaTransfer.etaLaw_lt_zero μ))
    let k := z.toNat + 1
    have hk : z = (k : ℤ) - 1 := by dsimp [k]; omega
    refine ⟨k, by omega, ?_, hk⟩
    intro hμ
    have hreal : (etaLaw μ).real {z} = 0 := by
      rw [hk, etaLaw_real_singleton_of_nat μ (by omega), hμ]; simp
    exact hz ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 hreal)
  · rintro ⟨k, hk, hμ, rfl⟩
    exact etaLaw_atom_ne_zero hc hne hk hμ

/-- Lattice support of `etaLaw` is exactly lattice support of positive offspring,
with residue translated by one. -/
theorem etaLaw_ae_dvd_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (d : ℕ) (r : ℤ) :
    (∀ᵐ z ∂etaLaw μ, (d : ℤ) ∣ z - r) ↔
      ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d : ℤ) ∣ (k : ℤ) - (r + 1) := by
  rw [ae_iff_of_countable]
  constructor
  · intro h k hk hk0
    simpa only [sub_sub, add_comm r 1] using
      h _ (etaLaw_atom_ne_zero hc hne (by omega) hk)
  · intro h z hz
    obtain ⟨k, hk, hμ, rfl⟩ := (etaLaw_support hc hne z).1 hz
    simpa only [sub_sub, add_comm r 1] using h k hμ (by omega)

/-- A lattice-supported law is the affine image of its integer rescaling. -/
theorem map_rescale_affine (ν : Measure ℤ) (d : ℕ) (r : ℤ)
    (hsupp : ∀ᵐ z ∂ν, (d : ℤ) ∣ z - r) :
    (ν.map (fun z => (z - r) / (d : ℤ))).map (fun z => (d : ℤ) * z + r) = ν := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    _ = ν.map id := Measure.map_congr (hsupp.mono fun z hz => by
      dsimp only [Function.comp_def, id_eq]
      rw [Int.mul_ediv_cancel' hz]
      ring)
    _ = ν := Measure.map_id

/-- Centering and scaling compensate exactly for an affine change of increments. -/
theorem isStableAttracted_of_affine {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    {d : ℕ} (hd : 0 < d) (r : ℤ) {θ m : ℝ} {a : ℕ → ℝ}
    (h : IsStableAttracted (ρ.map (fun z => (d : ℤ) * z + r)) θ m a) :
    IsStableAttracted ρ θ ((m - r) / d) (fun n => a n / d) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  refine ⟨h.alpha_mem, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := h.pos
    exact ⟨N, fun n hn => div_pos (hN n hn) hdR⟩
  · obtain ⟨X, hX, hLap, hlim⟩ := h.converges
    refine ⟨X, hX, hLap, fun f => ?_⟩
    apply (hlim f).congr
    intro n
    rw [intWalk_map_affine, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 2
    funext z
    dsimp only [Function.comp_def]
    push_cast
    field_simp
    ring

/-- The mean of an affine image. -/
theorem mean_map_affine (ρ : Measure ℤ) [IsProbabilityMeasure ρ]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ρ) (d r : ℤ) :
    mean (ρ.map (fun z => d * z + r)) = (d : ℝ) * mean ρ + r := by
  rw [mean, integral_map (by fun_prop) (by fun_prop)]
  simp only [Int.cast_add, Int.cast_mul]
  rw [integral_add (hint.const_mul _) (integrable_const _), integral_const_mul]
  simp [mean]

/-- The abstract lattice LLT, stated for an affine image of a span-one law. -/
theorem llt_lattice_affine (ρ : Measure ℤ) [IsProbabilityMeasure ρ]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ρ) (hnl : ¬ IsLatticeLaw ρ)
    {d : ℕ} (hd : 0 < d) (r : ℤ) {θ : ℝ} {a : ℕ → ℝ}
    (hmono : Monotone a)
    (h : IsStableAttracted (ρ.map (fun z => (d : ℤ) * z + r)) θ
      (mean (ρ.map (fun z => (d : ℤ) * z + r))) a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |a n * intWalkProb (ρ.map (fun z => (d : ℤ) * z + r)) n k -
        (if (d : ℤ) ∣ k - n * r then (d : ℝ) * Scalar.stableDensity θ
          (((k : ℝ) - n * mean (ρ.map (fun z => (d : ℤ) * z + r))) / a n)
        else 0)| ≤ ε := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmean := mean_map_affine ρ hint (d : ℤ) r
  have h' := isStableAttracted_of_affine hd r h
  rw [hmean] at h'
  have hm : (((d : ℤ) : ℝ) * mean ρ + r - r) / d = mean ρ := by
    push_cast; field_simp; ring
  rw [hm] at h'
  obtain ⟨N, hN⟩ := llt_abstract ρ hint hnl
    (fun i j hij => div_le_div_of_nonneg_right (hmono hij) hdR.le) h'
    (div_pos hε hdR)
  refine ⟨N, fun n hn k => ?_⟩
  rw [intWalkProb, intWalk_map_affine, measureReal_def,
    Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  by_cases hk : (d : ℤ) ∣ k - n * r
  · rw [ite_eq_left hk]
    let j : ℤ := (k - n * r) / d
    have hj : (d : ℤ) * j + n * r = k := by
      dsimp [j]; rw [Int.mul_ediv_cancel' hk]; ring
    have hpre : (fun z : ℤ => (d : ℤ) * z + n * r) ⁻¹' {k} = {j} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        exact mul_left_cancel₀ hdZ (by linear_combination hz - hj)
      · rintro rfl; exact hj
    rw [hpre]
    have harg : ((j : ℝ) - n * mean ρ) / (a n / d) =
        ((k : ℝ) - n * mean (ρ.map (fun z => (d : ℤ) * z + r))) / a n := by
      rw [hmean]
      have hjR := congrArg (fun z : ℤ => (z : ℝ)) hj
      push_cast at hjR ⊢
      rw [div_div_eq_mul_div]
      congr 1
      nlinarith [hjR]
    have hb := mul_le_mul_of_nonneg_left (hN n hn j) hdR.le
    rw [harg, ← abs_of_pos hdR, ← abs_mul] at hb
    simp only [abs_of_pos hdR] at hb
    simp only [intWalkProb, measureReal_def] at hb
    convert hb using 1 <;> field_simp [hdR.ne']
  · rw [ite_eq_right hk]
    have hpre : (fun z : ℤ => (d : ℤ) * z + n * r) ⁻¹' {k} = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hz
      apply hk
      exact ⟨z, by linear_combination -hz⟩
    simp [hpre, hε.le]

/-- Uniform lattice LLT at the maximal span, obtained by integer affine rescaling. -/
theorem llt_lattice_abstract (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {d : ℕ} (hspan : HasSpan ν d) (r : ℤ)
    (hsupp : ∀ᵐ z ∂ν, (d : ℤ) ∣ z - r)
    {θ : ℝ} {a : ℕ → ℝ} (hmono : Monotone a)
    (h : IsStableAttracted ν θ (mean ν) a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |a n * intWalkProb ν n k -
        (if (d : ℤ) ∣ k - n * r then (d : ℝ) * Scalar.stableDensity θ
          (((k : ℝ) - n * mean ν) / a n) else 0)| ≤ ε := by
  let ρ := ν.map (fun z => (z - r) / (d : ℤ))
  have heq : ρ.map (fun z => (d : ℤ) * z + r) = ν := map_rescale_affine ν d r hsupp
  have hd : 0 < (d : ℝ) := by exact_mod_cast hspan.1
  have hintρ : Integrable (fun z : ℤ => (z : ℝ)) ρ := by
    have hc : Integrable (fun z : ℤ => (((d : ℤ) * z + r : ℤ) : ℝ)) ρ := by
      exact ((integrable_map_measure (by fun_prop) (by fun_prop)).1 (heq ▸ hint))
    have hc' : Integrable (fun z : ℤ => (d : ℝ) * z + r) ρ := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hc
    convert (hc'.sub (integrable_const (r : ℝ))).div_const (d : ℝ) using 1
    funext z
    dsimp only [Pi.sub_apply]
    field_simp
    ring
  have hnl : ¬ IsLatticeLaw ρ := by
    rintro ⟨s, e, he, hres⟩
    have hde : d * e ∣ d := hspan.2.2 (d * e) ⟨(d : ℤ) * s + r, by
      rw [← heq, ae_map_iff (by fun_prop) MeasurableSet.of_discrete]
      filter_upwards [hres] with z hz
      have hh := mul_dvd_mul_left (d : ℤ) hz
      convert hh using 1 <;> push_cast <;> ring⟩
    have hle := Nat.le_of_dvd hspan.1 hde
    nlinarith [hspan.1]
  have hh := llt_lattice_affine ρ hintρ hnl hspan.1 r hmono (heq.symm ▸ h) hε
  simpa only [heq] using hh

/-- A maximal positive support span excludes a single positive offspring atom. -/
theorem isSuppSpan_two_points {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0 := by
  obtain ⟨j, hj, hjμ⟩ := hc.exists_two_le_ne_zero hne
  by_contra hS
  have heq : ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → k = j := by
    intro k hk hk0
    by_contra hkj
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · exact hS ⟨k, j, by omega, hlt, hk, hjμ⟩
    · exact hS ⟨j, k, by omega, hgt, hjμ, hk⟩
  have hbad := hdb.2.2.1 (d + 1) (by omega) ⟨j, fun k hk hk0 => by
    rw [heq k hk hk0]; simp⟩
  omega

/-- The maximal offspring-support span is also the span of the conditioned excess law. -/
theorem hasSpan_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {d b : ℕ} (hdb : IsSuppSpan μ d b) : HasSpan (etaLaw μ) d := by
  have hd1 := hdb.1
  have hsupp : ∀ᵐ z ∂etaLaw μ, (d : ℤ) ∣ z - ((b : ℤ) - 1) := by
    apply (etaLaw_ae_dvd_iff hc hne d _).2
    simpa only [sub_add_cancel] using hdb.2.1
  refine ⟨by omega, ⟨(b : ℤ) - 1, hsupp⟩, ?_⟩
  intro e he
  obtain ⟨r, hr⟩ := he
  have hr' := (etaLaw_ae_dvd_iff hc hne e r).1 hr
  obtain ⟨k₁, k₂, hk₁, hk₂, hμ₁, hμ₂⟩ := isSuppSpan_two_points hc hne hdb
  have hepos : 0 < e := by
    by_contra he0
    have heq : e = 0 := by omega
    have h₁ := hr' k₁ hμ₁ (by omega)
    have h₂ := hr' k₂ hμ₂ (by omega)
    simp only [heq, Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at h₁ h₂
    omega
  have hlpos : 1 ≤ Nat.lcm d e := Nat.lcm_pos (by omega) hepos
  have hlmax : Nat.lcm d e ≤ d := hdb.2.2.1 _ hlpos ⟨k₁, by
    intro k hk hk0
    have hD := dvd_sub (hdb.2.1 k hk hk0) (hdb.2.1 k₁ hμ₁ (by omega))
    have hE := dvd_sub (hr' k hk hk0) (hr' k₁ hμ₁ (by omega))
    simp only [sub_sub_sub_cancel_right] at hD hE
    have hh := Int.coe_lcm_dvd hD hE
    simpa only [Int.lcm_def, Int.natAbs_natCast, sub_sub_sub_cancel_right] using hh⟩
  have hle : d ≤ Nat.lcm d e := Nat.le_of_dvd (by omega) (Nat.dvd_lcm_left d e)
  have heq : Nat.lcm d e = d := le_antisymm hlmax hle
  simpa only [heq] using Nat.dvd_lcm_right d e

/-- Lattice and non-lattice descriptions agree for the offspring and excess laws. -/
theorem etaLaw_nonLattice_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    (¬ IsLatticeLaw (etaLaw μ)) ↔ d = 1 := by
  have hspan := hasSpan_etaLaw hc hne hdb
  have hd1 := hdb.1
  constructor
  · intro hnl
    by_contra hd
    exact hnl ⟨(b : ℤ) - 1, d, by omega,
      (etaLaw_ae_dvd_iff hc hne d _).2 (by simpa only [sub_add_cancel] using hdb.2.1)⟩
  · intro hd ⟨r, e, he, hr⟩
    have he' := hspan.2.2 e ⟨r, hr⟩
    rw [hd] at he'
    have := Nat.le_of_dvd (by norm_num : 0 < 1) he'
    omega

/-- The lattice local limit theorem for `Y`, including the factor equal to its span. -/
theorem llt_etaLaw_lattice {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {d b : ℕ} (hdb : IsSuppSpan μ d b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming (etaLaw μ) θ n * intWalkProb (etaLaw μ) n k -
          (if (d : ℤ) ∣ k - n * ((b : ℤ) - 1) then
            (d : ℝ) * Scalar.stableDensity θ
              (((k : ℝ) - n * ((μ 0).toReal / (1 - (μ 0).toReal))) / norming (etaLaw μ) θ n)
          else 0)| ≤ ε := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  obtain ⟨hattr, hmono, _⟩ := etaLaw_norming hc hne (isSuppSpan_two_points hc hne hdb) hDA
  simpa only [mean_etaLaw hc hne] using llt_lattice_abstract (etaLaw μ)
    (integrable_etaLaw hc hne) (hasSpan_etaLaw hc hne hdb) ((b : ℤ) - 1)
    ((etaLaw_ae_dvd_iff hc hne d _).2 (by simpa only [sub_add_cancel] using hdb.2.1))
    hmono hattr hε

/-- Periodicity of the offspring law forces the excess law onto a proper lattice. -/
theorem etaLaw_isLattice_of_periodic {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hper : ¬ Aperiodic μ) : IsLatticeLaw (etaLaw μ) := by
  have hdpos := Scalar.latticeSpan_pos hc hne
  have hdne : Scalar.latticeSpan μ ≠ 1 := by
    intro hd
    exact hper ((aperiodic_iff_latticeSpan_eq_one hc hne).2 hd)
  refine ⟨-1, Scalar.latticeSpan μ, by omega, ?_⟩
  apply (etaLaw_ae_dvd_iff hc hne _ _).2
  intro k hk _
  simpa using Scalar.latticeSpan_dvd_of_ne_zero hc hne hk

/-- In the infinite-variance Gaussian case the slowly varying excess norming diverges. -/
theorem etaLaw_gauss_hprime_tendsto {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ 2 a)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) 2 n / Real.sqrt n) atTop atTop := by
  have := isProbabilityMeasure_stepLaw μ
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  obtain ⟨a, ha⟩ := hDA
  have hb : IsStableAttracted (stepLaw μ) 2 (mean (stepLaw μ)) a := by
    rw [mean_stepLaw hc]
    exact stableDomain_isStableAttracted ha
  obtain ⟨hK, hKinf⟩ := DomainCriterion.truncSecondMoment_slowlyVarying_unbounded hb
    (integrable_stepLaw hc) hinf
  have hηK := LemHhp.slowlyVarying_K_eta hc hne hK hKinf
  have hηinf := LemHhp.tendsto_K_eta hc hne hKinf
  have hηsq := GaussianBranch.not_integrable_of_tendsto_atTop hηinf
  have hlim := Real.tendsto_sqrt_atTop.comp
    ((GaussianBranch.truncSecondMoment_gaussQuantile_tendsto_atTop hηK hηinf).atTop_div_const
      (by norm_num : (0 : ℝ) < 2))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  simp only [norming, ite_eq_right hηsq, lt_self_iff_false, ite_false]
  rw [show (n : ℝ) * truncSecondMoment (etaLaw μ) (gaussQuantile (etaLaw μ) n) / 2 =
    (n : ℝ) * (truncSecondMoment (etaLaw μ) (gaussQuantile (etaLaw μ) n) / 2) by ring,
    Real.sqrt_mul hnR.le, mul_div_cancel_left₀ _ hsn]
  rfl

end BGWLeaves.LeafMass.YLaw
