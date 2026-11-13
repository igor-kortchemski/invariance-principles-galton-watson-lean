module

public import BGWLeaves.LeafLimitsGeneral.Residue
public import BGWLeaves.LeafLimits.Bridge

/-! Lattice bridge-prefix densities. The moving-path proof is adapted from
`LeafLimits.Bridge`, with the endpoint projected to the bridge-clock residue. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.BridgeLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.LeafLimits.Bridge
open scoped ENNReal NNReal Topology

/-- Signed local convergence on the permitted moving residue; the estimate is
uniform on all endpoints, so no separate bounded-window hypothesis is required. -/
theorem tendsto_scaled_chi {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {j : ℕ → ℤ} {x : ℝ}
    (hx : Tendsto (fun k => (j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal)) atTop (𝓝 x))
    (hres : ∀ᶠ k in atTop, (arithFactor μ {0} : ℤ) ∣ (q k : ℤ) - 1 - j k) :
    Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) (j k)).toReal)
      atTop (𝓝 ((arithFactor μ {0} : ℝ) * Scalar.stableDensity θ (-x))) := by
  obtain ⟨a, ha⟩ := hDA
  have hd := (((Scalar.continuous_stableDensity ha.alpha_mem).tendsto (-x)).comp hx.neg).const_mul
    (arithFactor μ {0} : ℝ)
  have he : Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) (j k)).toReal -
      (arithFactor μ {0} : ℝ) * Scalar.stableDensity θ
        (-((j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal)))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := LocalLattice.lem_technic3 hc hne ⟨a, ha⟩ (half_pos hε)
    filter_upwards [hqtop.eventually_ge_atTop N, hres] with k hk hr
    rw [Real.dist_eq, sub_zero]
    have hh := hN (q k) hk (j k)
    rw [ite_eq_left hr] at hh
    exact hh.trans_lt (half_lt_self hε)
  simpa only [Function.comp_def, zero_add, sub_add_cancel] using he.add hd

/-- The residue is `n-k-1`, because the walk clock has completed its `k`-th leaf step. -/
noncomputable def clockPrefixDensity (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (f : Skorokhod.D a ℝ) : ℝ≥0∞ :=
  chi μ (n - ⌊a * n⌋₊) (Residue.project (arithFactor μ {0})
    (((n - ⌊a * n⌋₊ : ℕ) : ℤ) - 1)
      (round (f ⟨a, ha.le, le_rfl⟩ * B ⌊(n : ℝ) / (μ 0).toReal⌋₊))) / chi μ n 0

theorem measurable_clockPrefixDensity (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) : Measurable (clockPrefixDensity μ B n ha) := by
  exact ((measurable_of_countable (fun j : ℤ => chi μ (n - ⌊a * n⌋₊) j)).comp
    ((measurable_of_countable (Residue.project (arithFactor μ {0})
      (((n - ⌊a * n⌋₊ : ℕ) : ℤ) - 1))).comp
        (BGW.Probability.measurable_round.comp ((Skorokhod.measurable_eval _).mul_const _)))).div_const _

theorem tendsto_clockPrefixDensity {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (_hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f : ℕ → Skorokhod.D a ℝ} {g : Skorokhod.D a ℝ}
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun k => clockPrefixDensity μ B (q k) ha (f k)) atTop
      (𝓝 (ENNReal.ofReal (bridgePrefixWeight θ a ha.le g))) := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  obtain ⟨hDA, hBB⟩ := stableDomain_of_isRealStableAttracted hc hne hB
  have hcan := isRealStableAttracted_norming hc hne hDA
  let N := leafNormIndex (μ 0).toReal
  let r : ℕ → ℕ := fun k => q k - ⌊a * q k⌋₊
  let j0 : ℕ → ℤ := fun k => round ((f k) ⟨a, ha.le, le_rfl⟩ * B (N (q k)))
  let j : ℕ → ℤ := fun k => Residue.project (arithFactor μ {0}) ((r k : ℤ) - 1) (j0 k)
  let d := (1 - a)^(1 / θ)
  have hd : 0 < d := Real.rpow_pos_of_pos (sub_pos.mpr ha1) _
  have hNtop := (tendsto_leafNormIndex hp).comp hqtop
  have hrTop : Tendsto r atTop atTop := (tendsto_remaining_mark ha.le ha1).comp hqtop
  have hNrTop := (tendsto_leafNormIndex hp).comp hrTop
  have hAr : Tendsto (fun k => normB μ θ ((r k : ℝ) / (μ 0).toReal) /
      normB μ θ ((q k : ℝ) / (μ 0).toReal)) atTop (𝓝 d) :=
    (hcan.tendsto_norming_ratio (sub_pos.mpr ha1) (tendsto_leafNormIndex hp)
      (leafNormIndex_remaining_ratio hp ha.le ha1)).comp hqtop
  have he := ((Skorokhod.lipschitzWith_one_eval_right (E := ℝ) ha.le).continuous.tendsto g).comp hf
  have hjB := BGW.Probability.round_normalized_tendsto he (hB.tendsto_norming_atTop.comp hNtop)
  have hj0A : Tendsto (fun k => (j0 k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal))
      atTop (𝓝 (g ⟨a, ha.le, le_rfl⟩)) := by
    have ht := hjB.mul (hBB.comp hNtop)
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [hNtop.eventually hB.pos] with k hk
    simp only [Function.comp_def, leafNormIndex] at hk
    simp only [j0, N, leafNormIndex, Function.comp_def, normB]
    field_simp [hk.ne']
  have hjA : Tendsto (fun k => (j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal))
      atTop (𝓝 (g ⟨a, ha.le, le_rfl⟩)) :=
    Residue.project_normalized_tendsto (GeneralA.Arithmetic.arithFactor_pos hc hne {0})
      ((LocalLattice.block_norming_atTop hc hne hDA).comp hqtop) hj0A
  have hjAr : Tendsto (fun k => (j k : ℝ) / normB μ θ ((r k : ℝ) / (μ 0).toReal))
      atTop (𝓝 (g ⟨a, ha.le, le_rfl⟩ / d)) := by
    apply (hjA.div hAr hd.ne').congr'
    filter_upwards [hNtop.eventually hcan.pos] with k hk
    change (j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal) /
      (normB μ θ ((r k : ℝ) / (μ 0).toReal) / normB μ θ ((q k : ℝ) / (μ 0).toReal)) = _
    field_simp [show normB μ θ ((q k : ℝ) / (μ 0).toReal) ≠ 0 from (by simpa only [Function.comp_def, leafNormIndex, normB] using hk.ne')]
  have hnum := tendsto_scaled_chi hc hne hDA hrTop hjAr
    (Eventually.of_forall fun k => Residue.project_dvd _ _ _)
  have hp0 : 0 < Scalar.stableDensity θ 0 := Scalar.stableDensity_zero_pos hB.index_mem
  let span : ℝ := arithFactor μ {0}
  have hspan : 0 < span := by dsimp [span]; exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  have hspan0 : span * Scalar.stableDensity θ 0 ≠ 0 := (mul_pos hspan hp0).ne'
  have hden := DenominatorLattice.chi_zero_asymp hc hne hDA hqtop hq
  have hreal : Tendsto (fun k => (chi μ (r k) (j k)).toReal / (chi μ (q k) 0).toReal)
      atTop (𝓝 ((1 / d) * (Scalar.stableDensity θ (-(g ⟨a, ha.le, le_rfl⟩ / d)) /
        Scalar.stableDensity θ 0))) := by
    have ht := hAr.inv₀ hd.ne' |>.mul (hnum.div hden hspan0)
    have hcanc : ((arithFactor μ {0} : ℝ) * Scalar.stableDensity θ (-(g ⟨a, ha.le, le_rfl⟩ / d))) /
        ((arithFactor μ {0} : ℝ) * Scalar.stableDensity θ 0) =
        Scalar.stableDensity θ (-(g ⟨a, ha.le, le_rfl⟩ / d)) / Scalar.stableDensity θ 0 :=
      mul_div_mul_left _ _ hspan.ne'
    rw [hcanc] at ht
    simp only [inv_eq_one_div] at ht
    apply ht.congr'
    filter_upwards [hNtop.eventually hcan.pos, hNrTop.eventually hcan.pos, hden.eventually_ne hspan0] with k hk hrk hχk
    have hQ : normB μ θ ((q k : ℝ) / (μ 0).toReal) ≠ 0 := by
      simpa only [Function.comp_def, leafNormIndex, normB] using hk.ne'
    have hR : normB μ θ ((r k : ℝ) / (μ 0).toReal) ≠ 0 := by
      simpa only [Function.comp_def, leafNormIndex, normB] using hrk.ne'
    have hχ0 := (mul_ne_zero_iff.mp hχk).2
    simp only [Pi.div_apply]
    field_simp [hQ, hR, hχ0]
  have hident : (1 / d) * (Scalar.stableDensity θ (-(g ⟨a, ha.le, le_rfl⟩ / d)) /
      Scalar.stableDensity θ 0) = bridgePrefixWeight θ a ha.le g := by
    have hpow : (1 - a)^(-1 / θ) = 1 / d := by
      rw [show -1 / θ = -(1 / θ) by ring, Real.rpow_neg (sub_pos.mpr ha1).le]
      simp only [one_div, d]
    simp only [bridgePrefixWeight, stableDensityAt, hpow]
    have harg : -(g ⟨a, ha.le, le_rfl⟩ / d) = (1 / d) * -g ⟨a, ha.le, le_rfl⟩ := by ring
    rw [harg]
    ring
  rw [hident] at hreal
  apply (ENNReal.tendsto_ofReal hreal).congr'
  filter_upwards [hqtop.eventually_ge_atTop 1] with k hk
  have hχ : chi μ (q k) 0 ≠ 0 := by
    simpa only [chi, sub_zero, ← bridgeAtMark_eq_walkStopEvent] using
      (iidWalk_bridgeAtMark_ne_zero_iff μ hk).mpr (hq k)
  have hfin : chi μ (r k) (j k) / chi μ (q k) 0 ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top _ _) hχ
  rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal hfin]
  rfl


end BGWLeaves.LeafLimitsGeneral.BridgeLattice
