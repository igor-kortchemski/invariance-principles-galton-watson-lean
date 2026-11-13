module

public import BGWLeaves.LeafLimitsGeneral.Residue

/-! Lattice absolute-continuity densities. The analytic assembly is adapted from
`LeafLimits.Absolue`, retaining the residue hypotheses until projection. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.DensityLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.LeafLimits BGWLeaves.LeafLimits.Absolue
open scoped ENNReal NNReal Topology

private theorem tendsto_zero_of_uniform_error {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) {e : ℕ → ℕ → ℝ} {j : ℕ → ℕ}
    {R : ℕ → ℝ} (hj : ∀ᶠ n : ℕ in atTop, 1 ≤ j n ∧ (j n : ℝ) ≤ R (q n))
    (he : ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ i : ℕ,
      1 ≤ i → (i : ℝ) ≤ R n → |e n i| ≤ ε) :
    Tendsto (fun n => e (q n) (j n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := he (ε / 2) (half_pos hε)
  filter_upwards [hqtop.eventually_ge_atTop N, hj] with n hn hjn
  rw [Real.dist_eq, sub_zero]
  exact (hN (q n) hn (j n) hjn.1 hjn.2).trans_lt (half_lt_self hε)

theorem tendsto_remaining_density {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ b, StableDomain μ θ b) (hθ : 1 < θ ∧ θ ≤ 2)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {j : ℕ → ℕ} {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hj : ∀ᶠ n : ℕ in atTop, 1 ≤ j n ∧ (j n : ℝ) ≤ α * normB μ θ (q n))
    (hjx : Tendsto (fun n => (j n : ℝ) / normB μ θ ((q n : ℝ) / (μ 0).toReal))
      atTop (𝓝 x))
    (hres : ∀ᶠ n : ℕ in atTop, (arithFactor μ {0} : ℤ) ∣
      ((q n - ⌊a * (μ 0).toReal * r (q n)⌋₊ : ℕ) : ℤ) - j n) :
    Tendsto (fun n : ℕ => θ * ((q n : ℝ) *
        (psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal) /
      (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal)
      atTop (𝓝 ((arithFactor μ {0} : ℝ) * gammaA θ a x)) := by
  have hdom : IsOpen {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} :=
    (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd)
  have harg : Tendsto (fun n => (1 - a,
      (j n : ℝ) / normB μ θ ((q n : ℝ) / (μ 0).toReal))) atTop (𝓝 (1 - a, x)) :=
    tendsto_const_nhds.prodMk_nhds hjx
  have hpos : (1 - a, x) ∈ {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} :=
    ⟨sub_pos.mpr ha1, hx⟩
  have hG := ((continuousOn_sizeTailKernel hθ).continuousAt
    (hdom.mem_nhds hpos)).tendsto.comp harg
  have hQ := ((continuousOn_qKernel hθ).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds (sub_pos.mpr ha1))).tendsto.comp harg
  simp only [Function.comp_def, ← ClassicalLimits.Cited.sizeTailKernel_eq_kernel] at hG
  simp only [Function.comp_def, ← ClassicalLimits.Cited.qKernel_eq_kernel] at hQ
  have hGe := tendsto_zero_of_uniform_error hqtop hj
    (fun ε hε => cor_tejhnique_i hc hne hap hDA ha0 ha1 hr hrn hα hε)
  have hQe : Tendsto (fun n : ℕ => (q n : ℝ) *
      (psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal -
        (arithFactor μ {0} : ℝ) * BGWLeaves.qKernel θ (1 - a)
          ((j n : ℝ) / normB μ θ ((q n : ℝ) / (μ 0).toReal))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := ShiftLattice.cor_tejhnique_ii hc hne hap hDA ha0 ha1 hr hrn hα (half_pos hε)
    filter_upwards [hqtop.eventually_ge_atTop N, hj, hres] with n hn hjn hrn
    rw [Real.dist_eq, sub_zero]
    have hh := hN (q n) hn (j n) hjn.1 hjn.2
    rw [ite_eq_left hrn] at hh
    exact hh.trans_lt (half_lt_self hε)
  have hGl : Tendsto (fun n =>
      (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal) atTop
      (𝓝 (BGWLeaves.sizeTailKernel θ (1 - a) x)) := by
    convert hGe.add hG using 1 <;> simp
  have hQl : Tendsto (fun n : ℕ => (q n : ℝ) *
      (psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal) atTop
      (𝓝 ((arithFactor μ {0} : ℝ) * BGWLeaves.qKernel θ (1 - a) x)) := by
    convert hQe.add (hQ.const_mul (arithFactor μ {0} : ℝ)) using 1 <;> simp
  have hGn : BGWLeaves.sizeTailKernel θ (1 - a) x ≠ 0 := by
    rw [ClassicalLimits.Cited.sizeTailKernel_eq_kernel]
    exact (sizeTailKernel_pos hθ (sub_pos.mpr ha1) hx).ne'
  rw [ClassicalLimits.Cited.gammaA_eq_paper]
  convert (hQl.const_mul θ).div hGl hGn using 1
  ring_nf

theorem tendsto_abscon_density {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ b, StableDomain μ θ b) (hθ : 1 < θ ∧ θ ≤ 2)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ n, LeafAdmissible μ (q n))
    {j : ℕ → ℕ} {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hj : ∀ᶠ n : ℕ in atTop, 1 ≤ j n ∧ (j n : ℝ) ≤ α * normB μ θ (q n))
    (hjx : Tendsto (fun n => (j n : ℝ) / normB μ θ ((q n : ℝ) / (μ 0).toReal))
      atTop (𝓝 x))
    (hres : ∀ᶠ n : ℕ in atTop, (arithFactor μ {0} : ℤ) ∣
      ((q n - ⌊a * (μ 0).toReal * r (q n)⌋₊ : ℕ) : ℤ) - j n) :
    Tendsto (fun n : ℕ =>
      (((psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n) / psi μ (q n) 1) /
        (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n) /
          psiStar μ (q n) 1)).toReal)) atTop (𝓝 (gammaA θ a x)) := by
  have hθn : θ ≠ 0 := by linarith [hθ.1]
  have hrem := tendsto_remaining_density hc hne hap hDA hθ ha0 ha1 hr hrn
    hqtop hα hx hj hjx hres
  have hcoef := DenominatorLattice.tendsto_tail_div_leaf_mass hc hne hap hDA hqtop hq
  have ht := (hrem.div_const θ).mul hcoef
  have hg : (arithFactor μ {0} : ℝ) ≠ 0 := by
    exact_mod_cast (GeneralA.Arithmetic.arithFactor_pos hc hne {0}).ne'
  have he : ((arithFactor μ {0} : ℝ) * gammaA θ a x / θ) *
      (θ / (arithFactor μ {0} : ℝ)) = gammaA θ a x := by field_simp
  rw [he] at ht
  apply ht.congr'
  filter_upwards [hqtop.eventually (eventually_ne_atTop (0 : ℕ))] with n hn
  have hnR : (q n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [ENNReal.toReal_div]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  generalize (psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal = A
  generalize (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal = C
  generalize (psi μ (q n) 1).toReal = E
  generalize (psiStar μ (q n) 1).toReal = D
  calc
    _ = (θ * θ⁻¹) * ((q n : ℝ) * (q n : ℝ)⁻¹) * (A * E⁻¹ * (D * C⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hθn, mul_inv_cancel₀ hnR]; ring

/-- The leaf-forest density projected onto the permitted endpoint residue. -/
noncomputable def absWeight (μ : PMF ℕ) (B : ℕ → ℝ) (r n : ℕ) (a : ℝ≥0)
    (z : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ)) : ℝ≥0∞ :=
  let m := n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊
  let j := Residue.natProject (arithFactor μ {0}) (m : ℤ) ⌊B r * evalEnd a z.1⌋₊
  (psi μ m j / psi μ n 1) / (psiStar μ m j / psiStar μ n 1)

theorem measurable_absWeight (μ : PMF ℕ) (B : ℕ → ℝ) (r n : ℕ) (a : ℝ≥0) :
    Measurable (absWeight μ B r n a) := by
  exact (measurable_of_countable (fun j : ℕ =>
    (psi μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) j / psi μ n 1) /
      (psiStar μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) j / psiStar μ n 1))).comp
    ((measurable_of_countable (Residue.natProject (arithFactor μ {0})
      ((n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊ : ℕ) : ℤ))).comp
      ((measurable_const.mul ((measurable_evalEnd a).comp measurable_fst)).nat_floor))

private theorem mu0_bounds {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    0 < (μ 0).toReal ∧ (μ 0).toReal < 1 := by
  refine ⟨ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0), ?_⟩
  have hle : (μ 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  refine lt_of_le_of_ne hle fun heq => BGWLeaves.mu0_ne_one hc hne ?_
  exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top 0) ENNReal.one_ne_top).1
    (by simpa using heq)

private theorem norming_rGreatest_ratio {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    Tendsto (fun n : ℕ => B (rGreatest μ n) /
      normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 (1 : ℝ)) := by
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  have hcan := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).2
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos
    (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hp1 : (μ 0).toReal < 1 := by
    have hle : (μ 0).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
    refine lt_of_le_of_ne hle fun heq => BGWLeaves.mu0_ne_one hc hne ?_
    exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top 0) ENNReal.one_ne_top).1
      (by simpa using heq)
  have hr := BGWLeaves.normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hp)
    (tendsto_rGreatest_div_leaf hp hp1)
  have hdindex : Tendsto (fun n : ℕ => ((n : ℝ) / (μ 0).toReal) / n)
      atTop (𝓝 (1 / (μ 0).toReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hd := BGWLeaves.normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hp) hdindex
  simp only [normB_natCast] at hr hd
  have h := ((hcan.comp (tendsto_rGreatest hp hp1)).mul hr).div hd
    (Real.rpow_pos_of_pos (one_div_pos.mpr hp) _).ne'
  simp only [one_mul, div_self (Real.rpow_pos_of_pos (one_div_pos.mpr hp) _).ne'] at h
  apply h.congr'
  filter_upwards [normB_pos_eventually hc hne hap hDA,
    (tendsto_rGreatest hp hp1).eventually (normB_pos_eventually hc hne hap hDA)] with n hn hrn
  dsimp
  field_simp [hn.ne', hrn.ne']


theorem absWeight_contConv {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, LeafAdmissible μ (q k))
    {z : ℕ → Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ)} {x : ℝ}
    (hx : 0 < x) (hz : Tendsto (fun k => evalEnd a (z k).1) atTop (𝓝 x)) :
    Tendsto (fun k => (absWeight μ B (rGreatest μ (q k)) (q k) a (z k)).toReal)
      atTop (𝓝 (gammaA θ a x)) := by
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  let j0 := fun k => ⌊B (rGreatest μ (q k)) * evalEnd a (z k).1⌋₊
  have hBr := hB.tendsto_norming_atTop.comp ((tendsto_rGreatest hp hp1).comp hqtop)
  have hprod := hBr.atTop_mul_pos hx hz
  have hj0top : Tendsto j0 atTop atTop := tendsto_nat_floor_atTop.comp hprod
  have hratio := (norming_rGreatest_ratio hc hne hap hB).comp hqtop
  have hfloor := tendsto_nat_floor_div_atTop.comp hprod
  have hj0x : Tendsto (fun k => (j0 k : ℝ) /
      normB μ θ ((q k : ℝ) / (μ 0).toReal)) atTop (𝓝 x) := by
    have ht := hfloor.mul (hratio.mul hz)
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [hprod.eventually (eventually_ne_atTop (0 : ℝ))] with k hk
    dsimp only [Function.comp_apply, j0] at hk ⊢
    rw [show B (rGreatest μ (q k)) / normB μ θ ((q k : ℝ) / (μ 0).toReal) *
      evalEnd a (z k).1 = (B (rGreatest μ (q k)) * evalEnd a (z k).1) /
        normB μ θ ((q k : ℝ) / (μ 0).toReal) by ring]
    exact div_mul_div_cancel₀ hk
  have hg := GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  let residue := fun k => ((q k - ⌊(a : ℝ) * (μ 0).toReal * rGreatest μ (q k)⌋₊ : ℕ) : ℤ)
  let j := fun k => Residue.natProject (arithFactor μ {0}) (residue k) (j0 k)
  have hjtop : Tendsto j atTop atTop := tendsto_atTop_mono
    (fun k => (Residue.natProject_bounds hg (residue k) (j0 k)).1) hj0top
  have hjx : Tendsto (fun k => (j k : ℝ) /
      normB μ θ ((q k : ℝ) / (μ 0).toReal)) atTop (𝓝 x) := by
    have ht := Residue.project_normalized_tendsto hg (r := residue) (z := fun k => (j0 k : ℤ))
      ((LocalLattice.block_norming_atTop hc hne hDA).comp hqtop) (by simpa using hj0x)
    convert ht using 1
    funext k
    rw [← Residue.natProject_cast hg]
    simp only [Int.cast_natCast]
    rfl
  have hcpos : 0 < (1 / (μ 0).toReal) ^ (1 / θ) :=
    Real.rpow_pos_of_pos (one_div_pos.mpr hp) _
  have hdindex : Tendsto (fun n : ℕ => ((n : ℝ) / (μ 0).toReal) / n)
      atTop (𝓝 (1 / (μ 0).toReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hd := (normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hp) hdindex).comp hqtop
  have hupper := hjx.mul hd
  have hupper' : Tendsto (fun k => (j k : ℝ) / normB μ θ (q k)) atTop
      (𝓝 (x * (1 / (μ 0).toReal) ^ (1 / θ))) := by
    apply hupper.congr'
    have hfloorindex : Tendsto (fun k => ⌊(q k : ℝ) / (μ 0).toReal⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp
        ((tendsto_natCast_atTop_atTop.comp hqtop).atTop_div_const hp)
    filter_upwards [hfloorindex.eventually (normB_pos_eventually hc hne hap hDA)] with k hk
    dsimp [normB] at hk ⊢
    field_simp [hk.ne']
  let α := x * (1 / (μ 0).toReal) ^ (1 / θ) + 1
  have hα : 0 < α := by dsimp [α]; positivity
  have hj : ∀ᶠ k in atTop, 1 ≤ j k ∧ (j k : ℝ) ≤ α * normB μ θ (q k) := by
    filter_upwards [hjtop.eventually_ge_atTop 1,
      hupper'.eventually (gt_mem_nhds (show x * (1 / (μ 0).toReal) ^ (1 / θ) < α by dsimp [α]; linarith)),
      hqtop.eventually (normB_pos_eventually hc hne hap hDA)] with k hjk huk hnk
    refine ⟨hjk, ?_⟩
    rw [normB_natCast]
    rw [normB_natCast] at huk
    exact ((div_lt_iff₀ hnk).1 huk).le
  let r := fun n => max (rGreatest μ n) 1
  have hr : ∀ n, 0 < r n := fun n => lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hre : ∀ᶠ n : ℕ in atTop, r n = rGreatest μ n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact max_eq_left (rGreatest_spec hp hp1 hn).1
  have hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal) :=
    (tendsto_leaf_div_rGreatest hp hp1).congr' (hre.mono fun n hn => by
      change (n : ℝ) / rGreatest μ n = (n : ℝ) / r n
      rw [hn])
  have hres : ∀ᶠ k : ℕ in atTop, (arithFactor μ {0} : ℤ) ∣
      ((q k - ⌊(a : ℝ) * (μ 0).toReal * r (q k)⌋₊ : ℕ) : ℤ) - j k := by
    filter_upwards [hqtop.eventually hre] with k hk
    rw [hk]
    exact Residue.natProject_dvd hg (residue k) (j0 k)
  have ht := tendsto_abscon_density hc hne hap hDA hB.index_mem
    (NNReal.coe_pos.mpr ha.1) (NNReal.coe_lt_coe.mpr ha.2) hr hrn hqtop hq hα hx hj hjx hres
  apply ht.congr'
  filter_upwards [hqtop.eventually hre] with k hk
  simp only [hk, absWeight, j, residue, j0]



end BGWLeaves.LeafLimitsGeneral.DensityLattice
