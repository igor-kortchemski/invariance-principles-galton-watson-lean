module

public import BGWLeaves.LeafLimitsGeneral.LocalLattice
public import BGWLeaves.LocalEstimates.NormRatios
public import BGWLeaves.LocalEstimates.SizeTailKernel

/-! Lattice 5.5(ii). Scale the forest mass by its span on permitted residues,
then use the regular-variation comparison from `LocalEstimates.LeafWindow`.
The comparison proofs below are copied and adapted from that provider. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.ShiftLattice
open MeasureTheory ProbabilityTheory Filter Asymptotics BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.LocalEstimates NormRatios LeafWindow
open scoped ENNReal Topology

private theorem index_atTop {k : ℕ → ℕ} {l : ℝ} (hl : 0 < l)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 l)) : Tendsto k atTop atTop := by
  have ht := hk.pos_mul_atTop hl tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop := ht.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp)
  exact tendsto_natCast_atTop_iff.mp ht'

section
variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

set_option linter.unusedSectionVars false in
private theorem norming_positive : ∀ᶠ n : ℕ in atTop, 0 < norming (stepLaw μ) θ n := by
  obtain ⟨b, hb⟩ := hDA
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  exact (TransformConvergence.tendsto_atTop (stepLaw μ) ha).eventually (eventually_gt_atTop 0)

private theorem inverse_scale_ratio {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => normB μ θ n / normB μ θ (u n)) atTop (𝓝 ((l ^ (1 / θ))⁻¹)) ∧
      ∀ᶠ n : ℕ in atTop, 0 < normB μ θ (u n) := by
  have ht := NormRatios.normB_ratio_tendsto hc hne hap hDA hl hu
  have hlp : 0 < l ^ (1 / θ) := Real.rpow_pos_of_pos hl _
  refine ⟨by simpa only [inv_div] using ht.inv₀ hlp.ne', ?_⟩
  filter_upwards [ht.eventually (Ioi_mem_nhds hlp), norming_positive hc hne hap hDA] with n hn hB
  rw [normB_natCast] at hn
  rw [lt_div_iff₀ hB, zero_mul] at hn
  exact hn

private theorem shifted_range {k : ℕ → ℕ} {l : ℝ} (hl : 0 < l)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 l)) {α : ℝ} (hα : 0 < α) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, 0 < normB μ θ (k n) ∧ α * normB μ θ n ≤ A * normB μ θ (k n) := by
  obtain ⟨hr, hp⟩ := inverse_scale_ratio hc hne hap hDA hl hk
  let r : ℝ := (l ^ (1 / θ))⁻¹
  have hr0 : 0 < r := by dsimp [r]; positivity
  refine ⟨α * (r + 1), by positivity, ?_⟩
  filter_upwards [hp, hr.eventually (eventually_lt_nhds (show r < r + 1 by linarith))] with n hn hrat
  refine ⟨hn, ?_⟩
  have hh := (div_lt_iff₀ hn).mp hrat
  nlinarith

private theorem uniform_scale_compare (f : ℝ → ℝ)
    (hf : ∀ A : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A → |f x - f y| ≤ L * |x - y|)
    {d e : ℕ → ℝ} {r : ℝ}
    (hd : Tendsto (fun n : ℕ => normB μ θ n / d n) atTop (𝓝 r))
    (he : Tendsto (fun n : ℕ => normB μ θ n / e n) atTop (𝓝 r))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < d n ∧ 0 < e n)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, (j : ℝ) ≤ α * normB μ θ n →
      |f ((j : ℝ) / d n) - f ((j : ℝ) / e n)| ≤ η := by
  let A : ℝ := α * (|r| + 1)
  obtain ⟨L, hL, hLip⟩ := hf A
  have hsmall : Tendsto (fun n : ℕ => L * α * |normB μ θ n / d n - normB μ θ n / e n|) atTop (𝓝 0) := by
    simpa using (hd.sub he).abs.const_mul (L * α)
  have hdu : ∀ᶠ n : ℕ in atTop, normB μ θ n / d n ≤ |r| + 1 := by
    filter_upwards [hd.eventually (Metric.ball_mem_nhds r zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    linarith [le_abs_self (normB μ θ n / d n - r), le_abs_self r]
  have heu : ∀ᶠ n : ℕ in atTop, normB μ θ n / e n ≤ |r| + 1 := by
    filter_upwards [he.eventually (Metric.ball_mem_nhds r zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    linarith [le_abs_self (normB μ θ n / e n - r), le_abs_self r]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hsmall.eventually (eventually_lt_nhds hη)).and
    (hp.and (hdu.and (heu.and (norming_positive hc hne hap hDA)))))
  refine ⟨N, fun n hn j hju => ?_⟩
  obtain ⟨hs, ⟨hdp, hep⟩, hdb, heb, hBp⟩ := hN n hn
  have hB : 0 < normB μ θ n := by simpa only [normB_natCast] using hBp
  have harg (a : ℝ) (ha : 0 < a) (hab : normB μ θ n / a ≤ |r| + 1) : 0 ≤ (j : ℝ) / a ∧ (j : ℝ) / a ≤ A := by
    refine ⟨by positivity, ?_⟩
    calc _ ≤ α * normB μ θ n / a := div_le_div_of_nonneg_right hju ha.le
      _ = α * (normB μ θ n / a) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left hab hα.le
  obtain ⟨hxd, hxdA⟩ := harg (d n) hdp hdb
  obtain ⟨hxe, hxeA⟩ := harg (e n) hep heb
  apply (hLip _ _ hxd hxdA hxe hxeA).trans
  have heq : (j : ℝ) / d n - (j : ℝ) / e n =
      ((j : ℝ) / normB μ θ n) * (normB μ θ n / d n - normB μ θ n / e n) := by field_simp
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) / normB μ θ n)]
  have hjdiv : (j : ℝ) / normB μ θ n ≤ α := (div_le_iff₀ hB).mpr hju
  calc
    _ ≤ L * (α * |normB μ θ n / d n - normB μ θ n / e n|) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hjdiv (abs_nonneg _)) hL
    _ = L * α * |normB μ θ n / d n - normB μ θ n / e n| := by ring
    _ ≤ η := hs.le

set_option linter.unusedSectionVars false in
private theorem linear_time_ratio (m : ℝ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n : ℝ) / m) / n) atTop (𝓝 (1 / m)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

private theorem uniform_leaf_shift (f : ℝ → ℝ)
    (hf : ∀ A : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A → |f x - f y| ≤ L * |x - y|)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, (j : ℝ) ≤ α * normB μ θ n →
      |f ((j : ℝ) / ((1 - a) ^ (1 / θ) * normB μ θ ((n : ℝ) / (μ 0).toReal))) -
        f ((j : ℝ) / normB μ θ (((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / (μ 0).toReal))| ≤ η := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq : 0 < 1 - a := sub_pos.mpr ha1
  have hmn := mn_ratio_tendsto hc hne hap hDA ha0 ha1 hr hrn
  have hv : Tendsto (fun n : ℕ => (((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / (μ 0).toReal) / n)
      atTop (𝓝 ((1 - a) / (μ 0).toReal)) := by
    convert hmn.div_const (μ 0).toReal using 1
    ext n
    ring
  obtain ⟨ht₁, hp₁⟩ := inverse_scale_ratio hc hne hap hDA (one_div_pos.mpr hm)
    (linear_time_ratio hc hne hap hDA (μ 0).toReal hm)
  obtain ⟨ht₂, hp₂⟩ := inverse_scale_ratio hc hne hap hDA (div_pos hq hm) hv
  have hcpos : 0 < (1 - a) ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have heq : (((1 - a) / (μ 0).toReal) ^ (1 / θ))⁻¹ =
      ((1 / (μ 0).toReal) ^ (1 / θ))⁻¹ / (1 - a) ^ (1 / θ) := by
    rw [Real.div_rpow hq.le hm.le, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hm.le, Real.one_rpow]
    simp only [inv_div, div_one]
  rw [heq] at ht₂
  have ht₁' : Tendsto (fun n : ℕ => normB μ θ n / ((1 - a) ^ (1 / θ) * normB μ θ ((n : ℝ) / (μ 0).toReal))) atTop
      (𝓝 (((1 / (μ 0).toReal) ^ (1 / θ))⁻¹ / (1 - a) ^ (1 / θ))) := by
    convert ht₁.div_const ((1 - a) ^ (1 / θ)) using 1
    ext n
    ring
  apply uniform_scale_compare hc hne hap hDA f hf ht₁' ht₂ _ hα hη
  filter_upwards [hp₁, hp₂] with n hn₁ hn₂
  exact ⟨mul_pos hcpos hn₁, hn₂⟩

private theorem shifted_on_residue
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      (arithFactor μ {0} : ℤ) ∣ ((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℤ) - j →
      |(n : ℝ) * ((psi μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal / (arithFactor μ {0} : ℝ)) -
          qKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  have hg : 0 < (arithFactor μ {0} : ℝ) := by exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq : 0 < 1 - a := sub_pos.mpr ha1
  let k : ℕ → ℕ := fun n => n - ⌊a * (μ 0).toReal * r n⌋₊
  let t : ℝ := 1 / (1 - a)
  let c : ℝ := (1 - a) ^ (1 / θ)
  have ht : 0 < t := one_div_pos.mpr hq
  have hcpos : 0 < c := Real.rpow_pos_of_pos hq _
  let η : ℝ := ε / (3 * (t + 2))
  have hη : 0 < η := by dsimp [η]; positivity
  have hbudget : (t + 1) * η ≤ ε / 3 := by
    calc _ ≤ (t + 2) * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
      _ = ε / 3 := by dsimp [η]; field_simp
  have hmn := mn_ratio_tendsto hc hne hap hDA ha0 ha1 hr hrn
  have hktop : Tendsto k atTop atTop := index_atTop hq hmn
  have hinv : Tendsto (fun n : ℕ => (n : ℝ) / (k n : ℝ)) atTop (𝓝 t) := by
    simpa only [inv_div, one_div, t] using hmn.inv₀ hq.ne'
  obtain ⟨A, hA, hrange⟩ := shifted_range hc hne hap hDA hq hmn hα
  obtain ⟨Nt, htech⟩ := LocalLattice.lem_technical_ii hc hne hDA hA (mul_pos hg hη)
  obtain ⟨Nc, hcomp⟩ := uniform_leaf_shift hc hne hap hDA (qKernel θ 1)
    (SizeTailKernel.qKernel_one_lipschitzOn hb.alpha_mem) ha0 ha1 hr hrn hα hη
  obtain ⟨M, hM, hMb⟩ := Scalar.exists_stableDensity_le (α := θ)
  obtain ⟨hDen, hpDen⟩ := inverse_scale_ratio hc hne hap hDA (one_div_pos.mpr hm)
    (linear_time_ratio hc hne hap hDA (μ 0).toReal hm)
  let R : ℝ := ((1 / (μ 0).toReal) ^ (1 / θ))⁻¹ / c
  let Q : ℝ := (α * (|R| + 1)) * M
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDb : ∀ᶠ n : ℕ in atTop, normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal)) ≤ |R| + 1 := by
    have hd : Tendsto (fun n : ℕ => normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal))) atTop (𝓝 R) := by
      convert hDen.div_const c using 1
      ext n
      ring
    filter_upwards [hd.eventually (Metric.ball_mem_nhds R zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    linarith [le_abs_self (normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal)) - R), le_abs_self R]
  have hsmall : Tendsto (fun n : ℕ => Q * |(n : ℝ) / (k n : ℝ) - t|) atTop (𝓝 0) := by
    simpa using (hinv.sub_const t).abs.const_mul Q
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrange.and ((hktop.eventually (eventually_ge_atTop (max 1 Nt))).and
    (hpDen.and (hDb.and ((hinv.eventually (eventually_lt_nhds (show t < t + 1 by linarith))).and
      (hsmall.eventually (eventually_lt_nhds (by positivity : 0 < ε / 3))))))))
  refine ⟨max N Nc, fun n hn j hj hju hres => ?_⟩
  obtain ⟨⟨hkp, hrng⟩, hkN, hdp, hdb, hir, hsm⟩ := hN n (le_of_max_le_left hn)
  have hk1 : 1 ≤ k n := le_of_max_le_left hkN
  have hkt : Nt ≤ k n := le_of_max_le_right hkN
  have hk0 : (k n : ℝ) ≠ 0 := by exact_mod_cast (show k n ≠ 0 by omega)
  have hir0 : 0 ≤ (n : ℝ) / (k n : ℝ) := by positivity
  have hTraw := htech (k n) hkt j hj (hju.trans hrng)
  rw [ite_eq_left hres] at hTraw
  have hT : |(k n : ℝ) * ((psi μ (k n) j).toReal / (arithFactor μ {0} : ℝ)) -
      qKernel θ 1 ((j : ℝ) / normB μ θ ((k n : ℝ) / (μ 0).toReal))| ≤ η := by
    have hh := div_le_div_of_nonneg_right hTraw hg.le
    rw [mul_div_cancel_left₀ η hg.ne'] at hh
    have he : (k n : ℝ) * ((psi μ (k n) j).toReal / (arithFactor μ {0} : ℝ)) -
        qKernel θ 1 ((j : ℝ) / normB μ θ ((k n : ℝ) / (μ 0).toReal)) =
        ((k n : ℝ) * (psi μ (k n) j).toReal - (arithFactor μ {0} : ℝ) *
          qKernel θ 1 ((j : ℝ) / normB μ θ ((k n : ℝ) / (μ 0).toReal))) /
            (arithFactor μ {0} : ℝ) := by field_simp [hg.ne']
    rw [he, abs_div, abs_of_pos hg]
    exact hh
  have hC := hcomp n (le_of_max_le_right hn) j hju
  let x : ℝ := (j : ℝ) / normB μ θ (((k n : ℕ) : ℝ) / (μ 0).toReal)
  let y : ℝ := (j : ℝ) / (c * normB μ θ ((n : ℝ) / (μ 0).toReal))
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyA : y ≤ α * (|R| + 1) := by
    calc _ ≤ α * normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal)) := div_le_div_of_nonneg_right hju (by positivity)
      _ = α * (normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdb hα.le
  have hqb : |qKernel θ 1 y| ≤ Q := by
    rw [qKernel_one, abs_mul, abs_of_nonneg hy]
    exact mul_le_mul hyA (hMb _) (abs_nonneg _) (by positivity)
  have heval : qKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)) = t * qKernel θ 1 y := by
    rw [SizeTailKernel.qKernel_scaling hq, Real.rpow_neg hq.le]
    rw [show (1 - a)⁻¹ = t by dsimp only [t]; rw [one_div]]
    apply congrArg (fun z : ℝ => t * qKernel θ 1 z)
    dsimp only [y, c]
    ring
  have h₁ : |(n : ℝ) * ((psi μ (k n) j).toReal / (arithFactor μ {0} : ℝ)) - ((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x| ≤ ε / 3 := by
    have heq : (n : ℝ) * ((psi μ (k n) j).toReal / (arithFactor μ {0} : ℝ)) - ((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x =
        ((n : ℝ) / (k n : ℝ)) * ((k n : ℝ) * ((psi μ (k n) j).toReal / (arithFactor μ {0} : ℝ)) - qKernel θ 1 x) := by field_simp
    rw [heq, abs_mul, abs_of_nonneg hir0]
    exact (mul_le_mul hir.le hT (abs_nonneg _) (by linarith : 0 ≤ t + 1)).trans hbudget
  have h₂ : |((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x - ((n : ℝ) / (k n : ℝ)) * qKernel θ 1 y| ≤ ε / 3 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hir0]
    rw [abs_sub_comm] at hC
    exact (mul_le_mul hir.le hC (abs_nonneg _) (by linarith : 0 ≤ t + 1)).trans hbudget
  have h₃ : |((n : ℝ) / (k n : ℝ)) * qKernel θ 1 y - t * qKernel θ 1 y| ≤ ε / 3 := by
    rw [← sub_mul, abs_mul]
    calc _ ≤ |(n : ℝ) / (k n : ℝ) - t| * Q := mul_le_mul_of_nonneg_left hqb (abs_nonneg _)
      _ = Q * |(n : ℝ) / (k n : ℝ) - t| := by ring
      _ ≤ ε / 3 := hsm.le
  have hh := abs_sub_le ((n : ℝ) * ((psi μ (k n) j).toReal / (arithFactor μ {0} : ℝ)))
    (((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x) (t * qKernel θ 1 y)
  have hh' := abs_sub_le (((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x)
    (((n : ℝ) / (k n : ℝ)) * qKernel θ 1 y) (t * qKernel θ 1 y)
  rw [heval]
  change |_ - _| ≤ ε
  linarith

/-- Lattice replacement for 5.5(ii), with the residue at the remaining leaf count. -/
theorem cor_tejhnique_ii {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ}
    (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(n : ℝ) * (psi μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal -
        (if (arithFactor μ {0} : ℤ) ∣ ((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℤ) - j then
          (arithFactor μ {0} : ℝ) * qKernel θ (1 - a)
            ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)) else 0)| ≤ ε := by
  have hg : 0 < (arithFactor μ {0} : ℝ) := by exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  obtain ⟨N, hN⟩ := shifted_on_residue hc hne hap hDA ha0 ha1 hr hrn hα (div_pos hε hg)
  refine ⟨N, fun n hn j hj hju => ?_⟩
  by_cases hres : (arithFactor μ {0} : ℤ) ∣ ((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℤ) - j
  · rw [ite_eq_left hres]
    have hh := mul_le_mul_of_nonneg_left (hN n hn j hj hju hres) hg.le
    rw [mul_div_cancel₀ ε hg.ne'] at hh
    have he : (n : ℝ) * (psi μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal -
        (arithFactor μ {0} : ℝ) * qKernel θ (1 - a)
          ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)) =
        (arithFactor μ {0} : ℝ) *
          ((n : ℝ) * ((psi μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal /
            (arithFactor μ {0} : ℝ)) - qKernel θ (1 - a)
              ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))) := by
      field_simp [hg.ne']
    rw [he, abs_mul, abs_of_pos hg]
    exact hh
  · rw [ite_eq_right hres, LocalLattice.psi_eq_markedForest hc hne,
      GeneralAInf.Forest.zetaA_forest_eq_zero_of_not_dvd hc hne {0} hj hres]
    simpa using hε.le

end
end BGWLeaves.LeafLimitsGeneral.ShiftLattice
