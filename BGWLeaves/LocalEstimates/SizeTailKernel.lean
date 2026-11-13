module

public import BGWLeaves.LocalEstimates.Defs
import BGWLeaves.StableAnalysis.TransformConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Lemma 5.11: the uniform size-tail kernel

Proofs of the nine `SizeTailKernel` statements of `BGWLeaves.LocalEstimates`, exported
with exactly the types stated there in namespace `BGWLeaves.LocalEstimates.SizeTailKernel`.

The unmarked Kemperman formula gives the discrete tail identity, and the uniform local limit
theorem with Karamata domination gives `sizeTail_llt`. For the Riemann step, the discrete sum
is exactly the integral of its floor-step extension. The scalar error `gridError` bounds the
approximation simultaneously for all spatial arguments in `[0, α]`. Potter bounds dominate
this error by a constant times `s ^ (-1 - 1 / θ / 2)`, an integrable function on `(1, ∞)`.
Dominated convergence therefore gives the uniform Riemann tail and Lemma 5.11, with no
variance-regime restriction beyond the stable-domain hypotheses of the statement.
-/

@[expose] public section

namespace BGWLeaves.LocalEstimates.SizeTailKernel

open MeasureTheory ProbabilityTheory Filter Set BGW BGW.StableTrees
open BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

theorem qKernel_scaling {θ : ℝ} {a : ℝ} (ha : 0 < a) (x : ℝ) :
    qKernel θ a x = a⁻¹ * qKernel θ 1 (x * a ^ (-(1 / θ))) := by
  have _ := ha
  rw [qKernel_one]
  simp only [qKernel, pDens, neg_mul, div_eq_mul_inv]
  ring

theorem qKernel_one_lipschitzOn {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (A : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A →
      |qKernel θ 1 x - qKernel θ 1 y| ≤ L * |x - y| := by
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  obtain ⟨K, hLip⟩ : ∃ K : ℝ≥0, LipschitzWith K (Scalar.stableDensity θ) :=
    ⟨_, Scalar.lipschitzWith_stableDensity hθ⟩
  refine ⟨max A 0 * K + M, by positivity, ?_⟩
  intro x y hx hxA hy hyA
  have hd : |Scalar.stableDensity θ (-x) - Scalar.stableDensity θ (-y)| ≤
      (K : ℝ) * |x - y| := by
    simpa only [Real.dist_eq, neg_sub_neg, abs_sub_comm y x] using hLip.dist_le_mul (-x) (-y)
  rw [qKernel_one, qKernel_one]
  calc
    |x * Scalar.stableDensity θ (-x) - y * Scalar.stableDensity θ (-y)| =
        |x * (Scalar.stableDensity θ (-x) - Scalar.stableDensity θ (-y)) +
          (x - y) * Scalar.stableDensity θ (-y)| := by congr 1; ring
    _ ≤ |x * (Scalar.stableDensity θ (-x) - Scalar.stableDensity θ (-y))| +
          |(x - y) * Scalar.stableDensity θ (-y)| := abs_add_le _ _
    _ ≤ x * ((K : ℝ) * |x - y|) + |x - y| * M := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx]
      exact add_le_add (mul_le_mul_of_nonneg_left hd hx)
        (mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _))
    _ ≤ max A 0 * ((K : ℝ) * |x - y|) + |x - y| * M := by
      gcongr
      exact hxA.trans (le_max_left _ _)
    _ = (max A 0 * K + M) * |x - y| := by ring

private theorem qKernel_mul_time {θ a s x : ℝ} (ha : 0 < a) (hs : 0 < s) :
    qKernel θ (a * s) x = a⁻¹ * qKernel θ s (x * a ^ (-(1 / θ))) := by
  simp only [qKernel, pDens, Real.mul_rpow ha.le hs.le, neg_mul, div_eq_mul_inv,
    mul_inv_rev]
  ring_nf

theorem sizeTailKernel_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a : ℝ}
    (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    sizeTailKernel θ a x = sizeTailKernel θ 1 (x * a ^ (-(1 / θ))) := by
  have _ := hθ
  have _ := hx
  have ht := integral_comp_mul_left_Ioi' (qKernel θ · x) 1 ha
  simp only [mul_one, smul_eq_mul] at ht
  unfold sizeTailKernel
  rw [← ht]
  have heq : (∫ s in Set.Ioi (1 : ℝ), qKernel θ (a * s) x) =
      a⁻¹ * ∫ s in Set.Ioi (1 : ℝ), qKernel θ s (x * a ^ (-(1 / θ))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact qKernel_mul_time ha (lt_trans zero_lt_one hs)
  rw [heq, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

private theorem qKernel_power {θ s x : ℝ} (hs : 0 < s) :
    qKernel θ s x = x * s ^ (-1 - 1 / θ) *
      Scalar.stableDensity θ (-(x * s ^ (-(1 / θ)))) := by
  rw [show -1 - 1 / θ = -1 + -(1 / θ) by ring, Real.rpow_add hs]
  simp only [qKernel, pDens, neg_mul, Real.rpow_neg_one, div_eq_mul_inv]
  ring

private theorem qKernel_integrable {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    IntegrableOn (qKernel θ · x) (Set.Ioi (1 : ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  have hρ : 0 < 1 / θ := by have := hθ.1; positivity
  have hc : ContinuousOn (qKernel θ · x) (Set.Ioi (1 : ℝ)) := by
    apply ContinuousOn.congr
      (((continuousOn_const.mul (continuousOn_id.rpow_const (fun s hs =>
        Or.inl (ne_of_gt (lt_trans zero_lt_one hs))))).mul
        ((Scalar.continuous_stableDensity hθ).comp_continuousOn
          ((continuousOn_const.mul (continuousOn_id.rpow_const (fun s hs =>
            Or.inl (ne_of_gt (lt_trans zero_lt_one hs))))).neg))))
    intro s hs
    exact qKernel_power (lt_trans zero_lt_one hs)
  refine ((integrableOn_Ioi_rpow_of_lt (by linarith : -1 - 1 / θ < -1)
    zero_lt_one).const_mul (|x| * M)).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [qKernel_power (lt_trans zero_lt_one hs), Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one hs) _)]
  calc |x| * s ^ (-1 - 1 / θ) * |Scalar.stableDensity θ (-(x * s ^ (-(1 / θ))))| ≤
      |x| * s ^ (-1 - 1 / θ) * M := mul_le_mul_of_nonneg_left (hbound _) (mul_nonneg (abs_nonneg x) (Real.rpow_nonneg (lt_trans zero_lt_one hs).le _))
    _ = |x| * M * s ^ (-1 - 1 / θ) := by ring

theorem sizeTailKernel_eq_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ} (hx : 0 ≤ x) :
    sizeTailKernel θ 1 x = θ * ∫ u in (0 : ℝ)..x, Scalar.stableDensity θ (-u) := by
  have _ := hx
  let f : ℝ → ℝ := fun u => Scalar.stableDensity θ (-u)
  let F : ℝ → ℝ := fun s => θ * ∫ u in (0 : ℝ)..(x * s ^ (-(1 / θ))), f u
  have hf : Continuous f := (Scalar.continuous_stableDensity hθ).comp continuous_neg
  have hF (s : ℝ) (hs : 1 ≤ s) : HasDerivAt F (-qKernel θ s x) s := by
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hp := (Real.hasDerivAt_rpow_const (p := -(1 / θ)) (Or.inl hs0.ne')).const_mul x
    have hprim := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 (x * s ^ (-(1 / θ))))
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    have hd := (hprim.comp s hp).const_mul θ
    change HasDerivAt F _ s at hd
    convert hd using 1
    rw [qKernel_power hs0]
    dsimp [f]
    have hθ0 : θ ≠ 0 := by linarith [hθ.1]
    rw [show -(1 / θ) - 1 = -1 - 1 / θ by ring]
    field_simp
  have hprim0 : ContinuousAt (fun v : ℝ => ∫ u in (0 : ℝ)..v, f u) 0 :=
    (intervalIntegral.differentiable_integral_of_continuous hf 0).continuousAt
  have hp0 : Tendsto (fun s : ℝ => x * s ^ (-(1 / θ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_rpow_neg_atTop
      (by have := hθ.1; positivity : 0 < 1 / θ)))
  have hlim : Tendsto F atTop (𝓝 0) := by
    have ht := (hprim0.tendsto.comp hp0).const_mul θ
    simpa [F] using ht
  have ht := integral_Ioi_of_hasDerivAt_of_tendsto' hF (qKernel_integrable hθ x).neg hlim
  change (∫ s in Set.Ioi (1 : ℝ), qKernel θ s x) = θ * ∫ u in (0 : ℝ)..x, f u
  simpa only [F, Real.one_rpow, mul_one, integral_neg, zero_sub, neg_inj] using ht

theorem sizeTailKernel_lipschitz {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |sizeTailKernel θ 1 x - sizeTailKernel θ 1 y| ≤ L * |x - y| := by
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  have hf : Continuous (fun u => Scalar.stableDensity θ (-u)) :=
    (Scalar.continuous_stableDensity hθ).comp continuous_neg
  refine ⟨θ * M, mul_nonneg (by linarith [hθ.1]) hM, ?_⟩
  intro x y hx hy
  rw [sizeTailKernel_eq_integral hθ hx, sizeTailKernel_eq_integral hθ hy,
    ← mul_sub, abs_mul, abs_of_pos (by linarith [hθ.1] : 0 < θ),
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have hb : |∫ u in y..x, Scalar.stableDensity θ (-u)| ≤ M * |x - y| := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := y) (b := x) (C := M) (f := fun u => Scalar.stableDensity θ (-u)) (fun u _ => by simpa only [Real.norm_eq_abs] using hbound (-u)))
  calc θ * |∫ u in y..x, Scalar.stableDensity θ (-u)| ≤ θ * (M * |x - y|) :=
      mul_le_mul_of_nonneg_left hb (by linarith [hθ.1])
    _ = θ * M * |x - y| := by ring

private theorem measurableSet_forestSize (j p : ℕ) : MeasurableSet (forestSizeEvent j p) := by
  have hc : (forestSizeEvent j p).Countable :=
    (Set.countable_range (fun ts : Fin j → PlaneTree => fun i => (ts i).toLocallyFinite)).mono (by
      rintro F ⟨ts, _, hF⟩
      exact ⟨ts, hF.symm⟩)
  exact hc.measurableSet

private theorem forestSize_disjoint (j : ℕ) : Pairwise (Function.onFun Disjoint (forestSizeEvent j)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro F ⟨ts, hts, hF⟩ ⟨us, hus, hG⟩
  have heq : ts = us := by
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun (hF.symm.trans hG) i)
  exact hpq (hts.symm.trans (heq ▸ hus))

private theorem inverse_tail_bound {ρ : ℝ} {a : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (∑' p : ℕ, if n ≤ p then 1 / ((p : ℝ) * a p) else 0) ≤ C / a n := by
  obtain ⟨C, hC, hb⟩ := hrv.karamata_tail_tsum hmono hpos hρ
  refine ⟨C + 1, fun n hn => ?_⟩
  let f : ℕ → ℝ := fun p => 1 / ((p : ℝ) * a p)
  have hs : Summable f := hrv.summable_inv_mul hmono hpos hρ
  have hi : Summable ((Set.Ioi n).indicator f) := hs.indicator _
  have heq : (fun p => if n ≤ p then f p else 0) =
      (fun p => if p = n then f n else 0) + (Set.Ioi n).indicator f := by
    funext p
    by_cases hpn : p = n
    · subst p; simp
    · by_cases hnp : n ≤ p
      · have hlt : n < p := by omega
        simp [hpn, hnp, Set.indicator, hlt]
      · have hlt : ¬n < p := by omega
        simp [hpn, hnp, Set.indicator, hlt]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have han := hpos n hn
  change (∑' p, if n ≤ p then f p else 0) ≤ _
  rw [heq]
  change (∑' p : ℕ, ((if p = n then f n else 0) + (Set.Ioi n).indicator f p)) ≤ _
  rw [Summable.tsum_add (hasSum_ite_eq n (f n)).summable hi]
  simp only [tsum_ite_eq]
  have hfirst : f n ≤ 1 / a n := by
    dsimp [f]
    apply one_div_le_one_div_of_le han
    nlinarith
  calc f n + ∑' p, (Set.Ioi n).indicator f p ≤ 1 / a n + C / a n :=
        add_le_add hfirst (hb n hn)
    _ = (C + 1) / a n := by ring

/-- An absolutely summable discrete tail as an integral of its floor-step extension. -/
private theorem step_tail_integral {n : ℕ} (hn : 1 ≤ n) {f : ℕ → ℝ} (hf : Summable f) :
    IntegrableOn (fun s : ℝ => f ⌊(n : ℝ) * s⌋₊) (Ioi 1) ∧
    (∫ s in Ioi (1 : ℝ), f ⌊(n : ℝ) * s⌋₊) = (1 / (n : ℝ)) * ∑' k : ℕ, f (n + k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let S : ℕ → Set ℝ := fun k => Ico (((n + k : ℕ) : ℝ) / n) (((n + k + 1 : ℕ) : ℝ) / n)
  have hfloor (k : ℕ) {s : ℝ} (hs : s ∈ S k) : ⌊(n : ℝ) * s⌋₊ = n + k := by
    have hlow : ((n + k : ℕ) : ℝ) ≤ (n : ℝ) * s := by
      have := (div_le_iff₀ hnR).mp hs.1
      nlinarith
    have hhigh : (n : ℝ) * s < ((n + k + 1 : ℕ) : ℝ) := by
      have := (lt_div_iff₀ hnR).mp hs.2
      nlinarith
    exact (Nat.floor_eq_iff (hlow.trans' (by positivity))).mpr ⟨hlow, by exact_mod_cast hhigh⟩
  have hunion : (⋃ k, S k) = Ici (1 : ℝ) := by
    ext s
    constructor
    · intro hs
      obtain ⟨k, hk⟩ := mem_iUnion.mp hs
      have hkn : (1 : ℝ) ≤ ((n + k : ℕ) : ℝ) / n := by
        rw [le_div_iff₀ hnR]
        norm_cast
        omega
      exact hkn.trans hk.1
    · intro hs
      change 1 ≤ s at hs
      have hns : (n : ℝ) ≤ (n : ℝ) * s := by nlinarith
      have hp : n ≤ ⌊(n : ℝ) * s⌋₊ := Nat.le_floor hns
      refine mem_iUnion.mpr ⟨⌊(n : ℝ) * s⌋₊ - n, ?_⟩
      dsimp [S]
      rw [Nat.add_sub_of_le hp]
      constructor
      · rw [div_le_iff₀ hnR]
        nlinarith [Nat.floor_le (by positivity : 0 ≤ (n : ℝ) * s)]
      · rw [lt_div_iff₀ hnR]
        have := Nat.lt_floor_add_one ((n : ℝ) * s)
        push_cast
        nlinarith
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro s hks hls
    have := (hfloor k hks).symm.trans (hfloor l hls)
    omega
  have hconst (k : ℕ) : Set.EqOn (fun s : ℝ => f ⌊(n : ℝ) * s⌋₊) (fun _ => f (n + k)) (S k) := by
    intro s hs
    change f ⌊(n : ℝ) * s⌋₊ = f (n + k)
    rw [hfloor k hs]
  have hmeasure (k : ℕ) : volume.real (S k) = 1 / (n : ℝ) := by
    dsimp [S]
    rw [Real.volume_real_Ico]
    have hsub : (((n + k + 1 : ℕ) : ℝ) / n - ((n + k : ℕ) : ℝ) / n) = 1 / (n : ℝ) := by
      push_cast
      ring
    rw [hsub, max_eq_left (by positivity)]
  have hint (k : ℕ) : IntegrableOn (fun s : ℝ => f ⌊(n : ℝ) * s⌋₊) (S k) := by
    apply IntegrableOn.congr_fun (integrableOn_const (by dsimp [S]; exact measure_Ico_lt_top.ne))
      (fun s hs => (hconst k hs).symm) measurableSet_Ico
  have hval (k : ℕ) : (∫ s in S k, f ⌊(n : ℝ) * s⌋₊) = (1 / (n : ℝ)) * f (n + k) := by
    rw [setIntegral_congr_fun measurableSet_Ico (hconst k), integral_const,
      measureReal_restrict_apply_univ, smul_eq_mul, hmeasure]
  have hnorm (k : ℕ) : (∫ s in S k, ‖f ⌊(n : ℝ) * s⌋₊‖) = (1 / (n : ℝ)) * ‖f (n + k)‖ := by
    rw [setIntegral_congr_fun measurableSet_Ico (fun s hs => congrArg norm (hconst k hs)),
      integral_const, measureReal_restrict_apply_univ, smul_eq_mul, hmeasure]
  have hs : Summable (fun k : ℕ => ‖f (n + k)‖) := by
    simpa only [Nat.add_comm n] using (summable_nat_add_iff n).mpr hf.norm
  have hi : IntegrableOn (fun s : ℝ => f ⌊(n : ℝ) * s⌋₊) (Ici 1) := by
    rw [← hunion]
    apply integrableOn_iUnion_of_summable_integral_norm hint
    simpa only [hnorm] using hs.mul_left (1 / (n : ℝ))
  refine ⟨hi.mono_set Ioi_subset_Ici_self, ?_⟩
  rw [← integral_Ici_eq_integral_Ioi, ← hunion, integral_iUnion (fun _ => measurableSet_Ico) hdisj
    (by rwa [hunion]), ← tsum_mul_left]
  apply tsum_congr
  exact hval

/-- Integer-part bounds on the rescaled time grid, uniform for `s ≥ 1`. -/
private theorem floor_time_bounds {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 1 ≤ s) :
    n ≤ ⌊(n : ℝ) * s⌋₊ ∧
      0 < (⌊(n : ℝ) * s⌋₊ : ℝ) ∧
      (s / 2) ≤ (⌊(n : ℝ) * s⌋₊ : ℝ) / n ∧
      (0 : ℝ) ≤ (n : ℝ) / ⌊(n : ℝ) * s⌋₊ ∧
      (n : ℝ) / ⌊(n : ℝ) * s⌋₊ ≤ 2 / s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsR : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hns : (n : ℝ) ≤ (n : ℝ) * s := by nlinarith
  have hpn : n ≤ ⌊(n : ℝ) * s⌋₊ := Nat.le_floor hns
  have hp1 : (1 : ℝ) ≤ ⌊(n : ℝ) * s⌋₊ := by exact_mod_cast hn.trans hpn
  have hfloor := Nat.lt_floor_add_one ((n : ℝ) * s)
  have hhalf : (n : ℝ) * s ≤ 2 * ⌊(n : ℝ) * s⌋₊ := by linarith
  refine ⟨hpn, by linarith, ?_, div_nonneg hnR.le (by linarith), ?_⟩
  · rw [le_div_iff₀ hnR]
    nlinarith
  · rw [div_le_div_iff₀ (by linarith) hsR]
    nlinarith

/-- The Potter majorant for the inverse norming on the time grid. -/
private theorem floor_ratio_domination {ρ : ℝ} {a : ℕ → ℝ} (hρ : 0 < ρ)
    (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, 1 ≤ s →
      0 ≤ a n / a ⌊(n : ℝ) * s⌋₊ ∧
      a n / a ⌊(n : ℝ) * s⌋₊ ≤ 1 ∧
      a n / a ⌊(n : ℝ) * s⌋₊ ≤ D * s ^ (-(ρ / 2)) := by
  obtain ⟨C, hC, hb⟩ := hrv.exists_potter_global hmono hpos hρ.le (half_pos hρ)
  refine ⟨C * (2 : ℝ) ^ (ρ / 2), by positivity, fun n hn s hs => ?_⟩
  obtain ⟨hpn, hpR, hhalf, _, _⟩ := floor_time_bounds hn hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsR : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have han := hpos n hn
  have hap := hpos _ (hn.trans hpn)
  have hpow : 0 < ((⌊(n : ℝ) * s⌋₊ : ℝ) / n) ^ (ρ / 2) := by positivity
  have hpot := (hb n ⌊(n : ℝ) * s⌋₊ hn hpn).2
  rw [show ρ - ρ / 2 = ρ / 2 by ring] at hpot
  have hratio : a n / a ⌊(n : ℝ) * s⌋₊ ≤
      C * ((⌊(n : ℝ) * s⌋₊ : ℝ) / n) ^ (-(ρ / 2)) := by
    rw [Real.rpow_neg (by positivity), div_le_iff₀ hap]
    have hd : a n ≤ C * a ⌊(n : ℝ) * s⌋₊ /
        ((⌊(n : ℝ) * s⌋₊ : ℝ) / n) ^ (ρ / 2) := by
      rw [le_div_iff₀ hpow]
      nlinarith [hpot]
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hd
  refine ⟨div_nonneg han.le hap.le, (div_le_one hap).mpr (hmono hpn), ?_⟩
  calc a n / a ⌊(n : ℝ) * s⌋₊
      ≤ C * ((⌊(n : ℝ) * s⌋₊ : ℝ) / n) ^ (-(ρ / 2)) := hratio
    _ ≤ C * (s / 2) ^ (-(ρ / 2)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)) hC.le
    _ = (C * (2 : ℝ) ^ (ρ / 2)) * s ^ (-(ρ / 2)) := by
      rw [Real.div_rpow hsR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have ht : (2 : ℝ) ^ (ρ / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      field_simp

/-- The density error is uniform in its bounded spatial argument. -/
private theorem density_coefficient_error {θ α M : ℝ} {K : ℝ≥0}
    (_hM : 0 ≤ M) (hbound : ∀ z, |Scalar.stableDensity θ z| ≤ M)
    (hLip : LipschitzWith K (Scalar.stableDensity θ))
    {x t r b v : ℝ} (hx : 0 ≤ x) (hxα : x ≤ α) (hb : 0 ≤ b) (hv : 0 ≤ v) :
    |x * t * r * Scalar.stableDensity θ (-(x * r)) -
      x * (b * v) * Scalar.stableDensity θ (-(x * v))| ≤
      α * M * |t * r - b * v| + α ^ 2 * (K : ℝ) * (b * v) * |r - v| := by
  have hd : |Scalar.stableDensity θ (-(x * r)) - Scalar.stableDensity θ (-(x * v))| ≤
      (K : ℝ) * x * |r - v| := by
    have hh := hLip.dist_le_mul (-(x * r)) (-(x * v))
    rw [Real.dist_eq, Real.dist_eq, neg_sub_neg, ← mul_sub, abs_mul, abs_of_nonneg hx,
      abs_sub_comm v r] at hh
    simpa only [mul_assoc] using hh
  have hα : 0 ≤ α := hx.trans hxα
  calc
    |x * t * r * Scalar.stableDensity θ (-(x * r)) -
        x * (b * v) * Scalar.stableDensity θ (-(x * v))| =
      |x * (t * r - b * v) * Scalar.stableDensity θ (-(x * r)) +
        x * (b * v) * (Scalar.stableDensity θ (-(x * r)) - Scalar.stableDensity θ (-(x * v)))| := by
          congr 1; ring
    _ ≤ |x * (t * r - b * v) * Scalar.stableDensity θ (-(x * r))| +
        |x * (b * v) * (Scalar.stableDensity θ (-(x * r)) - Scalar.stableDensity θ (-(x * v)))| := abs_add_le _ _
    _ = x * |t * r - b * v| * |Scalar.stableDensity θ (-(x * r))| +
        x * (b * v) * |Scalar.stableDensity θ (-(x * r)) - Scalar.stableDensity θ (-(x * v))| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hx,
            abs_of_nonneg (mul_nonneg hb hv)]
    _ ≤ α * |t * r - b * v| * M + α * (b * v) * ((K : ℝ) * α * |r - v|) := by
      gcongr
      · exact hbound _
      · exact hd.trans (by gcongr)
    _ = α * M * |t * r - b * v| + α ^ 2 * (K : ℝ) * (b * v) * |r - v| := by ring

private noncomputable def gridTime (n : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ) / ⌊(n : ℝ) * s⌋₊

private noncomputable def gridScale (a : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  a n / a ⌊(n : ℝ) * s⌋₊

private noncomputable def gridError (θ α M : ℝ) (K : ℝ≥0) (a : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  α * M * |gridTime n s * gridScale a n s - s ^ (-1 - 1 / θ)| +
    α ^ 2 * (K : ℝ) * s ^ (-1 - 1 / θ) * |gridScale a n s - s ^ (-(1 / θ))|

private theorem gridError_measurable (θ α M : ℝ) (K : ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    Measurable (gridError θ α M K a n) := by
  have hp : Measurable (fun s : ℝ => ⌊(n : ℝ) * s⌋₊) :=
    Nat.measurable_floor.comp (measurable_const.mul measurable_id)
  have ht : Measurable (gridTime n) :=
    measurable_const.div ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hp)
  have hr : Measurable (gridScale a n) :=
    measurable_const.div ((measurable_of_countable a).comp hp)
  have hP : Measurable (fun s : ℝ => s ^ (-1 - 1 / θ)) := measurable_id.pow_const _
  have hV : Measurable (fun s : ℝ => s ^ (-(1 / θ))) := measurable_id.pow_const _
  have hA : Measurable (fun s => |gridTime n s * gridScale a n s - s ^ (-1 - 1 / θ)|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.mul_apply] using ((ht.mul hr).sub hP).norm
  have hB : Measurable (fun s => |gridScale a n s - s ^ (-(1 / θ))|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hr.sub hV).norm
  exact (hA.const_mul (α * M)).add ((hP.const_mul (α ^ 2 * (K : ℝ))).mul hB)

/-- A single integrable majorant for all bounded spatial arguments. -/
private theorem gridError_majorant {θ α M : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (K : ℝ≥0) {a : ℕ → ℝ}
    (hmono : Monotone a) (hpos : ∀ n, 1 ≤ n → 0 < a n)
    (hrv : RegularlyVaryingSeq (1 / θ) a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, 1 ≤ s →
      ‖gridError θ α M K a n s‖ ≤ C * s ^ (-1 - 1 / θ / 2) := by
  have hρ : 0 < 1 / θ := by have := hθ.1; positivity
  obtain ⟨D, hD, hb⟩ := floor_ratio_domination hρ hrv hmono hpos
  let C : ℝ := α * M * (2 * D + 1) + 2 * α ^ 2 * (K : ℝ)
  refine ⟨C, by dsimp [C]; positivity, fun n hn s hs => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  obtain ⟨_, _, _, ht0, ht⟩ := floor_time_bounds hn hs
  obtain ⟨hr0, hr1, hr⟩ := hb n hn s hs
  change 0 ≤ gridTime n s at ht0
  change gridTime n s ≤ 2 / s at ht
  change 0 ≤ gridScale a n s at hr0
  change gridScale a n s ≤ 1 at hr1
  change gridScale a n s ≤ D * s ^ (-(1 / θ / 2)) at hr
  have hp0 : 0 ≤ s ^ (-1 - 1 / θ) := Real.rpow_nonneg hs0.le _
  have hv0 : 0 ≤ s ^ (-(1 / θ)) := Real.rpow_nonneg hs0.le _
  have hv1 : s ^ (-(1 / θ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have hP : s ^ (-1 - 1 / θ) ≤ s ^ (-1 - 1 / θ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have htr : gridTime n s * gridScale a n s ≤
      2 * D * s ^ (-1 - 1 / θ / 2) := by
    calc _ ≤ (2 / s) * (D * s ^ (-(1 / θ / 2))) := mul_le_mul ht hr hr0 (by positivity)
      _ = 2 * D * s ^ (-1 - 1 / θ / 2) := by
        rw [show -1 - 1 / θ / 2 = -1 + -(1 / θ / 2) by ring, Real.rpow_add hs0,
          Real.rpow_neg_one]
        ring
  have herr1 : |gridTime n s * gridScale a n s - s ^ (-1 - 1 / θ)| ≤
      (2 * D + 1) * s ^ (-1 - 1 / θ / 2) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg ht0 hr0]
  have herr2 : |gridScale a n s - s ^ (-(1 / θ))| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have he0 : 0 ≤ gridError θ α M K a n s := by unfold gridError; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg he0]
  unfold gridError
  calc
    _ ≤ α * M * ((2 * D + 1) * s ^ (-1 - 1 / θ / 2)) +
        α ^ 2 * (K : ℝ) * s ^ (-1 - 1 / θ / 2) * 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left herr1 (mul_nonneg hα hM)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hP (by positivity)) herr2
          (abs_nonneg _) (by positivity)
    _ = C * s ^ (-1 - 1 / θ / 2) := by dsimp [C]; ring

/-- Dominated convergence for the scalar error majorizing the supremum over `x`. -/
private theorem gridError_integral_tendsto {θ α M : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (K : ℝ≥0) {a : ℕ → ℝ}
    (hmono : Monotone a) (hpos : ∀ n, 1 ≤ n → 0 < a n)
    (hrv : RegularlyVaryingSeq (1 / θ) a)
    (hratio : ∀ s : ℝ, 0 < s →
      Tendsto (fun n : ℕ => a ⌊s * (n : ℝ)⌋₊ / a n) atTop (𝓝 (s ^ (1 / θ)))) :
    Tendsto (fun n : ℕ => ∫ s in Ioi (1 : ℝ), gridError θ α M K a n s) atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → IntegrableOn (gridError θ α M K a n) (Ioi (1 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := gridError_majorant hθ hα hM K hmono hpos hrv
  have hρ : 0 < 1 / θ := by have := hθ.1; positivity
  have hi : IntegrableOn (fun s : ℝ => C * s ^ (-1 - 1 / θ / 2)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul C
  have hmeas (n : ℕ) : AEStronglyMeasurable (gridError θ α M K a n)
      (volume.restrict (Ioi (1 : ℝ))) :=
    (gridError_measurable θ α M K a n).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ s ∂volume.restrict (Ioi (1 : ℝ)),
      ‖gridError θ α M K a n s‖ ≤ C * s ^ (-1 - 1 / θ / 2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hb n hn s hs.le
  have hlim : ∀ᵐ s ∂volume.restrict (Ioi (1 : ℝ)),
      Tendsto (fun n : ℕ => gridError θ α M K a n s) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans zero_lt_one hs
    have ht : Tendsto (fun n : ℕ => gridTime n s) atTop (𝓝 (s⁻¹)) := by
      have hh := ((tendsto_nat_floor_mul_div_atTop hs0.le).comp tendsto_natCast_atTop_atTop).inv₀ hs0.ne'
      simpa only [gridTime, Function.comp_apply, inv_div, mul_comm s] using hh
    have hr : Tendsto (fun n : ℕ => gridScale a n s) atTop (𝓝 (s ^ (-(1 / θ)))) := by
      have hh := (hratio s hs0).inv₀ (Real.rpow_pos_of_pos hs0 _).ne'
      simpa only [gridScale, inv_div, Real.rpow_neg hs0.le, mul_comm s] using hh
    have hprod : s⁻¹ * s ^ (-(1 / θ)) = s ^ (-1 - 1 / θ) := by
      rw [show -1 - 1 / θ = -1 + -(1 / θ) by ring, Real.rpow_add hs0, Real.rpow_neg_one]
    have hfirst := (((ht.mul hr).sub_const (s ^ (-1 - 1 / θ))).abs).const_mul (α * M)
    have hsecond := ((hr.sub_const (s ^ (-(1 / θ)))).abs).const_mul
      (α ^ 2 * (K : ℝ) * s ^ (-1 - 1 / θ))
    simpa only [gridError, hprod, sub_self, abs_zero, mul_zero, add_zero] using hfirst.add hsecond
  constructor
  · have hh := tendsto_integral_filter_of_dominated_convergence
      (fun s : ℝ => C * s ^ (-1 - 1 / θ / 2))
      (Eventually.of_forall hmeas) hbound hi hlim
    simpa only [integral_zero] using hh
  · intro n hn
    apply hi.mono' (hmeas n)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hb n hn s hs.le

private noncomputable def densityTerm (θ : ℝ) (a : ℕ → ℝ) (z : ℝ) (p : ℕ) : ℝ :=
  (z / p) * (1 / a p) * Scalar.stableDensity θ (-(z / a p))

private theorem densityTerm_summable {θ : ℝ} {a : ℕ → ℝ}
    (hpos : ∀ n, 1 ≤ n → 0 < a n)
    (hs : Summable (fun p : ℕ => 1 / ((p : ℝ) * a p))) (z : ℝ) :
    Summable (densityTerm θ a z) := by
  obtain ⟨M, hM, hb⟩ := Scalar.exists_stableDensity_le (α := θ)
  apply (hs.mul_left (|z| * M)).of_norm_bounded
  intro p
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [densityTerm]
  have hap := hpos p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have heq : densityTerm θ a z p =
      z * (1 / ((p : ℝ) * a p)) * Scalar.stableDensity θ (-(z / a p)) := by
    simp only [densityTerm, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / ((p : ℝ) * a p))]
  calc |z| * (1 / ((p : ℝ) * a p)) * |Scalar.stableDensity θ (-(z / a p))|
      ≤ |z| * (1 / ((p : ℝ) * a p)) * M :=
        mul_le_mul_of_nonneg_left (hb _) (by positivity)
    _ = (|z| * M) * (1 / ((p : ℝ) * a p)) := by ring

private theorem tsum_tail_eq_shift {f : ℕ → ℝ} (hf : Summable f) (n : ℕ) :
    (∑' p : ℕ, if n ≤ p then f p else 0) = ∑' k : ℕ, f (n + k) := by
  let g : ℕ → ℝ := fun p => if n ≤ p then f p else 0
  have hg : Summable g := by
    apply (hf.indicator (Ici n)).congr
    intro p
    simp [g, Set.indicator]
  have hz : ∑ k ∈ Finset.range n, g k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn := Finset.mem_range.mp hk
    simp [g, not_le.mpr hkn]
  calc
    (∑' p : ℕ, if n ≤ p then f p else 0) = ∑' k : ℕ, g (k + n) := by
      simpa only [hz, zero_add] using (hg.sum_add_tsum_nat_add n).symm
    _ = ∑' k : ℕ, f (n + k) := by
      apply tsum_congr
      intro k
      simp [g, Nat.add_comm]

private theorem densityTerm_tail_integral {θ : ℝ} {a : ℕ → ℝ}
    (hpos : ∀ n, 1 ≤ n → 0 < a n)
    (hs : Summable (fun p : ℕ => 1 / ((p : ℝ) * a p)))
    {n : ℕ} (hn : 1 ≤ n) (z : ℝ) :
    IntegrableOn (fun s : ℝ => (n : ℝ) * densityTerm θ a z ⌊(n : ℝ) * s⌋₊) (Ioi 1) ∧
      (∑' p : ℕ, if n ≤ p then densityTerm θ a z p else 0) =
        ∫ s in Ioi (1 : ℝ), (n : ℝ) * densityTerm θ a z ⌊(n : ℝ) * s⌋₊ := by
  have hf := densityTerm_summable (θ := θ) hpos hs z
  obtain ⟨hi, he⟩ := step_tail_integral hn hf
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, he, ← mul_assoc, one_div,
    mul_inv_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_mul, tsum_tail_eq_shift hf n]

private theorem densityTerm_grid {θ : ℝ} {a : ℕ → ℝ} (n : ℕ) (s x : ℝ) :
    (n : ℝ) * densityTerm θ a (x * a n) ⌊(n : ℝ) * s⌋₊ =
      x * gridTime n s * gridScale a n s *
        Scalar.stableDensity θ (-(x * gridScale a n s)) := by
  simp only [densityTerm, gridTime, gridScale, div_eq_mul_inv, one_mul]
  ring_nf

private theorem densityTerm_grid_error {θ α M : ℝ} {K : ℝ≥0}
    (hM : 0 ≤ M) (hbound : ∀ z, |Scalar.stableDensity θ z| ≤ M)
    (hLip : LipschitzWith K (Scalar.stableDensity θ))
    {a : ℕ → ℝ} (n : ℕ) {s x : ℝ} (hs : 1 < s) (hx : 0 ≤ x) (hxα : x ≤ α) :
    ‖(n : ℝ) * densityTerm θ a (x * a n) ⌊(n : ℝ) * s⌋₊ - qKernel θ s x‖ ≤
      gridError θ α M K a n s := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hprod : s⁻¹ * s ^ (-(1 / θ)) = s ^ (-1 - 1 / θ) := by
    rw [show -1 - 1 / θ = -1 + -(1 / θ) by ring, Real.rpow_add hs0, Real.rpow_neg_one]
  rw [densityTerm_grid, qKernel_power hs0, Real.norm_eq_abs]
  have hh := density_coefficient_error hM hbound hLip hx hxα
    (inv_nonneg.mpr hs0.le) (Real.rpow_nonneg hs0.le (-(1 / θ)))
    (t := gridTime n s) (r := gridScale a n s)
  simpa only [hprod, gridError] using hh

/-- The weighted regularly varying Riemann tail, uniformly for a real spatial argument. -/
private theorem density_riemann_uniform {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ θ a) {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℝ, 0 ≤ x → x ≤ α →
      |(∑' p : ℕ, if n ≤ p then densityTerm θ a (x * a n) p else 0) -
        sizeTailKernel θ 1 x| ≤ ε := by
  obtain ⟨M, hM, hb⟩ := Scalar.exists_stableDensity_le (α := θ)
  obtain ⟨K, hLip⟩ : ∃ K : ℝ≥0, LipschitzWith K (Scalar.stableDensity θ) :=
    ⟨_, Scalar.lipschitzWith_stableDensity h.alpha_mem⟩
  have hrv := Scalar.regularlyVaryingSeq h
  have hratio : ∀ s : ℝ, 0 < s →
      Tendsto (fun n : ℕ => a ⌊s * (n : ℝ)⌋₊ / a n) atTop (𝓝 (s ^ (1 / θ))) := by
    intro s hs
    have ha := stableDomain_isStableAttracted h
    exact TransformConvergence.tendsto_div_of_tendsto_div' (stepLaw μ) ha ha hs
      ((tendsto_nat_floor_mul_div_atTop hs.le).comp tendsto_natCast_atTop_atTop)
  obtain ⟨ht, hi⟩ := gridError_integral_tendsto h.alpha_mem hα.le hM K h.monotone h.pos hrv hratio
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨max N 1, fun n hn x hx hxα => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hs := hrv.summable_inv_mul h.monotone h.pos (by have := h.alpha_mem.1; positivity)
  obtain ⟨hfi, hfeq⟩ := densityTerm_tail_integral h.pos hs hn1 (x * a n)
  rw [hfeq, sizeTailKernel, ← integral_sub hfi (qKernel_integrable h.alpha_mem x)]
  have hbound : ∀ᵐ s ∂volume.restrict (Ioi (1 : ℝ)),
      ‖(n : ℝ) * densityTerm θ a (x * a n) ⌊(n : ℝ) * s⌋₊ - qKernel θ s x‖ ≤
        gridError θ α M K a n s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact densityTerm_grid_error hM hb hLip n hs hx hxα
  have hh := norm_integral_le_of_norm_le (hi n hn1) hbound
  have hsmall : |∫ s in Ioi (1 : ℝ), gridError θ α M K a n s| ≤ ε := by
    simpa only [Real.dist_eq, sub_zero] using (hN n hnN).le
  apply le_trans _ ((le_abs_self _).trans hsmall)
  simpa only [Real.norm_eq_abs] using hh

/-- Summing a uniform local-limit error against the Kemperman weights. -/
private theorem weighted_llt_error {ν : Measure ℤ} {θ δ : ℝ} {a : ℕ → ℝ}
    {n j : ℕ} (hn : 1 ≤ n) (hδ : 0 ≤ δ)
    (hpos : ∀ p, n ≤ p → 0 < a p)
    (hs : Summable (fun p : ℕ => if n ≤ p then 1 / ((p : ℝ) * a p) else 0))
    (hllt : ∀ p, n ≤ p →
      |a p * intWalkProb ν p (-(j : ℤ)) - Scalar.stableDensity θ (-((j : ℝ) / a p))| ≤ δ) :
    |(∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * intWalkProb ν p (-(j : ℤ)) else 0) -
      (∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * (1 / a p) *
        Scalar.stableDensity θ (-((j : ℝ) / a p)) else 0)| ≤
      δ * j * ∑' p : ℕ, if n ≤ p then 1 / ((p : ℝ) * a p) else 0 := by
  have _ := hδ
  let w : ℕ → ℝ := fun p => if n ≤ p then 1 / ((p : ℝ) * a p) else 0
  let f : ℕ → ℝ := fun p => if n ≤ p then
    ((j : ℝ) / p) * intWalkProb ν p (-(j : ℤ)) else 0
  let g : ℕ → ℝ := fun p => if n ≤ p then ((j : ℝ) / p) * (1 / a p) *
    Scalar.stableDensity θ (-((j : ℝ) / a p)) else 0
  have hw (p : ℕ) : 0 ≤ w p := by
    dsimp [w]
    split_ifs with hp
    · exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hpos p hp).le)
    · exact le_rfl
  have hd (p : ℕ) : ‖f p - g p‖ ≤ (δ * j) * w p := by
    by_cases hp : n ≤ p
    · have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      have haR := (hpos p hp).ne'
      have heq : f p - g p = ((j : ℝ) * w p) *
          (a p * intWalkProb ν p (-(j : ℤ)) - Scalar.stableDensity θ (-((j : ℝ) / a p))) := by
        dsimp [f, g, w]
        simp only [hp, ite_true]
        field_simp
      rw [heq, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg j) (hw p))]
      calc (j : ℝ) * w p * |a p * intWalkProb ν p (-(j : ℤ)) -
          Scalar.stableDensity θ (-((j : ℝ) / a p))| ≤ (j : ℝ) * w p * δ :=
            mul_le_mul_of_nonneg_left (hllt p hp) (mul_nonneg (Nat.cast_nonneg j) (hw p))
        _ = (δ * j) * w p := by ring
    · simp [f, g, w, hp]
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  have hg (p : ℕ) : ‖g p‖ ≤ ((j : ℝ) * M) * w p := by
    by_cases hp : n ≤ p
    · have heq : g p = ((j : ℝ) * w p) * Scalar.stableDensity θ (-((j : ℝ) / a p)) := by
        simp only [g, w, hp, ite_true, mul_inv_rev, div_eq_mul_inv]
        ring
      rw [heq, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg j) (hw p))]
      calc (j : ℝ) * w p * |Scalar.stableDensity θ (-((j : ℝ) / a p))| ≤
          (j : ℝ) * w p * M :=
            mul_le_mul_of_nonneg_left (hbound _) (mul_nonneg (Nat.cast_nonneg j) (hw p))
        _ = (j : ℝ) * M * w p := by ring
    · simp [g, w, hp]
  have hsD : Summable (fun p => f p - g p) := (hs.mul_left (δ * j)).of_norm_bounded hd
  have hsG : Summable g := (hs.mul_left ((j : ℝ) * M)).of_norm_bounded hg
  have hsF : Summable f := (hsD.add hsG).congr (fun p => sub_add_cancel _ _)
  have hb := (hsF.hasSum.sub hsG.hasSum).norm_le_of_bounded (hs.hasSum.mul_left (δ * j)) hd
  simpa only [Real.norm_eq_abs] using hb

set_option linter.unusedSectionVars false
section Htheta
variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

theorem sizeTailProb_eq_tsum {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    sizeTailProb μ n j =
      ∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * intWalkProb (stepLaw μ) p (-(j : ℤ)) else 0 := by
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure ≤ 1 := by
    rw [lintegral_countable']
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hc.le
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hae : ∀ᵐ F ∂forestLaw μ j, ∀ i, BGW.LocallyFinite.FiniteVertices (F i) := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin j => BGW.LocallyFinite.bienaymeLaw μ.toMeasure) (i := i)).eventually
      (BGW.LocallyFinite.ae_finiteVertices_bienaymeLaw μ.toMeasure hm hne')
  let E : ℕ → Set (Fin j → BGW.LocallyFinite.Tree) :=
    fun p => if n ≤ p then forestSizeEvent j p else ∅
  have hevent : forestSizeGeEvent j n =ᵐ[forestLaw μ j] ⋃ p, E p := by
    filter_upwards [hae] with F hF
    apply propext
    change ((∃ i, ¬ BGW.LocallyFinite.FiniteVertices (F i)) ∨
      ∃ p, F ∈ forestSizeEvent j p ∧ n ≤ p) ↔ F ∈ ⋃ p, E p
    simp only [not_exists.mpr (fun i => not_not.mpr (hF i)), false_or, Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp, hnp⟩
      exact ⟨p, by simpa [E, hnp] using hp⟩
    · rintro ⟨p, hp⟩
      by_cases hnp : n ≤ p
      · exact ⟨p, by simpa [E, hnp] using hp, hnp⟩
      · simp [E, hnp] at hp
  have hmeas (p : ℕ) : MeasurableSet (E p) := by
    dsimp [E]; split_ifs <;> simp [measurableSet_forestSize]
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro p q hpq
    change Disjoint (E p) (E q)
    dsimp [E]
    split_ifs <;> simp_all [forestSize_disjoint j hpq]
  unfold sizeTailProb
  rw [measureReal_congr hevent, measureReal_def, measure_iUnion hdisj hmeas,
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  apply tsum_congr
  intro p
  by_cases hnp : n ≤ p
  · simp only [E, hnp, ite_true]
    change (Measure.pi (fun _ : Fin j => BGW.LocallyFinite.bienaymeLaw μ.toMeasure)
      (forestSizeEvent j p)).toReal = _
    rw [kemperman_unmarked μ.toMeasure hj (hn.trans hnp), ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ← Scalar.walkLaw_neg_eq_pi_countForestBridges]
    simp only [intWalkProb, intWalk_stepLaw, measureReal_def]
  · simp [E, hnp]

theorem tailSum_bound :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑' p : ℕ, (if n ≤ p then 1 / ((p : ℝ) * norming (stepLaw μ) θ p) else 0) ≤
        C / norming (stepLaw μ) θ n := by
  obtain ⟨b, hb⟩ := hDA
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  have hm := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA').1
  rw [mean_stepLaw hc] at ha
  obtain ⟨a, heq, h⟩ := ha.exists_stableDomain hc hne hm
  obtain ⟨C, hC⟩ := inverse_tail_bound (by have := h.alpha_mem.1; positivity)
    (Scalar.regularlyVaryingSeq h) h.monotone h.pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 heq
  refine ⟨C, max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have ht := hC n hn1
  rw [hN n hnN] at ht
  convert ht using 1
  apply tsum_congr
  intro p
  split_ifs with hp
  · rw [hN p (hnN.trans hp)]
  · rfl

/-- Pointwise rescaling needed by the Riemann-sum argument. -/
private theorem norming_floor_ratio {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => norming (stepLaw μ) θ ⌊s * (n : ℝ)⌋₊ /
      norming (stepLaw μ) θ n) atTop (𝓝 (s ^ (1 / θ))) := by
  obtain ⟨b, hb⟩ := hDA
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  exact TransformConvergence.tendsto_div_of_tendsto_div' (stepLaw μ) ha ha hs
    ((tendsto_nat_floor_mul_div_atTop hs.le).comp tendsto_natCast_atTop_atTop)

/-- The local-limit replacement, before the Riemann-sum step. -/
private theorem sizeTail_llt {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j →
      (j : ℝ) ≤ α * norming (stepLaw μ) θ n →
      |sizeTailProb μ n j -
        (∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * (1 / norming (stepLaw μ) θ p) *
          Scalar.stableDensity θ (-((j : ℝ) / norming (stepLaw μ) θ p)) else 0)| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  have hmono := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA').1
  obtain ⟨Np, hp⟩ := ha.pos
  have ha0 : IsStableAttracted (stepLaw μ) θ 0 (norming (stepLaw μ) θ) := by
    simpa only [mean_stepLaw hc] using ha
  obtain ⟨a, heq, ha'⟩ := ha0.exists_stableDomain hc hne hmono
  have hs : Summable (fun p : ℕ => 1 / ((p : ℝ) * norming (stepLaw μ) θ p)) := by
    have hs' := (Scalar.regularlyVaryingSeq ha').summable_inv_mul ha'.monotone ha'.pos
      (by have := ha'.alpha_mem.1; positivity)
    apply hs'.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [heq] with p hp
    rw [hp]
  obtain ⟨C, Nc, hC⟩ := tailSum_bound hc hne hap ⟨b, hb⟩
  let D : ℝ := |C| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ : ℝ := ε / (α * D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Nl, hl⟩ := llt_abstract (stepLaw μ) (integrable_stepLaw hc)
    (nonLattice_stepLaw hc hne hap) hmono ha hδ
  refine ⟨max (max Nc Np) (max Nl 1), fun n hn j hj hjα => ?_⟩
  have hnC : Nc ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnP : Np ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnL : Nl ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnB := hp n hnP
  have htail : Summable (fun p : ℕ => if n ≤ p then
      1 / ((p : ℝ) * norming (stepLaw μ) θ p) else 0) := by
    apply (hs.indicator (Set.Ici n)).congr
    intro p
    simp [Set.indicator]
  rw [sizeTailProb_eq_tsum hc hne hap ⟨b, hb⟩ hn1 hj]
  have he := weighted_llt_error hn1 hδ.le (fun p hnp => hp p (hnP.trans hnp)) htail
    (fun p hnp => by
      have ht := hl p (hnL.trans hnp) (-(j : ℤ))
      simpa only [mean_stepLaw hc, mul_zero, sub_zero, Int.cast_neg, Int.cast_natCast,
        neg_div] using ht)
  calc _ ≤ δ * j * ∑' p : ℕ, if n ≤ p then
          1 / ((p : ℝ) * norming (stepLaw μ) θ p) else 0 := he
    _ ≤ δ * j * (D / norming (stepLaw μ) θ n) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hδ.le (Nat.cast_nonneg _))
      exact (hC n hnC).trans ((div_le_div_iff_of_pos_right hnB).mpr
        (le_trans (le_abs_self C) (by dsimp [D]; linarith)))
    _ = δ * ((j : ℝ) / norming (stepLaw μ) θ n) * D := by ring
    _ ≤ δ * α * D := by
      apply mul_le_mul_of_nonneg_right _ hD.le
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact (div_le_iff₀ hnB).mpr hjα
    _ = ε := by dsimp [δ]; field_simp

/-- The Riemann-sum step, uniform in the full spatial range of the statement. -/
theorem sizeTail_riemann {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * norming (stepLaw μ) θ n →
      |(∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * (1 / norming (stepLaw μ) θ p) *
          Scalar.stableDensity θ (-((j : ℝ) / norming (stepLaw μ) θ p)) else 0) -
        sizeTailKernel θ 1 ((j : ℝ) / norming (stepLaw μ) θ n)| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  have hmono := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA').1
  rw [mean_stepLaw hc] at ha
  obtain ⟨a, heq, h⟩ := ha.exists_stableDomain hc hne hmono
  obtain ⟨Nr, hr⟩ := density_riemann_uniform h hα hε
  obtain ⟨Ne, he⟩ := eventually_atTop.mp heq
  refine ⟨max (max Nr Ne) 1, fun n hn j hj hjα => ?_⟩
  have hnR : Nr ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnE : Ne ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have han := h.pos n hn1
  have hx0 : 0 ≤ (j : ℝ) / a n := div_nonneg (Nat.cast_nonneg _) han.le
  have hxα : (j : ℝ) / a n ≤ α := by
    rw [div_le_iff₀ han, he n hnE]
    exact hjα
  have hh := hr n hnR ((j : ℝ) / a n) hx0 hxα
  have hxj : ((j : ℝ) / a n) * a n = j := div_mul_cancel₀ _ han.ne'
  rw [hxj, he n hnE] at hh
  have hsum : (∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * (1 / norming (stepLaw μ) θ p) *
          Scalar.stableDensity θ (-((j : ℝ) / norming (stepLaw μ) θ p)) else 0) =
      ∑' p : ℕ, if n ≤ p then densityTerm θ a j p else 0 := by
    apply tsum_congr
    intro p
    by_cases hnp : n ≤ p
    · simp only [hnp, ite_true, densityTerm, he p (hnE.trans hnp)]
    · simp only [hnp, ite_false]
  rw [hsum]
  exact hh

/-- Lemma 5.11: combine the uniform LLT replacement with the uniform Riemann tail. -/
theorem lem_technical2 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |sizeTailProb μ n j - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ n)| ≤ ε := by
  obtain ⟨N₁, h₁⟩ := sizeTail_llt hc hne hap hDA hα (half_pos hε)
  obtain ⟨N₂, h₂⟩ := sizeTail_riemann hc hne hap hDA hα (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn j hj hjα => ?_⟩
  have hjB : (j : ℝ) ≤ α * norming (stepLaw μ) θ n := by
    simpa only [normB_natCast] using hjα
  let S : ℝ := ∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * (1 / norming (stepLaw μ) θ p) *
    Scalar.stableDensity θ (-((j : ℝ) / norming (stepLaw μ) θ p)) else 0
  have h₁' : |sizeTailProb μ n j - S| ≤ ε / 2 := h₁ n (le_of_max_le_left hn) j hj hjB
  have h₂' : |S - sizeTailKernel θ 1 ((j : ℝ) / norming (stepLaw μ) θ n)| ≤ ε / 2 :=
    h₂ n (le_of_max_le_right hn) j hj hjB
  rw [normB_natCast]
  calc _ ≤ |sizeTailProb μ n j - S| +
        |S - sizeTailKernel θ 1 ((j : ℝ) / norming (stepLaw μ) θ n)| := abs_sub_le _ S _
    _ ≤ ε / 2 + ε / 2 := add_le_add h₁' h₂'
    _ = ε := by ring

end Htheta

end BGWLeaves.LocalEstimates.SizeTailKernel
