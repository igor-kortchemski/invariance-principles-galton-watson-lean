module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.LeafLimits.AbsolueTail
public import BGWLeaves.Conditioning
public import BGWLeaves.Conditioning.AbsCont
public import BGWLeaves.LeafMass.Arithmetic
public import BGWLeaves.LeafMass.YLaw
public import BGWLeaves.LocalEstimates
public import BGWLeaves.ClassicalLimits.Cited
public import BGWLeaves.ClassicalLimits.Perturbation
public import BGWLeaves.ClassicalLimits.WalkClock
public import BGWLeaves.Coding
public import BGW.StableTrees.DiscreteForestPrefixMass
public import BGW.Probability.SeparableRepresentation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import BGW.StableTrees.ExactPrefixBasic
public import BGW.StableTrees.ExactPrefixLimit
public import BGW.StableTrees.KendallAdapter

/-!
# M13 provider `Absolue`

Provider for Lemma 5.8.  It proves the registered hole `lem_absolue` of `BGWLeaves.LeafLimits`,
exported in namespace `BGWLeaves.LeafLimits.Absolue` with exactly the type of the statements file.
Inputs: tranche 1 `prop_abscon`, `cor_tejhnique_i/ii`, `lem_CVf_i`, `prop_passage_ii`; M12 `thm_cvW`,
`prop_Gamma`, `gammaA_eq_paper`, `lem_CVproba_pair`.

Lemma 5.8 is proved by transferring the stopped-tail law through Proposition 4.4(ii),
identifying the exact endpoint density, and applying atom-free cutoffs to nonnegative bounded
continuous tests. Fatou gives the lower bound and probability mass gives weak convergence.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.Absolue

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- The real expression inside the ceiling has asymptotic slope `μ₀`. -/
theorem realCutoff_ratio (μ : PMF ℕ) :
    Tendsto (fun n : ℕ => ((μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ)) / n)
      atTop (𝓝 (μ 0).toReal) := by
  have ht : Tendsto (fun n : ℕ => (μ 0).toReal - (n : ℝ) ^ (-(1 / 4 : ℝ)))
      atTop (𝓝 ((μ 0).toReal - 0)) := tendsto_const_nhds.sub
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sub_div, mul_div_cancel_right₀ _ hnpos.ne', ← Real.rpow_sub_one hnpos.ne']
  norm_num

/-- Taking the natural ceiling does not change the asymptotic slope. -/
theorem leafCutoff_ratio {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal) :
    Tendsto (fun n : ℕ => (leafCutoff μ n : ℝ) / n) atTop (𝓝 (μ 0).toReal) := by
  have hr := realCutoff_ratio μ
  have hpos := hr.eventually (eventually_gt_nhds h0)
  have hu := hr.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hr hu
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg n)
  · filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have he : 0 ≤ (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) :=
      ((div_pos_iff_of_pos_right hnpos).1 hn).le
    rw [← add_div]
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one he).le hnpos.le

/-- The cutoff tends to infinity; monotonicity of the cutoff is not needed. -/
theorem tendsto_leafCutoff {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal) :
    Tendsto (leafCutoff μ) atTop atTop := by
  have ht := Filter.Tendsto.pos_mul_atTop h0 (leafCutoff_ratio h0)
    tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => (leafCutoff μ n : ℝ)) atTop atTop := by
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    exact div_mul_cancel₀ _ (by exact_mod_cast hn)
  exact tendsto_natCast_atTop_iff.mp ht'

/-- Every positive fibre defining `rGreatest` is finite and nonempty. -/
theorem rGreatest_fiber {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal)
    (h1 : (μ 0).toReal < 1) {n : ℕ} (hn : 1 ≤ n) :
    ({r : ℕ | 1 ≤ r ∧ leafCutoff μ r = n}).Finite ∧
      ({r : ℕ | 1 ≤ r ∧ leafCutoff μ r = n}).Nonempty := by
  constructor
  · obtain ⟨N, hN⟩ := eventually_atTop.1
      ((tendsto_leafCutoff h0).eventually (eventually_gt_atTop n))
    apply (Set.finite_Iio N).subset
    intro r hr
    exact lt_of_not_ge fun h => (ne_of_gt (hN r h)) hr.2
  · obtain ⟨r, hr⟩ := leafCutoff_surjective h0 h1 n hn
    refine ⟨r, ?_, hr⟩
    by_contra h
    have hz : r = 0 := by omega
    simp [hz, leafCutoff] at hr
    omega

/-- The defining maximum is attained, including at every small positive leaf number. -/
theorem rGreatest_spec {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal)
    (h1 : (μ 0).toReal < 1) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ rGreatest μ n ∧ leafCutoff μ (rGreatest μ n) = n := by
  obtain ⟨hf, he⟩ := rGreatest_fiber h0 h1 hn
  exact he.csSup_mem hf

/-- The leaf cutoff never exceeds its index. -/
theorem leafCutoff_le (μ : PMF ℕ) (r : ℕ) : leafCutoff μ r ≤ r := by
  apply Nat.ceil_le.2
  have hp : (μ 0).toReal ≤ 1 := by
    exact_mod_cast ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hr := Real.rpow_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (3 / 4 : ℝ)
  linarith

/-- In particular the maximum index is at least the positive leaf number. -/
theorem le_rGreatest {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal)
    (h1 : (μ 0).toReal < 1) {n : ℕ} (hn : 1 ≤ n) : n ≤ rGreatest μ n := by
  calc
    n = leafCutoff μ (rGreatest μ n) := (rGreatest_spec h0 h1 hn).2.symm
    _ ≤ rGreatest μ n := leafCutoff_le μ _

theorem tendsto_rGreatest {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal)
    (h1 : (μ 0).toReal < 1) : Tendsto (rGreatest μ) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact le_rGreatest h0 h1 hn

/-- The inverse cutoff normalization used in Corollary 5.5. -/
theorem tendsto_leaf_div_rGreatest {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal)
    (h1 : (μ 0).toReal < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) / rGreatest μ n) atTop (𝓝 (μ 0).toReal) := by
  apply ((leafCutoff_ratio h0).comp (tendsto_rGreatest h0 h1)).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_def, (rGreatest_spec h0 h1 hn).2]

/-- The paper's `r_n/n → 1/μ₀`. -/
theorem tendsto_rGreatest_div_leaf {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal)
    (h1 : (μ 0).toReal < 1) :
    Tendsto (fun n : ℕ => (rGreatest μ n : ℝ) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) / rGreatest μ n)) atTop
      (𝓝 (1 / (μ 0).toReal)) :=
    tendsto_const_nhds.div (tendsto_leaf_div_rGreatest h0 h1) h0.ne'
  exact ht.congr fun n => by simp only [one_div_div]

/-- For `a < 1`, the requested clock uses fewer than `n` leaves eventually.
This removes the junk clock values at the finitely many small leaf numbers. -/
theorem eventually_clock_index_lt {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal)
    (h1 : (μ 0).toReal < 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ᶠ n : ℕ in atTop, ⌊a * (μ 0).toReal * rGreatest μ n⌋₊ < n := by
  have ht := (tendsto_rGreatest_div_leaf h0 h1).const_mul (a * (μ 0).toReal)
  have hv : a * (μ 0).toReal * (1 / (μ 0).toReal) = a := by
    field_simp
  rw [hv] at ht
  filter_upwards [ht.eventually (gt_mem_nhds ha1), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hb : a * (μ 0).toReal * rGreatest μ n < n := by
    apply (div_lt_one hn0).1
    simpa only [mul_div_assoc] using hn
  apply Nat.floor_lt (by positivity) |>.2
  exact hb

/-- The positive survival kernel has a positive minimum on every compact interval away from zero.
This is the denominator bound left implicit in `eq:cva`. -/
theorem sizeTailKernel_lower_bound {θ s l u : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hs : 0 < s) (hl : 0 < l) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc l u, δ ≤ BGWLeaves.sizeTailKernel θ s x := by
  have hc : ContinuousOn (fun x => BGWLeaves.sizeTailKernel θ s x) (Set.Icc l u) := by
    simp_rw [ClassicalLimits.Cited.sizeTailKernel_eq_kernel]
    apply (continuousOn_sizeTailKernel hθ).comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨hs, lt_of_lt_of_le hl hx.1⟩
  apply isCompact_Icc.exists_forall_le' hc
  intro x hx
  rw [ClassicalLimits.Cited.sizeTailKernel_eq_kernel]
  exact sizeTailKernel_pos hθ hs (lt_of_lt_of_le hl hx.1)


theorem clock_eq_of_treeStopPath_eq {t s : PlaneTree} {k : ℕ}
    (he : treeStopPath t k = treeStopPath s k) :
    (treeLeafTime t k).toNat = (treeLeafTime s k).toNat := by
  have h := congrArg List.length he
  simp only [treeStopPath, List.length_map, List.length_range] at h
  omega

theorem luka_eq_of_treeStopPath_eq {t s : PlaneTree} {k i : ℕ}
    (he : treeStopPath t k = treeStopPath s k) (hi : i ≤ (treeLeafTime t k).toNat) :
    t.lukasiewicz i = s.lukasiewicz i := by
  have hc := clock_eq_of_treeStopPath_eq he
  have hh := congrArg (fun x : List ℤ => x[i]?) he
  simp only [treeStopPath, List.getElem?_map,
    List.getElem?_range (by omega : i < (treeLeafTime t k).toNat + 1),
    List.getElem?_range (by omega : i < (treeLeafTime s k).toNat + 1),
    Option.map_some, Option.some.injEq] at hh
  exact hh

theorem heightSeq_eq_of_luka_prefix {t s : PlaneTree} {m i : ℕ}
    (ht : m < t.size) (hs : m < s.size)
    (he : ∀ j ≤ m, t.lukasiewicz j = s.lukasiewicz j) (hi : i ≤ m) :
    t.heightSeq i = s.heightSeq i := by
  classical
  rw [PlaneTree.heightSeq_of_lt t (hi.trans_lt ht),
    PlaneTree.heightSeq_of_lt s (hi.trans_lt hs),
    PlaneTree.height_eq_card_recordMin, PlaneTree.height_eq_card_recordMin]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hjm : j ≤ m := (Finset.mem_range.mp hj).le.trans hi
  simp only [he j hjm]
  constructor <;> intro hh l hjl hli
  · rw [← he l (hli.trans hi)]
    exact hh l hjl hli
  · rw [he l (hli.trans hi)]
    exact hh l hjl hli

theorem heightLin_eq_of_luka_prefix {t s : PlaneTree} {m : ℕ}
    (ht : m < t.size) (hs : m < s.size)
    (he : ∀ j ≤ m, t.lukasiewicz j = s.lukasiewicz j)
    {u : ℝ} (hu0 : 0 ≤ u) (hum : u ≤ m) : t.heightLin u = s.heightLin u := by
  by_cases hu : u = m
  · rw [hu, PlaneTree.heightLin_natCast, PlaneTree.heightLin_natCast,
      heightSeq_eq_of_luka_prefix ht hs he le_rfl]
  · have hul : u < m := lt_of_le_of_ne hum hu
    have hf : ⌊u⌋₊ < m := (Nat.floor_lt hu0).2 hul
    rw [PlaneTree.heightLin, PlaneTree.heightLin,
      heightSeq_eq_of_luka_prefix ht hs he (by omega : ⌊u⌋₊ ≤ m),
      heightSeq_eq_of_luka_prefix ht hs he (by omega : ⌊u⌋₊ + 1 ≤ m)]

theorem treeLeafTime_toNat_lt_size {t : PlaneTree} {k : ℕ}
    (hk : 1 ≤ k) (hkt : k ≤ t.degreeCount 0) : (treeLeafTime t k).toNat < t.size := by
  obtain ⟨i, hi, hd, _⟩ := BGWLeaves.Conditioning.AbsCont.exists_treeLeafTime hk hkt
  rw [hi]
  have hl := List.getElem?_eq_some_iff.1 hd
  simpa only [PlaneTree.length_degrees, ENat.toNat_natCast] using hl.1

theorem heightLin_eq_of_treeStopPath_eq {t s : PlaneTree} {k : ℕ}
    (hk : 1 ≤ k) (hkt : k ≤ t.degreeCount 0) (hks : k ≤ s.degreeCount 0)
    (he : treeStopPath t k = treeStopPath s k) {u : ℝ}
    (hu0 : 0 ≤ u) (huT : u ≤ (treeLeafTime t k).toNat) :
    t.heightLin u = s.heightLin u := by
  have hc := clock_eq_of_treeStopPath_eq he
  apply heightLin_eq_of_luka_prefix (treeLeafTime_toNat_lt_size hk hkt)
    (hc ▸ treeLeafTime_toNat_lt_size hk hks)
    (fun _ hj => luka_eq_of_treeStopPath_eq he hj) hu0 huT

theorem rescaledLuka_eq_of_luka_prefix {t s : PlaneTree} {m : ℕ} (b : ℝ)
    (he : ∀ j ≤ m, t.lukasiewicz j = s.lukasiewicz j) :
    rescaledLuka m b t.toLocallyFinite = rescaledLuka m b s.toLocallyFinite := by
  apply Skorokhod.ext
  intro u
  change BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq t.toLocallyFinite)
      ⌊(m : ℝ) * (u : ℝ)⌋₊ / b =
    BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq s.toLocallyFinite)
      ⌊(m : ℝ) * (u : ℝ)⌋₊ / b
  simp only [BGW.Probability.RealWalk.partialSum, PathTail.treeIncrementSeq,
    ExactPrefix.treeIncrements_toLocallyFinite, ExactPrefix.sum_range_getD]
  congr 2
  apply he
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_right (Nat.cast_nonneg m) u.2.2

theorem treeHeightLin_toLocallyFinite (t : PlaneTree) (u : ℝ) :
    TailPair.treeHeightLin t.toLocallyFinite u = t.heightLin u := by
  simp only [TailPair.treeHeightLin, dite_eq_left t.finiteVertices_toLocallyFinite]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).heightLin _ = _
  rw [Equiv.symm_apply_apply]

theorem absPair_eq_of_treeStopPath_eq {t s : PlaneTree} {μ0 : ℝ} {B : ℕ → ℝ} {r : ℕ}
    {a : ℝ≥0} (ha : 0 < (a : ℝ))
    (hk : 1 ≤ ⌊(a : ℝ) * μ0 * r⌋₊)
    (hkt : ⌊(a : ℝ) * μ0 * r⌋₊ ≤ t.degreeCount 0)
    (hks : ⌊(a : ℝ) * μ0 * r⌋₊ ≤ s.degreeCount 0)
    (he : treeStopPath t ⌊(a : ℝ) * μ0 * r⌋₊ = treeStopPath s ⌊(a : ℝ) * μ0 * r⌋₊) :
    absPair μ0 B r a ha t.toLocallyFinite = absPair μ0 B r a ha s.toLocallyFinite := by
  have hc := clock_eq_of_treeStopPath_eq he
  have hW := rescaledLuka_eq_of_luka_prefix (B r)
    (fun j hj => luka_eq_of_treeStopPath_eq he hj)
  apply Prod.ext
  · change Skorokhod.timeSpaceScale (a : ℝ) zero_le_one (rescaledLuka _ _ _, _, _) =
      Skorokhod.timeSpaceScale (a : ℝ) zero_le_one (rescaledLuka _ _ _, _, _)
    simp only [treeLeafClock, toPlaneTree_toLocallyFinite, ← hc, hW]
  · apply ContinuousMap.ext
    intro u
    change B r / r * TailPair.treeHeightLin t.toLocallyFinite
        ((treeLeafClock t.toLocallyFinite ((a : ℝ) * μ0 * r) : ℝ) * (u : ℝ) / a) =
      B r / r * TailPair.treeHeightLin s.toLocallyFinite
        ((treeLeafClock s.toLocallyFinite ((a : ℝ) * μ0 * r) : ℝ) * (u : ℝ) / a)
    simp only [treeLeafClock, toPlaneTree_toLocallyFinite, ← hc, treeHeightLin_toLocallyFinite]
    congr 1
    apply heightLin_eq_of_treeStopPath_eq hk hkt hks he
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) u.2.1) ha.le
    · rw [div_le_iff₀ ha]
      exact mul_le_mul_of_nonneg_left u.2.2 (Nat.cast_nonneg _)

theorem exists_absPair_eq_comp_treeStopPath (μ0 : ℝ) (B : ℕ → ℝ) (r : ℕ)
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (hk : 1 ≤ ⌊(a : ℝ) * μ0 * r⌋₊) :
    ∃ G : List ℤ → Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ),
      ∀ t : PlaneTree, ⌊(a : ℝ) * μ0 * r⌋₊ ≤ t.degreeCount 0 →
        absPair μ0 B r a ha t.toLocallyFinite = G (treeStopPath t ⌊(a : ℝ) * μ0 * r⌋₊) := by
  classical
  let G := fun w : List ℤ =>
    if h : ∃ t : PlaneTree, ⌊(a : ℝ) * μ0 * r⌋₊ ≤ t.degreeCount 0 ∧
        treeStopPath t ⌊(a : ℝ) * μ0 * r⌋₊ = w then
      absPair μ0 B r a ha (Classical.choose h).toLocallyFinite
    else absPair μ0 B r a ha LocallyFinite.leaf
  refine ⟨G, fun t ht => ?_⟩
  have hex : ∃ s : PlaneTree, ⌊(a : ℝ) * μ0 * r⌋₊ ≤ s.degreeCount 0 ∧
      treeStopPath s ⌊(a : ℝ) * μ0 * r⌋₊ = treeStopPath t ⌊(a : ℝ) * μ0 * r⌋₊ :=
    ⟨t, ht, rfl⟩
  dsimp only [G]
  rw [dite_eq_left hex]
  exact absPair_eq_of_treeStopPath_eq ha hk ht (Classical.choose_spec hex).1
    (Classical.choose_spec hex).2.symm



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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {j : ℕ → ℕ} {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hj : ∀ᶠ n : ℕ in atTop, 1 ≤ j n ∧ (j n : ℝ) ≤ α * normB μ θ (q n))
    (hjx : Tendsto (fun n => (j n : ℝ) / normB μ θ ((q n : ℝ) / (μ 0).toReal))
      atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => θ * ((q n : ℝ) *
        (psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal) /
      (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal)
      atTop (𝓝 (gammaA θ a x)) := by
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
  have hQe := tendsto_zero_of_uniform_error hqtop hj
    (fun ε hε => cor_tejhnique_ii hc hne hap hDA hnl ha0 ha1 hr hrn hα hε)
  have hGl : Tendsto (fun n =>
      (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal) atTop
      (𝓝 (BGWLeaves.sizeTailKernel θ (1 - a) x)) := by
    convert hGe.add hG using 1 <;> simp
  have hQl : Tendsto (fun n : ℕ => (q n : ℝ) *
      (psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal) atTop
      (𝓝 (BGWLeaves.qKernel θ (1 - a) x)) := by
    convert hQe.add hQ using 1 <;> simp
  have hGn : BGWLeaves.sizeTailKernel θ (1 - a) x ≠ 0 := by
    rw [ClassicalLimits.Cited.sizeTailKernel_eq_kernel]
    exact (sizeTailKernel_pos hθ (sub_pos.mpr ha1) hx).ne'
  rw [ClassicalLimits.Cited.gammaA_eq_paper]
  exact (hQl.const_mul θ).div hGl hGn



theorem arithFactor_eq_one_of_nonLattice {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) : arithFactor μ {0} = 1 := by
  rw [LeafMass.Arithmetic.arithFactor_zero_eq_setGcd hc hne]
  have hg := (LeafMass.Arithmetic.arithFactor_isGreatest_of_two_le
    (LeafMass.Arithmetic.exists_two_le hc hne)).1
  have hg1 := hg.1
  by_contra h
  have hge : 2 ≤ Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0} := by omega
  apply hnl
  refine ⟨0, Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0}, hge, ?_⟩
  apply (LeafMass.YLaw.etaLaw_ae_dvd_iff hc hne _ 0).mpr
  intro k hk hk0
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hd := Int.natCast_dvd_natCast.2
    (Nat.setGcd_dvd_of_mem (show i ∈ {j : ℕ | μ (j + 1) ≠ 0} from hk))
  simpa using hd

theorem tendsto_leaf_mass_normalized {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ n)
      atTop (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0)) := by
  have hL := ltn_ii_tendsto hc hne hap hDA
  simp only [arithFactor_eq_one_of_nonLattice hc hne hnl, one_dvd,
    Set.ofPred_true, Filter.principal_univ, inf_top_eq, Nat.cast_one, mul_one] at hL
  have hnratio : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 (1 : ℝ)) := by
    have ht : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)))
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    push_cast
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn]
  have hBratio := normB_ratio_tendsto hc hne hap hDA zero_lt_one hnratio
  simp only [normB_natCast, Real.one_rpow] at hBratio
  have hnorm := (hnratio.mul hBratio).mul hL
  simp only [one_mul] at hnorm
  apply (tendsto_add_atTop_iff_nat 1).1
  apply hnorm.congr'
  filter_upwards [eventually_ge_atTop 1, normB_pos_eventually hc hne hap hDA] with n hn hBn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp [hn0, hBn.ne']

theorem tendsto_tail_div_leaf_mass {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    Tendsto (fun n : ℕ => (psiStar μ n 1).toReal / ((n : ℝ) * (psi μ n 1).toReal))
      atTop (𝓝 θ) := by
  obtain ⟨a, ha⟩ := hDA
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos
    (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hC : (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 ≠ 0 :=
    (mul_pos (Real.rpow_pos_of_pos hp _) (Scalar.stableDensity_zero_pos ha.alpha_mem)).ne'
  have hT := leafTail_asymp hc hne hap ⟨a, ha⟩
  have hL := tendsto_leaf_mass_normalized hc hne hap ⟨a, ha⟩ hnl
  have ht := hT.div hL hC
  have hv : (θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0) /
      ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0) = θ := by
    rw [mul_assoc, mul_div_cancel_right₀ _ hC]
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [normB_pos_eventually hc hne hap ⟨a, ha⟩] with n hn
  rw [psiStar_one, psi_one]
  change (norming (stepLaw μ) θ n *
      (bienaymeLaw μ.toMeasure).real (leafGeEvent n)) /
      ((n : ℝ) * norming (stepLaw μ) θ n * leafProb μ n) = _
  rw [mul_comm (n : ℝ), mul_assoc, mul_div_mul_left _ _ hn.ne']
  rfl

theorem tendsto_abscon_density {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ b, StableDomain μ θ b) (hθ : 1 < θ ∧ θ ≤ 2)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {j : ℕ → ℕ} {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hj : ∀ᶠ n : ℕ in atTop, 1 ≤ j n ∧ (j n : ℝ) ≤ α * normB μ θ (q n))
    (hjx : Tendsto (fun n => (j n : ℝ) / normB μ θ ((q n : ℝ) / (μ 0).toReal))
      atTop (𝓝 x)) :
    Tendsto (fun n : ℕ =>
      (((psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n) / psi μ (q n) 1) /
        (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n) /
          psiStar μ (q n) 1)).toReal)) atTop (𝓝 (gammaA θ a x)) := by
  have hθn : θ ≠ 0 := by linarith [hθ.1]
  have hrem := tendsto_remaining_density hc hne hap hDA hθ hnl ha0 ha1 hr hrn
    hqtop hα hx hj hjx
  have hcoef := (tendsto_tail_div_leaf_mass hc hne hap hDA hnl).comp hqtop
  have ht := (hrem.div_const θ).mul hcoef
  rw [div_mul_cancel₀ _ hθn] at ht
  apply ht.congr'
  filter_upwards [hqtop.eventually (eventually_ne_atTop (0 : ℕ))] with n hn
  have hnR : (q n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [ENNReal.toReal_div, Function.comp_apply]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  generalize (psi μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal = A
  generalize (psiStar μ (q n - ⌊a * (μ 0).toReal * r (q n)⌋₊) (j n)).toReal = C
  generalize (psi μ (q n) 1).toReal = E
  generalize (psiStar μ (q n) 1).toReal = D
  calc
    _ = (θ * θ⁻¹) * ((q n : ℝ) * (q n : ℝ)⁻¹) * (A * E⁻¹ * (D * C⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hθn, mul_inv_cancel₀ hnR]; ring



private theorem mu0_bounds {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    0 < (μ 0).toReal ∧ (μ 0).toReal < 1 := by
  refine ⟨ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0), ?_⟩
  have hle : (μ 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  refine lt_of_le_of_ne hle fun heq => BGWLeaves.mu0_ne_one hc hne ?_
  exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top 0) ENNReal.one_ne_top).1
    (by simpa using heq)

private theorem integral_add_norm {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {ν : Measure LocallyFinite.Tree} [IsProbabilityMeasure ν]
    (f : BoundedContinuousFunction E ℝ) {Φ : LocallyFinite.Tree → E} (hΦ : Measurable Φ) :
    ∫ τ, (f (Φ τ) + ‖f‖) ∂ν = ∫ τ, f (Φ τ) ∂ν + ‖f‖ := by
  have hint : Integrable (fun τ => f (Φ τ)) ν :=
    Integrable.of_bound (f.continuous.measurable.comp hΦ).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun τ => f.norm_coe_le_norm (Φ τ))
  rw [integral_add hint (integrable_const _), integral_const]
  simp

/-- Proposition 4.4(ii), then substitution of the attained inverse cutoff. -/
private theorem leafGe_absPair_tendsto_of_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    (hT : Tendsto (fun n : ℕ => (DiscreteForest.tailTreeLaw μ n).map
        (absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 (tailExcLaw θ a)))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) :
    Tendsto (fun k => (leafGeTreeLaw μ (q k)).map
        (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 (tailExcLaw θ a)) := by
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hT ⊢
  intro f
  let Φ := fun n => absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1)
  have hΦ : ∀ n, Measurable (Φ n) := fun n => measurable_absPair _ _ _ _ _
  let U := fun n τ => f (Φ n τ) + ‖f‖
  have hU : ∀ n, IsBoundedTest (2 * ‖f‖) (U n) := by
    intro n
    refine ⟨(f.continuous.measurable.comp (hΦ n)).add_const _, fun τ => ?_⟩
    have hb := abs_le.1 (show |f (Φ n τ)| ≤ ‖f‖ by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (Φ n τ))
    constructor <;> dsimp [U] <;> linarith [hb.1, hb.2]
  have hbase : Tendsto (fun n : ℕ => ∫ τ, U n τ
      ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n])) atTop
      (𝓝 ((∫ z, f z ∂(tailExcLaw θ a).toMeasure) + ‖f‖)) := by
    apply ((hT f).add_const ‖f‖).congr fun n => ?_
    have hn := BGWLeaves.sizeGeEvent_ne_zero hc hne n
    have := cond_isProbabilityMeasure (μ := bienaymeLaw μ.toMeasure) hn
    rw [ProbabilityMeasure.toMeasure_map,
      DiscreteForest.tailTreeLaw_toMeasure μ n hn,
      integral_map (hΦ n).aemeasurable f.continuous.aestronglyMeasurable]
    exact (integral_add_norm (ν := (bienaymeLaw μ.toMeasure)[|sizeGeEvent n]) f (hΦ n)).symm
  have hpass := BGWLeaves.prop_passage_ii hc hne hap hDA hU hbase
  have hcomp := hpass.comp ((tendsto_rGreatest hp hp1).comp hqtop)
  have hsub := hcomp.sub_const ‖f‖
  rw [add_sub_cancel_right] at hsub
  apply hsub.congr'
  filter_upwards [hqtop.eventually_ge_atTop 1] with k hk
  have hs := (rGreatest_spec hp hp1 hk).2
  have hn := BGWLeaves.leafGeEvent_ne_zero hc hne (q k)
  have := cond_isProbabilityMeasure (μ := bienaymeLaw μ.toMeasure) hn
  simp only [Function.comp_apply, hs]
  rw [integral_add_norm f (hΦ _), add_sub_cancel_right,
    ProbabilityMeasure.toMeasure_map, coe_leafGeTreeLaw hn,
    integral_map (hΦ _).aemeasurable f.continuous.aestronglyMeasurable]

private theorem evalEnd_absPair (μ0 : ℝ) (B : ℕ → ℝ) (r : ℕ) (a : ℝ≥0)
    (ha : 0 < (a : ℝ)) (t : PlaneTree) :
    evalEnd a (absPair μ0 B r a ha t.toLocallyFinite).1 =
      (treeStopPos t ⌊(a : ℝ) * μ0 * r⌋₊ : ℝ) / B r := by
  change 1 * (BGW.Probability.RealWalk.partialSum
      (PathTail.treeIncrementSeq t.toLocallyFinite)
      ⌊(treeLeafClock t.toLocallyFinite ((a : ℝ) * μ0 * r) : ℝ) *
        min (1 / (a : ℝ) * a) 1⌋₊ / B r) = _
  rw [one_div_mul_cancel ha.ne', min_self, mul_one, Nat.floor_natCast, one_mul]
  simp only [treeLeafClock, toPlaneTree_toLocallyFinite,
    BGW.Probability.RealWalk.partialSum, PathTail.treeIncrementSeq,
    ExactPrefix.treeIncrements_toLocallyFinite, ExactPrefix.sum_range_getD]
  rfl

private noncomputable def absWeight (μ : PMF ℕ) (B : ℕ → ℝ) (r n : ℕ) (a : ℝ≥0)
    (z : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ)) : ℝ≥0∞ :=
  (psi μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) ⌊B r * evalEnd a z.1⌋₊ / psi μ n 1) /
    (psiStar μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) ⌊B r * evalEnd a z.1⌋₊ /
      psiStar μ n 1)

private theorem measurable_absWeight (μ : PMF ℕ) (B : ℕ → ℝ) (r n : ℕ) (a : ℝ≥0) :
    Measurable (absWeight μ B r n a) := by
  exact (measurable_of_countable (fun j : ℕ =>
    (psi μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) j / psi μ n 1) /
      (psiStar μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) j / psiStar μ n 1))).comp
    ((measurable_const.mul ((measurable_evalEnd a).comp measurable_fst)).nat_floor)

private theorem absWeight_absPair {μ : PMF ℕ} {B : ℕ → ℝ} {r n : ℕ} {a : ℝ≥0}
    (ha : 0 < (a : ℝ)) (hB : B r ≠ 0) (t : PlaneTree) :
    absWeight μ B r n a (absPair (μ 0).toReal B r a ha t.toLocallyFinite) =
      ((psi μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
          (pendingTrees t ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) / psi μ n 1) /
        (psiStar μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
          (pendingTrees t ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) / psiStar μ n 1)) := by
  simp only [absWeight, evalEnd_absPair, mul_div_cancel₀ _ hB, ← Int.floor_toNat, Int.floor_intCast,
    pendingTrees]


private theorem lintegral_absPair_abscon {μ : PMF ℕ} {B : ℕ → ℝ} {r n : ℕ} {a : ℝ≥0}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (ha : 0 < (a : ℝ)) (hb : B r ≠ 0)
    (hadm : LeafAdmissible μ n)
    (hk : 1 ≤ ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
    (hkn : ⌊(a : ℝ) * (μ 0).toReal * r⌋₊ < n)
    (F : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂((leafTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure =
      ∫⁻ z, F z * absWeight μ B r n a z
        ∂((leafGeTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure := by
  obtain ⟨G, hG⟩ := exists_absPair_eq_comp_treeStopPath (μ 0).toReal B r a ha hk
  have hΦ := measurable_absPair (μ 0).toReal B r a ha
  have hge := BGWLeaves.leafGeEvent_ne_zero hc hne n
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    lintegral_map hF hΦ,
    lintegral_map (f := fun z => F z * absWeight μ B r n a z)
      (hF.mul (measurable_absWeight μ B r n a)) hΦ,
    coe_leafTreeLaw hadm, coe_leafGeTreeLaw hge]
  calc
    _ = ∫⁻ τ, finiteTreeLift (fun t => F (G (treeStopPath t
        ⌊(a : ℝ) * (μ 0).toReal * r⌋₊))) τ
        ∂((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) := by
      apply lintegral_congr_ae
      filter_upwards [ae_cond_mem (measurableSet_leafCountEvent n)] with τ hτ
      obtain ⟨t, rfl, ht⟩ := hτ
      rw [finiteTreeLift_toLocallyFinite, ← hG t (by omega)]
    _ = _ := BGWLeaves.prop_abscon hc hne hk hkn (fun w => F (G w))
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_cond_mem
        (BGWLeaves.Conditioning.AbsCont.measurableSet_finiteTreeEvent
          (fun t => n ≤ t.degreeCount 0))] with τ hτ
      obtain ⟨t, rfl, ht⟩ := hτ
      rw [finiteTreeLift_toLocallyFinite, ← hG t (by omega), absWeight_absPair ha hb]

private theorem map_leaf_eq_withDensity_absWeight {μ : PMF ℕ} {B : ℕ → ℝ} {r n : ℕ}
    {a : ℝ≥0} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (ha : 0 < (a : ℝ)) (hb : B r ≠ 0)
    (hadm : LeafAdmissible μ n) (hk : 1 ≤ ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
    (hkn : ⌊(a : ℝ) * (μ 0).toReal * r⌋₊ < n) :
    ((leafTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure =
      (((leafGeTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure).withDensity
        (absWeight μ B r n a) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_absWeight μ B r n a) hF]
  simpa only [Pi.mul_apply, mul_comm] using
    lintegral_absPair_abscon hc hne ha hb hadm hk hkn F hF


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
  have hr := normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hp)
    (tendsto_rGreatest_div_leaf hp hp1)
  have hdindex : Tendsto (fun n : ℕ => ((n : ℝ) / (μ 0).toReal) / n)
      atTop (𝓝 (1 / (μ 0).toReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hd := normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hp) hdindex
  simp only [normB_natCast] at hr hd
  have h := ((hcan.comp (tendsto_rGreatest hp hp1)).mul hr).div hd
    (Real.rpow_pos_of_pos (one_div_pos.mpr hp) _).ne'
  simp only [one_mul, div_self (Real.rpow_pos_of_pos (one_div_pos.mpr hp) _).ne'] at h
  apply h.congr'
  filter_upwards [normB_pos_eventually hc hne hap hDA,
    (tendsto_rGreatest hp hp1).eventually (normB_pos_eventually hc hne hap hDA)] with n hn hrn
  dsimp
  field_simp [hn.ne', hrn.ne']


private theorem absWeight_contConv {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {z : ℕ → Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ)} {x : ℝ}
    (hx : 0 < x) (hz : Tendsto (fun k => evalEnd a (z k).1) atTop (𝓝 x)) :
    Tendsto (fun k => (absWeight μ B (rGreatest μ (q k)) (q k) a (z k)).toReal)
      atTop (𝓝 (gammaA θ a x)) := by
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  let j := fun k => ⌊B (rGreatest μ (q k)) * evalEnd a (z k).1⌋₊
  have hBr := hB.tendsto_norming_atTop.comp ((tendsto_rGreatest hp hp1).comp hqtop)
  have hprod := hBr.atTop_mul_pos hx hz
  have hjtop : Tendsto j atTop atTop := tendsto_nat_floor_atTop.comp hprod
  have hratio := (norming_rGreatest_ratio hc hne hap hB).comp hqtop
  have hfloor := tendsto_nat_floor_div_atTop.comp hprod
  have hjx : Tendsto (fun k => (j k : ℝ) /
      normB μ θ ((q k : ℝ) / (μ 0).toReal)) atTop (𝓝 x) := by
    have ht := hfloor.mul (hratio.mul hz)
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [hprod.eventually (eventually_ne_atTop (0 : ℝ))] with k hk
    dsimp only [Function.comp_apply, j] at hk ⊢
    rw [show B (rGreatest μ (q k)) / normB μ θ ((q k : ℝ) / (μ 0).toReal) *
      evalEnd a (z k).1 = (B (rGreatest μ (q k)) * evalEnd a (z k).1) /
        normB μ θ ((q k : ℝ) / (μ 0).toReal) by ring]
    exact div_mul_div_cancel₀ hk
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
  have ht := tendsto_abscon_density hc hne hap hDA hB.index_mem hnl
    (NNReal.coe_pos.mpr ha.1) (NNReal.coe_lt_coe.mpr ha.2) hr hrn hqtop hα hx hj hjx
  apply ht.congr'
  filter_upwards [hqtop.eventually hre] with k hk
  simp only [hk, absWeight, j]


private theorem cutoff_tendsto {v : ℕ → ℝ} {x l u : ℝ}
    (hv : Tendsto v atTop (𝓝 x)) (hl : x ≠ l) (hu : x ≠ u) :
    Tendsto (fun n => if l < v n ∧ v n < u then (1 : ℝ) else 0) atTop
      (𝓝 (if l < x ∧ x < u then 1 else 0)) := by
  by_cases hmem : l < x ∧ x < u
  · rw [ite_eq_left hmem]
    apply tendsto_const_nhds.congr'
    filter_upwards [hv.eventually (lt_mem_nhds hmem.1),
      hv.eventually (gt_mem_nhds hmem.2)] with n hn1 hn2
    simp [hn1, hn2]
  · rw [ite_eq_right hmem]
    apply tendsto_const_nhds.congr'
    rcases le_or_gt x l with hxl | hlx
    · have hlt : x < l := lt_of_le_of_ne hxl hl
      filter_upwards [hv.eventually (gt_mem_nhds hlt)] with n hn
      have hnot : ¬ (l < v n ∧ v n < u) := by intro h; linarith [h.1]
      simp [hnot]
    · have hlt : u < x := lt_of_le_of_ne (le_of_not_gt (fun h => hmem ⟨hlx, h⟩)) hu.symm
      filter_upwards [hv.eventually (lt_mem_nhds hlt)] with n hn
      have hnot : ¬ (l < v n ∧ v n < u) := by intro h; linarith [h.2]
      simp [hnot]

private theorem lintegral_le_liminf_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : ℕ → Ω → ℝ≥0∞} {g : Ω → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n))
    (ht : ∀ᵐ ω ∂ν, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    ∫⁻ ω, g ω ∂ν ≤ liminf (fun n => ∫⁻ ω, f n ω ∂ν) atTop := by
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂ν :=
      lintegral_congr_ae (ht.mono fun _ h => h.liminf_eq.symm)
    _ ≤ _ := lintegral_liminf_le hf

/-- Cutoffs avoid both endpoint atoms. No assumption that every deterministic cutoff is a
continuity set is made. -/
private theorem exists_atom_free_cutoffs {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] {e : Ω → ℝ} (he : Measurable e) :
    ∃ α : ℕ → ℝ, Tendsto α atTop atTop ∧ ∀ m,
      1 < α m ∧ ν {ω | e ω = α m} = 0 ∧ ν {ω | e ω = 1 / α m} = 0 := by
  let A := {x : ℝ | 0 < ν {ω | e ω = x}}
  have hA : A.Countable := Measure.countable_meas_level_set_pos he
  have hbad : (A ∪ (Inv.inv ⁻¹' A)).Countable := hA.union (hA.preimage inv_injective)
  have hex (m : ℕ) : ∃ α ∈ Set.Ioo ((m : ℝ) + 2) ((m : ℝ) + 3),
      α ∉ A ∪ (Inv.inv ⁻¹' A) := by
    have hz := hbad.measure_zero volume
    have hpos : 0 < volume (Set.Ioo ((m : ℝ) + 2) ((m : ℝ) + 3) \
        (A ∪ (Inv.inv ⁻¹' A))) := by
      rw [measure_sdiff_null hz, Real.volume_Ioo]
      norm_num
    exact nonempty_of_measure_ne_zero hpos.ne'
  choose α hα hn using hex
  refine ⟨α, tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop, fun m => ?_⟩
  · exact le_trans (by linarith : (m : ℝ) ≤ m + 2) (hα m).1.le
  · have hnot1 : ¬ 0 < ν {ω | e ω = α m} := fun h => hn m (Or.inl h)
    have hnot2 : ¬ 0 < ν {ω | e ω = 1 / α m} := by
      intro h
      apply hn m
      right
      change 0 < ν {ω | e ω = (α m)⁻¹}
      simpa only [one_div] using h
    have hlarge : 1 < α m := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hm2 : (m : ℝ) + 2 < α m := (hα m).1
      linarith
    exact ⟨hlarge,
      le_antisymm (le_of_not_gt hnot1) bot_le, le_antisymm (le_of_not_gt hnot2) bot_le⟩

/-- The bounded-test change-of-measure argument, with atom-free endpoint cutoffs and cutoff
removal. Fatou gives the lower bound; probability mass gives convergence for all bounded tests. -/
private theorem weighted_tendsto_of_cutoffs {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E]
    {P Q : ℕ → ProbabilityMeasure E} {P₀ Q₀ : ProbabilityMeasure E}
    (hP : Tendsto P atTop (𝓝 P₀)) (w : ℕ → E → ℝ≥0∞) (g e : E → ℝ)
    (hw : ∀ n, Measurable (w n)) (hg : Measurable g) (he : Measurable e)
    (hgnn : ∀ x, 0 ≤ g x)
    (hQ : ∀ᶠ n in atTop, (Q n).toMeasure = (P n).toMeasure.withDensity (w n))
    (hΓ : ∀ f : BoundedContinuousFunction E ℝ,
      ∫ x, f x ∂Q₀.toMeasure = ∫ x, f x * g x ∂P₀.toMeasure)
    (hgood : ∀ᵐ x ∂P₀.toMeasure, ContinuousAt e x ∧ 0 < e x)
    (hconv : ∀ x, ContinuousAt e x → 0 < e x → ∀ z : ℕ → E,
      Tendsto z atTop (𝓝 x) →
      Tendsto (fun n => (w n (z n)).toReal) atTop (𝓝 (g x))) :
    Tendsto Q atTop (𝓝 Q₀) := by
  obtain ⟨Ω, mΩ, ν, hν, X, Y, hXm, hYm, hXlaw, hYlaw, hXY⟩ :=
    BGW.Probability.exists_probabilitySpace_tendsto_ae_of_tendsto_metric hP
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure ν := hν
  have hgoodY : ∀ᵐ ω ∂ν, ContinuousAt e (Y ω) ∧ 0 < e (Y ω) := by
    rw [← hYlaw] at hgood
    exact ae_of_ae_map hYm.aemeasurable hgood
  obtain ⟨α, hαtop, hα⟩ := exists_atom_free_cutoffs ν (he.comp hYm)
  let χ := fun m x => if 1 / α m < e x ∧ e x < α m then (1 : ℝ) else 0
  have hχm : ∀ m, Measurable (χ m) := fun m =>
    measurable_const.ite ((measurableSet_lt measurable_const he).inter
      (measurableSet_lt he measurable_const)) measurable_const
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  apply BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_integral
  intro f hfnn
  let L := liminf (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure) atTop
  have hcut (m : ℕ) :
      ∫⁻ ω, ENNReal.ofReal (f (Y ω) * g (Y ω) * χ m (Y ω)) ∂ν ≤ L := by
    let H := fun n ω => ENNReal.ofReal (f (X n ω) * (w n (X n ω)).toReal * χ m (X n ω))
    have hHm : ∀ n, Measurable (H n) := fun n => by
      exact ((f.continuous.measurable.comp (hXm n)).mul
        ((hw n).ennreal_toReal.comp (hXm n)) |>.mul ((hχm m).comp (hXm n))).ennreal_ofReal
    have hHt : ∀ᵐ ω ∂ν, Tendsto (fun n => H n ω) atTop
        (𝓝 (ENNReal.ofReal (f (Y ω) * g (Y ω) * χ m (Y ω)))) := by
      have hnull : ∀ᵐ ω ∂ν, e (Y ω) ≠ α m ∧ e (Y ω) ≠ 1 / α m := by
        have h1 : ∀ᵐ ω ∂ν, e (Y ω) ≠ α m := by
          rw [ae_iff]
          simpa only [not_not, Function.comp_apply] using (hα m).2.1
        have h2 : ∀ᵐ ω ∂ν, e (Y ω) ≠ 1 / α m := by
          rw [ae_iff]
          simpa only [not_not, Function.comp_apply] using (hα m).2.2
        exact h1.and h2
      filter_upwards [hgoodY, hXY, hnull] with ω hgω hxy hnω
      have hc := cutoff_tendsto (hgω.1.tendsto.comp hxy) hnω.2 hnω.1
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (((f.continuous.tendsto _).comp hxy).mul
          (hconv _ hgω.1 hgω.2 _ hxy) |>.mul hc)
    have hbound : ∀ᶠ n in atTop, (∫⁻ ω, H n ω ∂ν) ≤
        ∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure := by
      filter_upwards [hQ] with n hQn
      rw [hQn, lintegral_withDensity_eq_lintegral_mul _ (hw n) f.continuous.measurable.ennreal_ofReal]
      rw [← hXlaw n, lintegral_map (f := fun x => (w n * fun x => ENNReal.ofReal (f x)) x)
        ((hw n).mul f.continuous.measurable.ennreal_ofReal) (hXm n)]
      apply lintegral_mono
      intro ω
      dsimp only [H, χ]
      split_ifs with hmem
      · simp only [mul_one, Pi.mul_apply]
        rw [mul_comm (w n (X n ω))]
        calc
          _ = ENNReal.ofReal (f (X n ω)) * ENNReal.ofReal (w n (X n ω)).toReal :=
            ENNReal.ofReal_mul (hfnn _)
          _ ≤ _ := by gcongr; exact ENNReal.ofReal_toReal_le
      · simp
    exact (lintegral_le_liminf_of_ae_tendsto hHm hHt).trans
      (Filter.liminf_le_liminf hbound)
  have hfull : ∫⁻ ω, ENNReal.ofReal (f (Y ω) * g (Y ω)) ∂ν ≤ L := by
    have hm : ∀ m, Measurable (fun ω => ENNReal.ofReal
        (f (Y ω) * g (Y ω) * χ m (Y ω))) := fun m =>
      ((f.continuous.measurable.mul hg).mul (hχm m) |>.comp hYm).ennreal_ofReal
    have ht : ∀ᵐ ω ∂ν, Tendsto (fun m => ENNReal.ofReal
        (f (Y ω) * g (Y ω) * χ m (Y ω))) atTop
        (𝓝 (ENNReal.ofReal (f (Y ω) * g (Y ω)))) := by
      filter_upwards [hgoodY] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [(hαtop.const_div_atTop 1).eventually (gt_mem_nhds hω.2),
        hαtop.eventually_gt_atTop (e (Y ω))] with m hm1 hm2
      simp only [χ]
      rw [ite_eq_left (show 1 / α m < e (Y ω) ∧ e (Y ω) < α m from ⟨hm1, hm2⟩), mul_one]
    exact (lintegral_le_liminf_of_ae_tendsto hm ht).trans
      (liminf_le_of_frequently_le' (Eventually.of_forall hcut).frequently)
  have htarget : ∫⁻ ω, ENNReal.ofReal (f (Y ω) * g (Y ω)) ∂ν =
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂P₀.toMeasure := by
    rw [← hYlaw, lintegral_map (f := fun x : E => ENNReal.ofReal (f x * g x))
      (f.continuous.measurable.mul hg).ennreal_ofReal hYm]
  rw [htarget] at hfull
  have hbound : ∀ n, (∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure) ≤
      ENNReal.ofReal ‖f‖ := by
    intro n
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ‖f‖ ∂(Q n).toMeasure := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal
          ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x))
      _ = _ := by simp
  have hLfin : L ≠ ⊤ := ne_of_lt (lt_of_le_of_lt
    (liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently) ENNReal.ofReal_lt_top)
  rw [hΓ f, integral_eq_lintegral_of_nonneg_ae (f := fun x : E => f x * g x)
    (Eventually.of_forall fun x => mul_nonneg (hfnn x) (hgnn x))
    (f.continuous.measurable.mul hg).aestronglyMeasurable]
  have hreal := ENNReal.toReal_mono hLfin hfull
  dsimp only [L] at hreal
  rw [← ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top (Eventually.of_forall hbound)] at hreal
  have hi (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure).toReal =
      ∫ x, f x ∂(Q n).toMeasure :=
    (integral_eq_lintegral_of_nonneg_ae (f := fun x : E => f x)
      (Eventually.of_forall hfnn) f.continuous.measurable.aestronglyMeasurable).symm
  simpa only [hi] using hreal


private theorem lem_absolue_of_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ))
    (hT : ∀ {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1),
      Tendsto (fun n : ℕ => (DiscreteForest.tailTreeLaw μ n).map
          (absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1)))
        atTop (𝓝 (tailExcLaw θ a)))
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  change 0 < a ∧ a < 1 at ha
  let E := Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ)
  let P := fun k => (leafGeTreeLaw μ (q k)).map
    (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1))
  let Q := fun k => (leafTreeLaw μ (q k)).map
    (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1))
  let e := fun z : E => evalEnd a z.1
  let g := fun z : E => max (gammaA θ a (e z)) 0
  have ha0 : 0 < (a : ℝ) := NNReal.coe_pos.mpr ha.1
  have ha1 : (a : ℝ) < 1 := NNReal.coe_lt_coe.mpr ha.2
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  have hrtop := (tendsto_rGreatest hp hp1).comp hqtop
  have hP : Tendsto P atTop (𝓝 (tailExcLaw θ a)) :=
    leafGe_absPair_tendsto_of_tail hc hne hap hB ha (hT ha) hqtop
  have hgoodraw : ∀ᵐ z : E ∂(tailExcLaw θ a).toMeasure,
      ContinuousAt z.1 ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩ ∧ 0 < e z := by
    have hfst : (tailExcLaw θ a).toMeasure.map Prod.fst =
        (PathTail.tailPrefixLimit θ a).toMeasure :=
      congrArg ProbabilityMeasure.toMeasure (tailExcLaw_map_fst θ a)
    have hh := ExactPrefix.ae_tailPrefix_continuousAt_pos hB.index_mem a ha
    rw [← hfst] at hh
    exact ae_of_ae_map measurable_fst.aemeasurable hh
  have hgood : ∀ᵐ z : E ∂(tailExcLaw θ a).toMeasure, ContinuousAt e z ∧ 0 < e z := by
    filter_upwards [hgoodraw] with z hz
    exact ⟨(Skorokhod.continuousAt_eval hz.1).comp continuous_fst.continuousAt, hz.2⟩
  have he : Measurable e := (measurable_evalEnd a).comp measurable_fst
  have hg0 : Measurable (fun z : E => gammaA θ a (e z)) :=
    (measurable_gammaA θ).comp (measurable_const.prodMk he)
  have hgeq : g =ᵐ[(tailExcLaw θ a).toMeasure] (fun z => gammaA θ a (e z)) := by
    filter_upwards [hgood] with z hz
    exact max_eq_left (gammaA_nonneg hB.index_mem ha1 hz.2)
  have hQ : ∀ᶠ k in atTop, (Q k).toMeasure = (P k).toMeasure.withDensity
      (absWeight μ B (rGreatest μ (q k)) (q k) a) := by
    have hclocktop : Tendsto (fun k => ⌊(a : ℝ) * (μ 0).toReal * rGreatest μ (q k)⌋₊)
        atTop atTop := tendsto_nat_floor_atTop.comp
      ((tendsto_natCast_atTop_atTop.comp hrtop).const_mul_atTop (mul_pos ha0 hp))
    filter_upwards [hclocktop.eventually_ge_atTop 1,
      hqtop.eventually (eventually_clock_index_lt hp hp1 ha0 ha1),
      hrtop.eventually hB.pos] with k hk hkn hbr
    exact map_leaf_eq_withDensity_absWeight hc hne ha0 hbr.ne' (hq k) hk hkn
  have hΓ : ∀ f : BoundedContinuousFunction E ℝ,
      ∫ z, f z ∂((excLaw θ).map (restrictPair ha.2.le)).toMeasure =
        ∫ z, f z * g z ∂(tailExcLaw θ a).toMeasure := by
    intro f
    have hf : Measurable (fun z : E => f z * gammaA θ a (e z)) :=
      f.continuous.measurable.mul hg0
    calc
      _ = ∫ z, f (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure := by
        exact integral_map (measurable_restrictPair ha.2.le).aemeasurable
          f.continuous.aestronglyMeasurable
      _ = ∫ z, f (restrictPair ha.2.le z) * gammaA θ a
          (evalEnd a (restrictPair ha.2.le z).1) ∂(tailExcLaw θ 1).toMeasure :=
        ClassicalLimits.Cited.prop_Gamma hB.index_mem a ha f f.continuous.measurable
          ⟨‖f‖, fun z => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm z⟩
      _ = ∫ z, f z * gammaA θ a (e z) ∂(tailExcLaw θ a).toMeasure := by
        rw [← tailExcLaw_map_restrictPair θ ha.2.le, ProbabilityMeasure.toMeasure_map,
          integral_map (measurable_restrictPair ha.2.le).aemeasurable hf.aestronglyMeasurable]
      _ = _ := integral_congr_ae (hgeq.mono fun z hz => by rw [hz])
  apply weighted_tendsto_of_cutoffs hP
    (fun k => absWeight μ B (rGreatest μ (q k)) (q k) a) g e
    (fun k => measurable_absWeight _ _ _ _ _) (hg0.max measurable_const) he
    (fun z => le_max_right _ _) hQ hΓ hgood
  intro x hx hxp z hz
  have ht := absWeight_contConv hc hne hap hB hnl ha hqtop hxp (hx.tendsto.comp hz)
  simpa only [g, max_eq_left (gammaA_nonneg hB.index_mem ha1 hxp)] using ht

theorem lem_absolue {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  exact lem_absolue_of_tail hc hne hap hB hnl
    (fun {_} ha => AbsolueTail.tail_absPair_tendsto hc hne hap hB ha) ha hqtop hq

end BGWLeaves.LeafLimits.Absolue
