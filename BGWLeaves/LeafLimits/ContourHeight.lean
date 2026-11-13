module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Conditioning
public import BGWLeaves.ClassicalLimits.Cited
public import BGWLeaves.ClassicalLimits.Perturbation
public import BGWLeaves.ClassicalLimits.WalkClock
public import BGWLeaves.LeafLimits.Absolue
public import BGWLeaves.LeafLimits.Helpers
public import BGWLeaves.Coding.Norming
public import BGW.StableTrees.Attraction.Norming
public import BGW.StableTrees.Attraction.TransformConvergence
public import BGW.StableTrees.ExactContourGlobal
public import BGW.StableTrees.ExactContourBasic
public import BGW.Skorokhod.OptionalGaps
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import BGW.StableTrees.RealAttractionBounds
public import BGW.StableTrees.UnitExcursionDensity

/-!
# M13 provider `ContourHeight`

Theorems 5.9(i) and 5.9(ii), with the frozen signatures. The local joint walk/height limit
uses Lemma 5.8 on a strictly larger horizon and Lemma 5.7. At random tree size, compact
height sets give the local contour comparison. Leaf-conditioned mirror invariance, reflection
at the true contour duration, and zero padding give terminal control; C11 then gives the
whole-interval contour limit. The global contour/height comparison gives the diagonal limit.
An equivalent monotone stable norming supplies the discrete estimates, and a scalar Slutsky
argument transfers the result to every norming in the frozen statement.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.ContourHeight


open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.LeafLimits.Absolue
open BGW.StableTrees.ExactContour
open Set
open scoped ENNReal NNReal Topology

private theorem mu0_bounds {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    0 < (μ 0).toReal ∧ (μ 0).toReal < 1 := by
  refine ⟨ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0), ?_⟩
  have hle : (μ 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  refine lt_of_le_of_ne hle fun heq => BGWLeaves.mu0_ne_one hc hne ?_
  exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top 0) ENNReal.one_ne_top).1
    (by simpa using heq)

private theorem cond_real_le_of_inter_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {L E F : Set Ω} (hL : MeasurableSet L) (h : L ∩ E ⊆ F) :
    (P[|L]).real E ≤ (P[|L]).real F := by
  have hm : P (L ∩ E) ≤ P (L ∩ F) := measure_mono (Set.subset_inter Set.inter_subset_left h)
  have hle : P[|L] E ≤ P[|L] F := by
    rw [cond_apply hL, cond_apply hL]
    gcongr
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- Lemma 5.6(ii) at the moving leaf fraction `b μ₀ r_n/n`. -/
private theorem tendsto_leafClock_div_leaf {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {b : ℝ} (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < |(treeLeafClock τ (b * (μ 0).toReal * rGreatest μ (q k)) : ℝ) /
        q k - b / (μ 0).toReal|}) atTop (𝓝 0) := by
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  let c := fun k => b * (μ 0).toReal * (rGreatest μ (q k) : ℝ) / q k
  have hct : Tendsto c atTop (𝓝 b) := by
    have ht := ((tendsto_rGreatest_div_leaf hp hp1).comp hqtop).const_mul
      (b * (μ 0).toReal)
    have hv : b * (μ 0).toReal * (1 / (μ 0).toReal) = b := by field_simp
    rw [hv] at ht
    exact ht.congr fun k => by dsimp only [c, Function.comp_apply]; ring
  let δ := min b (1 - b) / 8
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (lt_min hb.1 (sub_pos.mpr hb.2)) (by norm_num)
  have hδα : δ < min (b / 2) ((1 - b) / 2) := by
    have h1 := min_le_left b (1 - b)
    have h2 := min_le_right b (1 - b)
    dsimp [δ]
    exact lt_min (by linarith [hb.1]) (by linarith [hb.2])
  have hbad := (BGWLeaves.lem_CVf_ii hc hne hap hDA hb hδα).comp hqtop
  have hcin : ∀ᶠ k in atTop, c k ∈ Set.Ioo (b - δ) (b + δ) :=
    hct.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have hsmall : Tendsto (fun k => (q k : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_natCast_atTop_atTop.comp hqtop)
  have hR : Tendsto (fun k => (q k : ℝ) ^ (-(1 / 4 : ℝ)) +
      |c k / (μ 0).toReal - b / (μ 0).toReal|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero] using
      hsmall.add (((hct.div_const (μ 0).toReal).sub_const (b / (μ 0).toReal)).abs)
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hbad
  filter_upwards [hcin, hR.eventually (gt_mem_nhds hε), hqtop.eventually_ge_atTop 1]
    with k hck hRk hqk
  simp only [Function.comp_apply]
  rw [coe_leafTreeLaw (hq k)]
  apply cond_real_le_of_inter_subset (measurableSet_leafCountEvent (q k))
  rintro τ ⟨⟨t, rfl, _⟩, hE⟩
  refine ⟨t, rfl, c k, hck, ?_⟩
  by_contra hcd
  have hbound : |((treeLeafTime t ⌊c k * q k⌋₊).toNat : ℝ) / q k -
      c k / (μ 0).toReal| ≤ (q k : ℝ) ^ (-(1 / 4 : ℝ)) := by
    exact le_of_not_gt (not_or.mp hcd).2
  have hnR : (q k : ℝ) ≠ 0 := by exact_mod_cast (by omega : q k ≠ 0)
  have harg : c k * q k = b * (μ 0).toReal * rGreatest μ (q k) := by
    dsimp [c]
    field_simp [hnR]
  change ε < |(treeLeafClock t.toLocallyFinite
    (b * (μ 0).toReal * rGreatest μ (q k)) : ℝ) / q k - b / (μ 0).toReal| at hE
  simp only [treeLeafClock, toPlaneTree_toLocallyFinite, ← harg] at hE
  have hab := abs_sub_le (((treeLeafTime t ⌊c k * q k⌋₊).toNat : ℝ) / q k)
    (c k / (μ 0).toReal) (b / (μ 0).toReal)
  linarith

private theorem probability_continuous_pair {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {X Y : ∀ n, Ω n → ℝ} {c d : ℝ}
    (hX : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (X n ω) c}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (Y n ω) d}) atTop (𝓝 0))
    {G : ℝ × ℝ → ℝ} (hG : ContinuousAt G (c, d)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (G (X n ω, Y n ω)) (G (c, d))}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hG ε hε
  have hlim := (hX (δ / 2) (half_pos hδ)).add (hY (δ / 2) (half_pos hδ))
  simp only [zero_add] at hlim
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hlim
  apply (measureReal_mono (s₂ := {ω | δ / 2 < dist (X n ω) c} ∪
    {ω | δ / 2 < dist (Y n ω) d}) ?_).trans (measureReal_union_le _ _)
  intro ω hω
  by_contra hout
  have hx : dist (X n ω) c ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inl h))
  have hy : dist (Y n ω) d ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inr h))
  have hp : dist (X n ω, Y n ω) (c, d) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (hx.trans_lt (half_lt_self hδ)) (hy.trans_lt (half_lt_self hδ))
  exact (not_lt_of_ge (hclose hp).le) hω

private theorem probability_const {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {x : ℕ → ℝ} {c : ℝ}
    (hx : Tendsto x atTop (𝓝 c)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {_ω | ε < dist (x n) c})
      atTop (𝓝 0) := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_iff_dist_tendsto_zero.mp hx).eventually (gt_mem_nhds hε)] with n hn
  simp [not_lt_of_gt hn]

private theorem probability_continuous {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {X : ∀ n, Ω n → ℝ} {c : ℝ}
    (hX : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (X n ω) c}) atTop (𝓝 0))
    {G : ℝ → ℝ} (hG : ContinuousAt G c) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (G (X n ω)) (G c)}) atTop (𝓝 0) :=
  probability_continuous_pair P (X := X) (Y := fun _ _ => (0 : ℝ))
    (c := c) (d := 0) (G := fun p : ℝ × ℝ => G p.1) hX
    (probability_const P (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    (hG.comp continuous_fst.continuousAt)

private theorem probability_max_index {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {m : ∀ n, Ω n → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / q n) c}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((max (m n ω) 1 : ℕ) / (q n : ℝ)) c}) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n => 1 / (q n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hqtop
  have ht := probability_continuous_pair P hm (probability_const P hsmall)
    (continuous_fst.max continuous_snd).continuousAt
  simp only [max_eq_left hc.le] at ht
  intro ε hε
  apply (ht ε hε).congr'
  filter_upwards [hqtop.eventually_ge_atTop 1] with n hn
  congr 1
  ext ω
  have hnR : (0 : ℝ) < q n := by exact_mod_cast hn
  have heq : (max (m n ω) 1 : ℕ) / (q n : ℝ) =
      max ((m n ω : ℝ) / q n) (1 / (q n : ℝ)) := by
    by_cases hm0 : m n ω = 0
    · simp [hm0]
    · have hm1 : 1 ≤ m n ω := by omega
      rw [max_eq_left hm1, max_eq_left]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hm1) hnR.le
  change (ε < dist (max ((m n ω : ℝ) / q n) (1 / (q n : ℝ))) c) ↔
    (ε < dist ((max (m n ω) 1 : ℕ) / (q n : ℝ)) c)
  rw [heq]


private theorem probability_index_ratio {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {q r : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {m : ∀ n, Ω n → ℕ} {c : ℝ} (hc : 0 < c)
    (hr : Tendsto (fun n => (r n : ℝ) / q n) atTop (𝓝 c))
    (hm : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / q n) c}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / r n) 1}) atTop (𝓝 0) := by
  have ht := probability_continuous_pair P (G := fun p : ℝ × ℝ => p.1 / p.2) hm (probability_const P hr)
    (continuous_fst.continuousAt.div continuous_snd.continuousAt hc.ne')
  simp only [div_self hc.ne'] at ht
  intro ε hε
  apply (ht ε hε).congr'
  filter_upwards [hqtop.eventually (eventually_ne_atTop (0 : ℕ))] with n hn
  congr 1
  ext ω
  change (ε < dist (((m n ω : ℝ) / q n) / ((r n : ℝ) / q n)) 1) ↔
    (ε < dist ((m n ω : ℝ) / r n) 1)
  rw [div_div_div_cancel_right₀ (show (q n : ℝ) ≠ 0 by exact_mod_cast hn)]

private theorem probability_norming_ratio {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) {r : ℕ → ℕ} (hrtop : Tendsto r atTop atTop)
    {m : ∀ n, Ω n → ℕ}
    (hm : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / r n) 1}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (B (m n ω) / B (r n)) 1}) atTop (𝓝 0) := by
  intro ε hε
  have hp : ContinuousAt (fun x : ℝ => x ^ (1 / θ)) 1 :=
    Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
  obtain ⟨η, hη, hpη⟩ := Metric.continuousAt_iff.mp hp (ε / 2) (half_pos hε)
  let δ := min (η / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (half_pos hη) (by norm_num)
  have hδη : δ < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨N, hN⟩ := hB.uniform_ratio (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 2) (ε / 2) (half_pos hε)
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ (hm δ hδ)
  filter_upwards [hrtop.eventually_ge_atTop N, hrtop.eventually_ge_atTop 1] with n hn hn1
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  by_contra hnot
  have hrat : |(m n ω : ℝ) / r n - 1| ≤ δ := by
    simpa only [Real.dist_eq] using le_of_not_gt hnot
  have hrpos : (0 : ℝ) < r n := by exact_mod_cast hn1
  have hbds := abs_le.mp hrat
  have hlo : (1 / 2 : ℝ) * r n ≤ m n ω :=
    (le_div_iff₀ hrpos).mp (by linarith [hbds.1])
  have hhi : (m n ω : ℝ) ≤ 2 * r n :=
    (div_le_iff₀ hrpos).mp (by linarith [hbds.2])
  have happrox := hN (r n) hn (m n ω) hlo hhi
  have hpclose : |((m n ω : ℝ) / r n) ^ (1 / θ) - 1| < ε / 2 := by
    have hdist : dist ((m n ω : ℝ) / r n) 1 < η := by
      rw [Real.dist_eq]
      exact hrat.trans_lt hδη
    simpa only [Real.dist_eq, Real.one_rpow] using hpη hdist
  have htri := abs_sub_le (B (m n ω) / B (r n))
    (((m n ω : ℝ) / r n) ^ (1 / θ)) 1
  change ε < dist (B (m n ω) / B (r n)) 1 at hω
  rw [Real.dist_eq] at hω
  linarith


private noncomputable def sizePair (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :=
  TailPair.treePairPath B (treeSize τ) a τ

private theorem measurable_sizePair (B : ℕ → ℝ) (a : ℝ≥0) : Measurable (sizePair B a) :=
  measurable_comp_nat measurable_treeSize (fun n => TailPair.measurable_treePairPath B n a)

private noncomputable def clockScale (p : ℝ) (r : ℕ) (b : ℝ≥0) (hb : 0 < (b : ℝ))
    (τ : LocallyFinite.Tree) : Set.Ioi (0 : ℝ) :=
  ⟨(b : ℝ) * (max (treeSize τ) 1 : ℕ) /
      (max (treeLeafClock τ ((b : ℝ) * p * r)) 1 : ℕ),
    div_pos (mul_pos hb (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)))
      (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))⟩

private theorem measurable_clockScale (p : ℝ) (r : ℕ) (b : ℝ≥0) (hb : 0 < (b : ℝ)) :
    Measurable (fun τ => (clockScale p r b hb τ : ℝ)) := by
  exact (measurable_const.mul
    ((measurable_from_nat (f := fun z : ℕ => ((max z 1 : ℕ) : ℝ))).comp
      measurable_treeSize)).div
    ((measurable_from_nat (f := fun z : ℕ => ((max z 1 : ℕ) : ℝ))).comp
      (measurable_treeLeafClock _))

private theorem scale_absPair_eq_sizePair (p : ℝ) (B : ℕ → ℝ) {r : ℕ}
    (hr : 0 < r) (hBr : B r ≠ 0) (a b : ℝ≥0) (hb : 0 < (b : ℝ))
    (τ : LocallyFinite.Tree) (hm : 0 < treeLeafClock τ ((b : ℝ) * p * r))
    (hz : 0 < treeSize τ) (S : Set.Ioi (0 : ℝ))
    (hS : (S : ℝ) = b * treeSize τ / treeLeafClock τ ((b : ℝ) * p * r))
    (hSa : (S : ℝ) * a ≤ b) :
    (Skorokhod.timeSpaceScale (a : ℝ) b.coe_nonneg
        ((absPair p B r b hb τ).1, B r / B (treeSize τ), S),
      Skorokhod.timeSpaceScaleC (a : ℝ) b.coe_nonneg
        ((absPair p B r b hb τ).2, (B (treeSize τ) / B r) * (r / (treeSize τ : ℝ)), S)) =
      sizePair B a τ := by
  let m := treeLeafClock τ ((b : ℝ) * p * r)
  let z := treeSize τ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast hz.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have htime (u : Set.Icc (0 : ℝ) a) : (S : ℝ) * u ≤ b :=
    (mul_le_mul_of_nonneg_left u.2.2 S.2.le).trans hSa
  have harg (u : Set.Icc (0 : ℝ) a) :
      (m : ℝ) * (1 / (b : ℝ) * ((S : ℝ) * u)) = (z : ℝ) * u := by
    rw [hS]
    dsimp only [m, z] at hmR ⊢
    field_simp [hmR, hb.ne']
  apply Prod.ext
  · apply Skorokhod.ext
    intro u
    have hin : 1 / (b : ℝ) * ((S : ℝ) * u) ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hb]
      exact htime u
    change B r / B z * (1 *
      (BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq τ)
        ⌊(m : ℝ) * min (1 / (b : ℝ) * min ((S : ℝ) * u) b) 1⌋₊ / B r)) =
      BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq τ)
        ⌊(z : ℝ) * u⌋₊ / B z
    rw [min_eq_left (htime u), min_eq_left hin, harg u, one_mul]
    exact div_mul_div_cancel₀' hBr _ _
  · apply ContinuousMap.ext
    intro u
    change (B z / B r * (r / (z : ℝ))) *
        (B r / r * TailPair.treeHeightLin τ ((m : ℝ) * min ((S : ℝ) * u) b / b)) =
      TailPair.treeHeightPath B z a τ u
    rw [min_eq_left (htime u)]
    have harg' : (m : ℝ) * ((S : ℝ) * u) / b = (z : ℝ) * u := by
      calc
        _ = (m : ℝ) * (1 / (b : ℝ) * ((S : ℝ) * u)) := by ring
        _ = _ := harg u
    rw [harg']
    simp only [TailPair.treeHeightPath, dite_eq_left (TailPair.continuous_treeHeightLin τ),
      ContinuousMap.coe_mk]
    field_simp [hBr, hrR, hzR]


private theorem probability_clockScale {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {b : ℝ≥0} (hb : b ∈ Set.Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    ∀ ε > 0, Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < dist (clockScale (μ 0).toReal (rGreatest μ (q k)) b
        (NNReal.coe_pos.mpr hb.1) τ : ℝ) 1}) atTop (𝓝 0) := by
  let P := fun k => leafTreeLaw μ (q k)
  obtain ⟨hp, _⟩ := mu0_bounds hc hne
  have hb0 : (0 : ℝ) < b := NNReal.coe_pos.mpr hb.1
  have hb1 : (b : ℝ) < 1 := NNReal.coe_lt_coe.mpr hb.2
  have hsize : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist ((treeSize τ : ℝ) / q k) (1 / (μ 0).toReal)}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [Real.dist_eq] using Helpers.tendsto_treeSize_div_leaf hc hne hap hDA hqtop hq hε
  have hclock : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist ((treeLeafClock τ ((b : ℝ) * (μ 0).toReal * rGreatest μ (q k)) : ℝ) /
        q k) ((b : ℝ) / (μ 0).toReal)}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [Real.dist_eq] using tendsto_leafClock_div_leaf hc hne hap hDA
      ⟨hb0, hb1⟩ hqtop hq hε
  have hmaxsize := probability_max_index P hqtop (one_div_pos.mpr hp) hsize
  have hmaxclock := probability_max_index P hqtop (div_pos hb0 hp) hclock
  have ht := probability_continuous_pair P (G := fun p : ℝ × ℝ => (b : ℝ) * p.1 / p.2)
    hmaxsize hmaxclock
    ((continuous_const.mul continuous_fst).continuousAt.div continuous_snd.continuousAt
      (div_pos hb0 hp).ne')
  have hv : (b : ℝ) * (1 / (μ 0).toReal) / ((b : ℝ) / (μ 0).toReal) = 1 := by
    field_simp [hb0.ne', hp.ne']
  rw [hv] at ht
  intro ε hε
  apply (ht ε hε).congr'
  filter_upwards [hqtop.eventually (eventually_ne_atTop (0 : ℕ))] with k hk
  congr 1
  ext τ
  have hkR : (q k : ℝ) ≠ 0 := by exact_mod_cast hk
  have heq : (b : ℝ) * ((max (treeSize τ) 1 : ℕ) / (q k : ℝ)) /
        ((max (treeLeafClock τ ((b : ℝ) * (μ 0).toReal * rGreatest μ (q k))) 1 : ℕ) /
          (q k : ℝ)) =
      (clockScale (μ 0).toReal (rGreatest μ (q k)) b hb0 τ : ℝ) := by
    rw [← mul_div_assoc, div_div_div_cancel_right₀ hkR]
    rfl
  change (ε < dist (_ : ℝ) 1) ↔ (ε < dist (_ : ℝ) 1)
  rw [heq]

private theorem ae_continuousAt_exc_prefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∀ᵐ z ∂((excLaw θ).map (restrictPair hb.le)).toMeasure,
      ContinuousAt (z.1 : Set.Icc (0 : ℝ) b → ℝ)
        ⟨(a : ℝ), a.coe_nonneg, NNReal.coe_le_coe.mpr hab⟩ := by
  let t : Set.Icc (0 : ℝ) b := ⟨a, a.coe_nonneg, NNReal.coe_le_coe.mpr hab⟩
  have hleft : ∀ᵐ z ∂((excLaw θ).map (restrictPair hb.le)).toMeasure,
      Function.leftLim (z.1 : Set.Icc (0 : ℝ) b → ℝ) t = z.1 t := by
    change ∀ᵐ z ∂(((unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1)).map
      (restrictPair hb.le)), _
    rw [Measure.map_map (measurable_restrictPair hb.le) (measurable_excursionPair θ 1)]
    apply (ae_map_iff ((measurable_restrictPair hb.le).comp
      (measurable_excursionPair θ 1)).aemeasurable
      (measurableSet_eq_fun ((Skorokhod.measurable_leftLim_eval t).comp measurable_fst)
        ((Skorokhod.measurable_eval t).comp measurable_fst))).mpr
    filter_upwards [levyExcLaw_noFixedJump hθ a ⟨ha, hab.trans_lt hb⟩] with e he
    change Function.leftLim (excursionRestrict b e) t = excursionRestrict b e t
    rw [leftLim_excursionRestrict b a ha hab e]
    exact he
  filter_upwards [hleft] with z hz
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (Skorokhod.isCadlag z.1).isRightContinuous _⟩
  change Tendsto z.1 (𝓝[<] t) (𝓝 (z.1 t))
  simpa only [hz] using (Skorokhod.isCadlag z.1).tendsto_nhdsLT_leftLim t


/-- Joint local walk/height convergence. The buffer `a < b < 1` is essential for Lemma 5.7. -/
private theorem tendsto_sizePair {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (sizePair B a)) atTop
      (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  change 0 < a ∧ a < 1 at ha
  let b : ℝ≥0 := (a + 1) / 2
  have hab : a < b := by
    change (a : ℝ) < (b : ℝ)
    dsimp [b]
    linarith [show (a : ℝ) < 1 from ha.2]
  have hb : b ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    refine ⟨ha.1.trans hab, ?_⟩
    change (b : ℝ) < 1
    dsimp [b]
    linarith [show (a : ℝ) < 1 from ha.2]
  have ha0 : (0 : ℝ) < a := NNReal.coe_pos.mpr ha.1
  have hb0 : (0 : ℝ) < b := NNReal.coe_pos.mpr hb.1
  have habR : (a : ℝ) < b := NNReal.coe_lt_coe.mpr hab
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  let P := fun k => leafTreeLaw μ (q k)
  let r := fun k => rGreatest μ (q k)
  let Z := fun k => absPair (μ 0).toReal B (r k) b hb0
  let K := fun k τ => (B (r k) / B (treeSize τ),
    B (treeSize τ) / B (r k) * ((r k : ℝ) / treeSize τ))
  let S := fun k => clockScale (μ 0).toReal (r k) b hb0
  let G := fun k τ =>
    (Skorokhod.timeSpaceScale (a : ℝ) b.coe_nonneg ((Z k τ).1, (K k τ).1, S k τ),
      Skorokhod.timeSpaceScaleC (a : ℝ) b.coe_nonneg ((Z k τ).2, (K k τ).2, S k τ))
  have hrtop : Tendsto r atTop atTop := (tendsto_rGreatest hp hp1).comp hqtop
  have hrdet : Tendsto (fun k => (r k : ℝ) / q k) atTop (𝓝 (1 / (μ 0).toReal)) :=
    (tendsto_rGreatest_div_leaf hp hp1).comp hqtop
  have hsize : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist ((treeSize τ : ℝ) / q k) (1 / (μ 0).toReal)}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [Real.dist_eq] using Helpers.tendsto_treeSize_div_leaf hc hne hap hDA hqtop hq hε
  have hratio := probability_index_ratio P hqtop (one_div_pos.mpr hp) hrdet hsize
  have hBN := probability_norming_ratio P hB hrtop hratio
  have hK₁ := probability_continuous P (G := fun x : ℝ => 1 / x) hBN
    (continuousAt_const.div continuousAt_id one_ne_zero)
  simp only [one_div_div, div_one] at hK₁
  have hRinv := probability_continuous P (G := fun x : ℝ => 1 / x) hratio
    (continuousAt_const.div continuousAt_id one_ne_zero)
  simp only [one_div_div, div_one] at hRinv
  have hK₂ := probability_continuous_pair P (G := fun p : ℝ × ℝ => p.1 * p.2) hBN hRinv
    (continuous_fst.mul continuous_snd).continuousAt
  simp only [one_mul] at hK₂
  have hKerr : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist (K k τ) 1}) atTop (𝓝 0) := by
    intro ε hε
    have hlim := (hK₁ ε hε).add (hK₂ ε hε)
    simp only [zero_add] at hlim
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_) hlim
    have heq : {τ | ε < dist (K k τ) 1} =
        {τ | ε < dist (B (r k) / B (treeSize τ)) 1} ∪
          {τ | ε < dist (B (treeSize τ) / B (r k) * ((r k : ℝ) / treeSize τ)) 1} := by
      ext τ
      change ε < max _ _ ↔ (_ ∨ _)
      exact lt_max_iff
    rw [heq]
    exact measureReal_union_le _ _
  have hSerr := probability_clockScale hc hne hap hDA hb hqtop hq
  have hZm : ∀ k, Measurable (Z k) := fun k => measurable_absPair _ _ _ _ _
  have hBz : Measurable (fun τ => B (treeSize τ)) :=
    (measurable_from_nat (f := B)).comp measurable_treeSize
  have hzr : Measurable (fun τ => (treeSize τ : ℝ)) :=
    (measurable_from_nat (f := fun z : ℕ => (z : ℝ))).comp measurable_treeSize
  have hKm : ∀ k, Measurable (K k) := fun k =>
    (measurable_const.div hBz).prodMk ((hBz.div measurable_const).mul (measurable_const.div hzr))
  have hSm : ∀ k, Measurable (fun τ => (S k τ : ℝ)) := fun k => measurable_clockScale _ _ _ _
  have hGm : ∀ k, Measurable (G k) := fun k =>
    ((measurable_timeSpaceScale (a : ℝ) b.coe_nonneg).comp
      ((hZm k).fst.prodMk ((hKm k).fst.prodMk (hSm k).subtype_mk))).prodMk
    ((measurable_timeSpaceScaleC (a : ℝ) b.coe_nonneg).comp
      ((hZm k).snd.prodMk ((hKm k).snd.prodMk (hSm k).subtype_mk)))
  have hlim := ClassicalLimits.Perturbation.lem_CVproba_pair ha.1 hab P Z K S hZm hKm hSm
    ((excLaw θ).map (restrictPair hb.2.le))
    (BGWLeaves.LeafLimits.Absolue.lem_absolue hc hne hap hB hnl hb hqtop hq)
    (ae_continuousAt_exc_prefix hB.index_mem ha.1 hab.le hb.2) hKerr hSerr
  have hlimlaw : ((excLaw θ).map (restrictPair hb.2.le)).map (restrictPair hab.le) =
      (excLaw θ).map (restrictPair ha.2.le) := by
    apply Subtype.ext
    change ((excLaw θ).toMeasure.map (restrictPair hb.2.le)).map (restrictPair hab.le) =
      (excLaw θ).toMeasure.map (restrictPair ha.2.le)
    erw [Measure.map_map (measurable_restrictPair hab.le) (measurable_restrictPair hb.2.le)]
    rfl
  rw [hlimlaw] at hlim
  have herr : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist (sizePair B a τ) (G k τ)}) atTop (𝓝 0) := by
    intro ε hε
    let η := ((b : ℝ) - a) / (2 * a)
    have hη : 0 < η := div_pos (sub_pos.mpr habR) (mul_pos (by norm_num) ha0)
    let d := (b : ℝ) / (2 * (μ 0).toReal)
    have hd : 0 < d := div_pos hb0 (by positivity)
    have hclock : Tendsto (fun k => (P k).toMeasure.real
        {τ | d < dist ((treeLeafClock τ ((b : ℝ) * (μ 0).toReal * r k) : ℝ) / q k)
          ((b : ℝ) / (μ 0).toReal)}) atTop (𝓝 0) := by
      simpa only [Real.dist_eq] using tendsto_leafClock_div_leaf hc hne hap hDA
        ⟨hb0, NNReal.coe_lt_coe.mpr hb.2⟩ hqtop hq hd
    have hbad := (hSerr η hη).add hclock
    simp only [zero_add] at hbad
    refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hbad
    filter_upwards [hqtop.eventually_ge_atTop 1, hrtop.eventually_ge_atTop 1,
      hrtop.eventually hB.pos] with k hqk hrk hbr
    have hmem : ∀ᵐ τ ∂(P k).toMeasure, τ ∈ leafCountEvent (q k) := by
      rw [coe_leafTreeLaw (hq k)]
      exact ae_cond_mem (measurableSet_leafCountEvent _)
    have hsub : {τ | ε < dist (sizePair B a τ) (G k τ)} ≤ᵐ[(P k).toMeasure]
        ({τ | η < dist (S k τ : ℝ) 1} ∪
          {τ | d < dist ((treeLeafClock τ ((b : ℝ) * (μ 0).toReal * r k) : ℝ) / q k)
            ((b : ℝ) / (μ 0).toReal)}) := by
      filter_upwards [hmem] with τ hτ hbadτ
      by_contra hout
      have hsg : dist (S k τ : ℝ) 1 ≤ η := le_of_not_gt (fun h => hout (Or.inl h))
      have hcg : dist ((treeLeafClock τ ((b : ℝ) * (μ 0).toReal * r k) : ℝ) / q k)
          ((b : ℝ) / (μ 0).toReal) ≤ d := le_of_not_gt (fun h => hout (Or.inr h))
      have hqR : (0 : ℝ) < q k := by exact_mod_cast hqk
      have hratpos : (0 : ℝ) <
          (treeLeafClock τ ((b : ℝ) * (μ 0).toReal * r k) : ℝ) / q k := by
        rw [Real.dist_eq] at hcg
        have hh := (abs_le.mp hcg).1
        dsimp [d] at hh
        have hbd : (0 : ℝ) < b / (μ 0).toReal := div_pos hb0 hp
        have heq : (b : ℝ) / (2 * (μ 0).toReal) = (b / (μ 0).toReal) / 2 := by ring
        rw [heq] at hh
        linarith
      have hm : 0 < treeLeafClock τ ((b : ℝ) * (μ 0).toReal * r k) := by
        exact_mod_cast (div_pos_iff_of_pos_right hqR).mp hratpos
      have hz : 0 < treeSize τ := by
        obtain ⟨t, rfl, _⟩ := hτ
        rw [treeSize_toLocallyFinite]
        exact t.size_pos
      have hSeq : (S k τ : ℝ) = b * treeSize τ /
          treeLeafClock τ ((b : ℝ) * (μ 0).toReal * r k) := by
        change (b : ℝ) * (max (treeSize τ) 1 : ℕ) /
          (max (treeLeafClock τ ((b : ℝ) * (μ 0).toReal * r k)) 1 : ℕ) = _
        rw [max_eq_left (Nat.succ_le_iff.mpr hz), max_eq_left (Nat.succ_le_iff.mpr hm)]
      have hSa : (S k τ : ℝ) * a ≤ b := by
        rw [Real.dist_eq] at hsg
        have hsupper := (abs_le.mp hsg).2
        have heq : η * (a : ℝ) = ((b : ℝ) - a) / 2 := by
          dsimp [η]
          field_simp [ha0.ne']
        have hmul := mul_le_mul_of_nonneg_right (show (S k τ : ℝ) ≤ 1 + η by linarith) a.coe_nonneg
        nlinarith
      have hid : G k τ = sizePair B a τ :=
        scale_absPair_eq_sizePair (μ 0).toReal B (by omega : 0 < r k) hbr.ne'
          a b hb0 τ hm hz (S k τ) hSeq hSa
      change ε < dist (sizePair B a τ) (G k τ) at hbadτ
      rw [hid, dist_self] at hbadτ
      exact (not_lt.mpr hε.le) hbadτ
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
      (measureReal_union_le _ _)
  exact BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability P
    (fun _ => measurable_sizePair B a) hGm herr hlim

theorem thm_cvG_i {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => Skorokhod.restrict ha1.le (rescaledLuka (treeSize τ) (B (treeSize τ)) τ)))
      atTop (𝓝 ((levyExcLaw θ).map (Skorokhod.restrict ha1.le))) := by
  let a' : ℝ≥0 := ⟨a, ha0.le⟩
  have ha' : 0 < a' ∧ a' < 1 := ⟨ha0, ha1⟩
  have hj := tendsto_sizePair hc hne hap hB hnl ha' hqtop hq
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hj
    (continuous_fst : Continuous (fun p : Skorokhod.D (a' : ℝ) ℝ ×
      C(Set.Icc (0 : ℝ) a', ℝ) => p.1))
  have hseq (k : ℕ) : ((leafTreeLaw μ (q k)).map (sizePair B a')).map Prod.fst =
      (leafTreeLaw μ (q k)).map (fun τ => Skorokhod.restrict ha1.le
        (rescaledLuka (treeSize τ) (B (treeSize τ)) τ)) := by
    apply Subtype.ext
    change ((leafTreeLaw μ (q k)).toMeasure.map (sizePair B a')).map Prod.fst = _
    rw [Measure.map_map measurable_fst (measurable_sizePair B a')]
    rfl
  have hlim : ((excLaw θ).map (restrictPair ha'.2.le)).map Prod.fst =
      (levyExcLaw θ).map (Skorokhod.restrict ha1.le) := by
    apply Subtype.ext
    change ((excLaw θ).toMeasure.map (restrictPair ha'.2.le)).map Prod.fst = _
    erw [Measure.map_map measurable_fst (measurable_restrictPair ha'.2.le)]
    rw [← excLaw_map_fst θ]
    change _ = ((excLaw θ).toMeasure.map Prod.fst).map (Skorokhod.restrict ha1.le)
    erw [Measure.map_map (Skorokhod.measurable_restrict ha1.le) measurable_fst]
    rfl
  rw [hlim] at ht
  exact ht.congr fun k => hseq k

private theorem exists_stableDomain_ratio {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    ∃ B' : ℕ → ℝ, StableDomain μ θ B' ∧
      Tendsto (fun n => B n / B' n) atTop (𝓝 1) := by
  have hatt := BGWLeaves.Coding.Norming.isStableAttracted_of_isRealStableAttracted hB
  have hmean : Attraction.mean (stepLaw μ) = 0 := Attraction.mean_stepLaw hc
  have hattm : Attraction.IsStableAttracted (stepLaw μ) θ
      (Attraction.mean (stepLaw μ)) B := by rwa [hmean]
  have hcanm := Attraction.Norming.locallimit_i (stepLaw μ)
    (Attraction.stepLaw_lt_neg_one μ) (Attraction.integrable_stepLaw hc) ⟨B, hattm⟩
  have hmono := (Attraction.Norming.locallimit_ii (stepLaw μ)
    (Attraction.stepLaw_lt_neg_one μ) (Attraction.integrable_stepLaw hc) ⟨B, hattm⟩).1
  have hcan : Attraction.IsStableAttracted (stepLaw μ) θ 0
      (Attraction.norming (stepLaw μ) θ) := by rwa [hmean] at hcanm
  obtain ⟨B', hEq, hdom⟩ := hcan.exists_stableDomain hc hne hmono
  refine ⟨B', hdom, ?_⟩
  have hratio := Attraction.TransformConvergence.norming_ratio_tendsto_one
    (stepLaw μ) hatt hcan
  apply hratio.congr'
  filter_upwards [hEq] with n hn
  rw [hn]


private noncomputable def sizeHeight (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :=
  TailPair.treeHeightPath B (treeSize τ) a τ

private noncomputable def sizeContour (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :=
  ExactContour.treeContourPath B (treeSize τ) a τ

private theorem measurable_sizeHeight (B : ℕ → ℝ) (a : ℝ≥0) : Measurable (sizeHeight B a) :=
  measurable_comp_nat measurable_treeSize (fun n => TailPair.measurable_treeHeightPath B n a)

private theorem measurable_sizeContour (B : ℕ → ℝ) (a : ℝ≥0) : Measurable (sizeContour B a) :=
  measurable_comp_nat measurable_treeSize (fun n => ExactContour.measurable_treeContourPath B n a)

private theorem tendsto_sizeHeight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (sizeHeight B a)) atTop
      (𝓝 (((excLaw θ).map (restrictPair ha.2.le)).map Prod.snd)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_sizePair hc hne hap hB hnl ha hqtop hq) continuous_snd
  have heq (k : ℕ) : ((leafTreeLaw μ (q k)).map (sizePair B a)).map Prod.snd =
      (leafTreeLaw μ (q k)).map (sizeHeight B a) := by
    apply Subtype.ext
    change ((leafTreeLaw μ (q k)).toMeasure.map (sizePair B a)).map Prod.snd = _
    rw [Measure.map_map measurable_snd (measurable_sizePair B a)]
    rfl
  exact ht.congr fun k => heq k

private theorem compact_containment {a : ℝ≥0}
    {P : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) a, ℝ)} {Q : ProbabilityMeasure C(Set.Icc (0 : ℝ) a, ℝ)}
    (hP : Tendsto P atTop (𝓝 Q)) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set C(Set.Icc (0 : ℝ) a, ℝ), IsCompact K ∧
      ∀ n, (P n).toMeasure Kᶜ ≤ ENNReal.ofReal η := by
  have hc : IsCompact (insert Q (Set.range P)) := hP.isCompact_insert_range
  have ht := isTightMeasureSet_of_isCompact_closure
    (S := insert Q (Set.range P)) (by rw [hc.isClosed.closure_eq]; exact hc)
  obtain ⟨K, hK, hp⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  refine ⟨K, hK, fun n => ?_⟩
  exact hp (P n).toMeasure ⟨P n, Set.mem_insert_of_mem _ (Set.mem_range_self n), rfl⟩

private theorem tendsto_prefix_contour_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < ExactContour.contourHeightError B (treeSize τ) a τ}) atTop (𝓝 0) := by
  let a' : ℝ≥0 := (a + 1) / 2
  have haa' : a < a' := by
    change (a : ℝ) < (a' : ℝ)
    dsimp [a']
    linarith [show (a : ℝ) < 1 from ha.2]
  have ha' : a' ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    refine ⟨ha.1.trans haa', ?_⟩
    change (a' : ℝ) < 1
    dsimp [a']
    linarith [show (a : ℝ) < 1 from ha.2]
  have ht := tendsto_sizeHeight h.critical h.nondegenerate hap h.isRealStableAttracted hnl ha' hqtop hq
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K, hK, hp⟩ := compact_containment ht (half_pos hη)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ExactContour.eventually_contourHeightError_le_of_compact h haa' ha'.2 K hK hε)
  filter_upwards [hqtop.eventually_ge_atTop N] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hmem : ∀ᵐ τ ∂(leafTreeLaw μ (q k)).toMeasure, τ ∈ leafCountEvent (q k) := by
    rw [coe_leafTreeLaw (hq k)]
    exact ae_cond_mem (measurableSet_leafCountEvent _)
  have hsub : {τ | ε < ExactContour.contourHeightError B (treeSize τ) a τ} ≤ᵐ[
      (leafTreeLaw μ (q k)).toMeasure] {τ | sizeHeight B a' τ ∉ K} := by
    filter_upwards [hmem] with τ hτ hbad
    intro hgood
    obtain ⟨t, rfl, ht⟩ := hτ
    have hqsize : q k ≤ t.size := ht ▸ t.degreeCount_le_size 0
    have hbound := hN t.size (hk.trans hqsize) t rfl
    dsimp only [sizeHeight] at hgood
    rw [treeSize_toLocallyFinite] at hgood hbad
    exact (not_le_of_gt hbad) (hbound hgood)
  have hpK := hp k
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_sizeHeight B a') hK.measurableSet.compl] at hpK
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono_ae hsub).trans hpK)
  rw [ENNReal.toReal_ofReal (half_pos hη).le] at hr
  exact hr.trans_lt (half_lt_self hη)

private theorem tendsto_sizeContour_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (sizeContour B a)) atTop
      (𝓝 (((excLaw θ).map (restrictPair ha.2.le)).map Prod.snd)) := by
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => leafTreeLaw μ (q k)) (fun _ => measurable_sizeContour B a)
    (fun _ => measurable_sizeHeight B a) ?_
    (tendsto_sizeHeight h.critical h.nondegenerate hap h.isRealStableAttracted hnl ha hqtop hq)
  intro ε hε
  simpa only [sizeContour, sizeHeight, ExactContour.contourHeightError_eq_dist] using
    tendsto_prefix_contour_error h hap hnl ha hqtop hq hε

open scoped Classical in
private theorem bienaymeLaw_finiteTreeEvent_eq_tsum (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (Q : PlaneTree → Prop) :
    LocallyFinite.bienaymeLaw ν (BGWLeaves.finiteTreeEvent Q) =
      ∑' t : PlaneTree, if Q t then PlaneTree.weight (fun d => ν {d}) t else 0 := by
  have hA : MeasurableSet (BGWLeaves.finiteTreeEvent Q) := by
    have hEq : BGWLeaves.finiteTreeEvent Q = PlaneTree.toLocallyFinite '' {t : PlaneTree | Q t} := by
      ext T
      simp only [BGWLeaves.finiteTreeEvent, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨t, rfl, ht⟩
        exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, rfl, ht⟩
    rw [hEq]
    exact (Set.to_countable _).image _ |>.measurableSet
  have hsub : BGWLeaves.finiteTreeEvent Q ⊆ {T : LocallyFinite.Tree | FiniteVertices T} := by
    rintro T ⟨t, rfl, -⟩
    exact t.finiteVertices_toLocallyFinite
  have h : LocallyFinite.bienaymeLaw ν (BGWLeaves.finiteTreeEvent Q) =
      (LocallyFinite.bienaymeLaw ν).restrict {T : LocallyFinite.Tree | FiniteVertices T}
        (BGWLeaves.finiteTreeEvent Q) := by
    rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hsub]
  rw [h, LocallyFinite.bienaymeLaw_restrict_finiteVertices, Measure.sum_apply _ hA]
  refine tsum_congr fun t => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases ht : Q t
  · have hmem : t.toLocallyFinite ∈ BGWLeaves.finiteTreeEvent Q := ⟨t, rfl, ht⟩
    simp [hmem, ht]
  · have hmem : t.toLocallyFinite ∉ BGWLeaves.finiteTreeEvent Q := by
      rintro ⟨s, hs, hq⟩
      exact ht (PlaneTree.toLocallyFinite_injective hs ▸ hq)
    simp [hmem, ht]


private theorem degreeCount_mirror (t : PlaneTree) (k : ℕ) :
    t.mirror.degreeCount k = t.degreeCount k := by
  induction t with
  | node ts ih =>
    simp only [PlaneTree.degreeCount, PlaneTree.mirror_node, PlaneTree.degrees_node,
      List.length_reverse, List.length_map, List.count_cons, List.count_flatten,
      List.map_reverse, List.sum_reverse, List.map_map]
    congr 1
    exact congrArg List.sum (List.map_congr_left fun t ht => ih t ht)

private theorem map_treeMirror_leafTreeLaw {μ : PMF ℕ} {n : ℕ}
    (hadm : LeafAdmissible μ n) :
    (leafTreeLaw μ n).map ExactContour.treeMirror = leafTreeLaw μ n := by
  classical
  apply Subtype.ext
  change (leafTreeLaw μ n).toMeasure.map ExactContour.treeMirror = (leafTreeLaw μ n).toMeasure
  simp only [coe_leafTreeLaw hadm]
  ext A hA
  rw [Measure.map_apply ExactContour.measurable_treeMirror hA,
    cond_apply (measurableSet_leafCountEvent n), cond_apply (measurableSet_leafCountEvent n)]
  congr 1
  have heq (D : Set LocallyFinite.Tree) : leafCountEvent n ∩ D =
      finiteTreeEvent (fun t => t.degreeCount 0 = n ∧ t.toLocallyFinite ∈ D) := by
    ext τ
    constructor
    · rintro ⟨⟨t, rfl, ht⟩, hD⟩
      exact ⟨t, rfl, ht, hD⟩
    · rintro ⟨t, rfl, ht, hD⟩
      exact ⟨⟨t, rfl, ht⟩, hD⟩
  rw [heq, heq, bienaymeLaw_finiteTreeEvent_eq_tsum,
    bienaymeLaw_finiteTreeEvent_eq_tsum]
  let e : PlaneTree ≃ PlaneTree :=
    ⟨PlaneTree.mirror, PlaneTree.mirror, PlaneTree.mirror_mirror, PlaneTree.mirror_mirror⟩
  rw [← e.tsum_eq]
  apply tsum_congr
  intro t
  simp only [e, Equiv.coe_fn_mk, degreeCount_mirror, Set.mem_preimage,
    ExactContour.treeMirror_toLocallyFinite, PlaneTree.mirror_mirror, PlaneTree.weight_mirror]
  by_cases hh : t.degreeCount 0 = n ∧ t.toLocallyFinite ∈ A <;> simp only [hh, ↓reduceIte]

private def initialExceed (a : ℝ≥0) (δ ε : ℝ) : Set C(Icc (0 : ℝ) (a : ℝ), ℝ) :=
  {f | ∃ t : Icc (0 : ℝ) (a : ℝ), (t : ℝ) ≤ δ ∧ ε < f t}

private theorem isOpen_initialExceed (a : ℝ≥0) (δ ε : ℝ) :
    IsOpen (initialExceed a δ ε) := by
  have he : initialExceed a δ ε = ⋃ t : Icc (0 : ℝ) (a : ℝ),
      ⋃ (_ : (t : ℝ) ≤ δ), {f : C(Icc (0 : ℝ) (a : ℝ), ℝ) | ε < f t} := by
    ext f
    simp [initialExceed]
  rw [he]
  exact isOpen_iUnion fun t => isOpen_iUnion fun _ =>
    isOpen_lt continuous_const (continuous_eval_const t)


private theorem terminal_reflection (B : ℕ → ℝ) {n : ℕ} (t : PlaneTree) (ht : t.size = n)
    {δ ε : ℝ} (hδ : δ ≤ 1 / 2) (hε : 0 < ε)
    (hbad : ∃ x : Icc (0 : ℝ) 1, 1 - δ ≤ (x : ℝ) ∧
      ε < B n / n * treeContourLin t.toLocallyFinite (2 * (n : ℝ) * (x : ℝ))) :
    treeContourPath B n (1 / 2) (treeMirror t.toLocallyFinite) ∈ initialExceed (1 / 2) δ ε := by
  obtain ⟨x, hx, hbad⟩ := hbad
  rw [treeContourLin_toLocallyFinite] at hbad
  have hn : (0 : ℝ) < n := by rw [← ht]; exact_mod_cast PlaneTree.size_pos t
  have hN : ((2 * (t.size - 1) : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_mul, Nat.cast_sub (by have := PlaneTree.size_pos t; omega), ht]
    norm_num
    ring
  have htime : 2 * (n : ℝ) * (x : ℝ) < 2 * (n : ℝ) - 2 := by
    by_contra hnot
    have hh := PlaneTree.contourLin_of_end_le t (s := 2 * (n : ℝ) * (x : ℝ))
      (by rw [hN]; exact le_of_not_gt hnot)
    rw [hh, mul_zero] at hbad
    linarith
  let y : ℝ := (2 * (n : ℝ) - 2 - 2 * n * (x : ℝ)) / (2 * n)
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by positivity)
  have hyδ : y ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    have hh := mul_le_mul_of_nonneg_left hx hn.le
    nlinarith
  let s : Icc (0 : ℝ) ((1 / 2 : ℝ≥0) : ℝ) := ⟨y, hy0, by norm_num; linarith⟩
  refine ⟨s, hyδ, ?_⟩
  rw [treeMirror_toLocallyFinite, treeContourPath_toLocallyFinite]
  have hys : 2 * (n : ℝ) * (s : ℝ) = 2 * (n : ℝ) - 2 - 2 * n * (x : ℝ) := by
    dsimp [s, y]
    field_simp
  have hsizeR : 2 * ((t.size : ℝ) - 1) = 2 * (n : ℝ) - 2 := by rw [ht]; ring
  rw [hys, PlaneTree.contourLin_mirror t (by linarith)
    (by rw [hsizeR]; nlinarith [x.property.1]), hsizeR,
    show 2 * (n : ℝ) - 2 - (2 * n - 2 - 2 * n * (x : ℝ)) =
      2 * n * (x : ℝ) by ring]
  exact hbad


private theorem sizeContour_zero (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :
    sizeContour B a τ ⟨0, le_rfl, a.coe_nonneg⟩ = 0 := by
  rw [sizeContour, treeContourPath, dite_eq_left (continuous_treeContourLin _)]
  change B (treeSize τ) / treeSize τ * treeContourLin τ (2 * (treeSize τ : ℝ) * 0) = 0
  rw [mul_zero, treeContourLin]
  split_ifs
  · simp [PlaneTree.contourLin, PlaneTree.contourAt_zero]
  · simp

private theorem initial_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧ ∀ k,
      (leafTreeLaw μ (q k)).toMeasure.real
        ((sizeContour B (1 / 2)) ⁻¹' initialExceed (1 / 2) δ ε) ≤ η := by
  let a : ℝ≥0 := 1 / 2
  have ha : a ∈ Ioo (0 : ℝ≥0) 1 := by norm_num [a]
  obtain ⟨K, hK, hp⟩ := compact_containment
    (tendsto_sizeContour_prefix h hap hnl ha hqtop hq) hη
  let K' := K ∩ {f | f ⟨0, le_rfl, a.coe_nonneg⟩ = 0}
  have hK' : IsCompact K' := hK.inter_right (isClosed_eq (continuous_eval_const _) continuous_const)
  have hosc : ∃ δ > 0, ∀ f ∈ K', ∀ t : Icc (0 : ℝ) (a : ℝ),
      (t : ℝ) ≤ δ → |f t| ≤ ε := by
    let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
    have heval : Continuous (fun p : K' × Icc (0 : ℝ) (a : ℝ) => p.1.val p.2) := by fun_prop
    obtain ⟨d, hd, hbd⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous heval) ε hε
    refine ⟨d / 2, half_pos hd, ?_⟩
    intro f hf t ht
    have hdist : dist ((⟨f, hf⟩ : K'), t)
        ((⟨f, hf⟩ : K'), (⟨0, le_rfl, a.coe_nonneg⟩ : Icc (0 : ℝ) (a : ℝ))) < d := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq,
        Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
      exact ht.trans_lt (half_lt_self hd)
    have hh := hbd hdist
    change |f t - f ⟨0, le_rfl, a.coe_nonneg⟩| < ε at hh
    rw [hf.2, sub_zero] at hh
    exact hh.le
  obtain ⟨d, hd, hosc⟩ := hosc
  let δ := min d (1 / 2)
  refine ⟨δ, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro k
  have hsub : (sizeContour B a) ⁻¹' initialExceed a δ ε ⊆
      {τ | sizeContour B a τ ∉ K} := by
    rintro τ ⟨t, ht, hbad⟩ hmem
    have hh := hosc _ ⟨hmem, sizeContour_zero B a τ⟩ t (ht.trans (min_le_left _ _))
    exact (not_le_of_gt hbad) ((le_abs_self _).trans hh)
  have hpK := hp k
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_sizeContour B a) hK.measurableSet.compl] at hpK
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hpK)
  rw [ENNReal.toReal_ofReal hη.le] at hr
  exact hr

private theorem terminal_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧ ∀ k,
      (leafTreeLaw μ (q k)).toMeasure.real
        {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε < sizeContour B 1 τ t} ≤ η := by
  obtain ⟨δ, hδ, hδhalf, hp⟩ := initial_small h hap hnl hqtop hq hε hη
  refine ⟨δ, hδ, hδhalf, ?_⟩
  intro k
  let A := (sizeContour B (1 / 2)) ⁻¹' initialExceed (1 / 2) δ ε
  have hA : MeasurableSet A := (isOpen_initialExceed _ _ _).measurableSet.preimage
    (measurable_sizeContour B (1 / 2))
  have hsize : ∀ᵐ τ ∂(leafTreeLaw μ (q k)).toMeasure, τ ∈ leafCountEvent (q k) := by
    rw [coe_leafTreeLaw (hq k)]
    exact ae_cond_mem (measurableSet_leafCountEvent _)
  have hsub : {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε < sizeContour B 1 τ t} ≤ᵐ[
      (leafTreeLaw μ (q k)).toMeasure] treeMirror ⁻¹' A := by
    filter_upwards [hsize] with τ hτ hbad
    obtain ⟨t, rfl, _⟩ := hτ
    have hh : ∃ x : Icc (0 : ℝ) 1, 1 - δ ≤ (x : ℝ) ∧
        ε < B t.size / t.size * treeContourLin t.toLocallyFinite (2 * (t.size : ℝ) * (x : ℝ)) := by
      simpa only [sizeContour, treeSize_toLocallyFinite, treeContourPath,
        dite_eq_left (continuous_treeContourLin _), ContinuousMap.coe_mk] using hbad
    have hh' := terminal_reflection B t rfl hδhalf hε hh
    simpa only [A, Set.mem_preimage, sizeContour, treeMirror_toLocallyFinite,
      treeSize_toLocallyFinite, PlaneTree.size_mirror] using hh'
  have hmap : (leafTreeLaw μ (q k)).toMeasure (treeMirror ⁻¹' A) =
      (leafTreeLaw μ (q k)).toMeasure A := by
    rw [← Measure.map_apply measurable_treeMirror hA]
    exact congrArg (fun P : ProbabilityMeasure LocallyFinite.Tree => P.toMeasure A)
      (map_treeMirror_leafTreeLaw (hq k))
  have hle := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [hmap] at hle
  exact hle.trans (hp k)

private theorem contourLin_nonneg (t : PlaneTree) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ t.contourLin s := by
  have hf := Nat.floor_le hs
  have hfl := Nat.lt_floor_add_one s
  apply add_nonneg <;> apply mul_nonneg
  · linarith
  · positivity
  · linarith
  · positivity

private theorem sizeContour_nonneg {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (τ : LocallyFinite.Tree) (s : Icc (0 : ℝ) 1) :
    0 ≤ sizeContour B 1 τ s := by
  rw [sizeContour, treeContourPath, dite_eq_left (continuous_treeContourLin _)]
  change 0 ≤ B (treeSize τ) / treeSize τ * treeContourLin τ (2 * (treeSize τ : ℝ) * s)
  by_cases hz : treeSize τ = 0
  · simp [hz]
  apply mul_nonneg (div_nonneg (h.pos _ (Nat.pos_of_ne_zero hz)).le (Nat.cast_nonneg _))
  rw [treeContourLin]
  split_ifs
  · exact contourLin_nonneg _ (by nlinarith [s.property.1, Nat.cast_nonneg (α := ℝ) (treeSize τ)])
  · exact le_rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tendsto_sizeContour {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (sizeContour B 1)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
  let Y : LocallyFinite.Tree → C(Icc (0 : ℝ) 1, ℝ) := sizeContour B 1
  let ν : ProbabilityMeasure C(Icc (0 : ℝ) 1, ℝ) := (excLaw θ).map Prod.snd
  change Tendsto (fun k => (leafTreeLaw μ (q k)).map Y) atTop (𝓝 ν)
  let a : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2)
  have ha (j : ℕ) : 0 < a j ∧ a j < 1 := by
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hd : (0 : ℝ) < j + 2 := by positivity
    constructor
    · exact sub_pos.mpr ((div_lt_one hd).mpr (by linarith))
    · exact sub_lt_self _ (by positivity)
  have hatop : Tendsto a atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop).const_div_atTop (1 : ℝ))
    simpa only [sub_zero] using hh
  apply BGW.Skorokhod.tendsto_continuous_of_tendsto_restrict_of_oscillation
    (T := (1 : ℝ)) (fun k => leafTreeLaw μ (q k)) (fun _ => (show Measurable Y from measurable_sizeContour B 1))
    (by norm_num) (fun j => (ha j).1.le) (fun j => (ha j).2) hatop
  · intro j
    let a' : ℝ≥0 := ⟨a j, (ha j).1.le⟩
    have ha' : a' ∈ Ioo (0 : ℝ≥0) 1 := ⟨(ha j).1, (ha j).2⟩
    have ht := tendsto_sizeContour_prefix h hap hnl ha' hqtop hq
    have hseq (k : ℕ) : (leafTreeLaw μ (q k)).map
        (BGW.Skorokhod.restrictContinuous (ha j).2.le ∘ Y) =
        (leafTreeLaw μ (q k)).map (sizeContour B a') := by
      congr 1
      funext τ
      apply ContinuousMap.ext
      intro t
      dsimp only [Function.comp_def, BGW.Skorokhod.restrictContinuous, Y,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      simp only [sizeContour, treeContourPath, dite_eq_left (continuous_treeContourLin _),
        ContinuousMap.coe_mk]
    have hlim : ν.map
        (BGW.Skorokhod.restrictContinuous (ha j).2.le) =
        ((excLaw θ).map (restrictPair ha'.2.le)).map Prod.snd := by
      apply Subtype.ext
      change ((excLaw θ).toMeasure.map Prod.snd).map _ =
        ((excLaw θ).toMeasure.map (restrictPair ha'.2.le)).map Prod.snd
      erw [Measure.map_map (BGW.Skorokhod.lipschitzWith_one_restrictContinuous _).continuous.measurable
        measurable_snd, Measure.map_map measurable_snd (measurable_restrictPair _)]
      rfl
    erw [← hlim] at ht
    exact ht.congr fun k => (hseq k).symm
  · intro ε hε
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨δ, hδ, _, hp⟩ := terminal_small h hap hnl hqtop hq (half_pos hε) (half_pos hη)
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hatop.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith)))
    refine ⟨N, ?_⟩
    intro j hj
    have hnn : 0 ≤ limsup (fun k => (leafTreeLaw μ (q k)).toMeasure.real
        {τ | ε < ⨆ s : {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (Y τ s.val) (Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩)}) atTop :=
      le_limsup_of_frequently_le (Frequently.of_forall fun _ => measureReal_nonneg)
        (isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    apply lt_of_le_of_lt _ (half_lt_self hη)
    apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
    apply Eventually.of_forall
    intro k
    have hsub : {τ | ε < ⨆ s : {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
        dist (Y τ s.val) (Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩)} ⊆
        {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε / 2 < Y τ t} := by
      intro τ hbad
      by_contra hh
      have hb (t : Icc (0 : ℝ) 1) (ht : a j ≤ (t : ℝ)) : Y τ t ≤ ε / 2 :=
        le_of_not_gt (fun hb => hh ⟨t, (hN j hj).le.trans ht, hb⟩)
      have hdist : (⨆ s : {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (Y τ s.val) (Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩)) ≤ ε := by
        let : Nonempty {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)} :=
          ⟨⟨⟨a j, (ha j).1.le, (ha j).2.le⟩, le_rfl⟩⟩
        apply ciSup_le
        intro s
        rw [Real.dist_eq, abs_le]
        have hs0 := sizeContour_nonneg h τ s.val
        have ha0 := sizeContour_nonneg h τ ⟨a j, (ha j).1.le, (ha j).2.le⟩
        have hs := hb s.val s.property
        have haa := hb ⟨a j, (ha j).1.le, (ha j).2.le⟩ le_rfl
        change 0 ≤ Y τ s.val at hs0
        change 0 ≤ Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩ at ha0
        constructor <;> linarith
      exact (not_le_of_gt hbad) hdist
    exact (measureReal_mono hsub).trans (hp k)

private theorem tendsto_global_contour_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < contourHeightError B (treeSize τ) 1 τ}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K, hK, hp⟩ := compact_containment
    (tendsto_sizeContour h hap hnl hqtop hq) (half_pos hη)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_globalError_le_of_compact h K hK hε)
  filter_upwards [hqtop.eventually_ge_atTop N] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hmem : ∀ᵐ τ ∂(leafTreeLaw μ (q k)).toMeasure, τ ∈ leafCountEvent (q k) := by
    rw [coe_leafTreeLaw (hq k)]
    exact ae_cond_mem (measurableSet_leafCountEvent _)
  have hsub : {τ | ε < contourHeightError B (treeSize τ) 1 τ} ≤ᵐ[
      (leafTreeLaw μ (q k)).toMeasure] {τ | sizeContour B 1 τ ∉ K} := by
    filter_upwards [hmem] with τ hτ hbad
    intro hgood
    obtain ⟨t, rfl, ht⟩ := hτ
    have hqsize : q k ≤ t.size := ht ▸ t.degreeCount_le_size 0
    have hbound := hN t.size (hk.trans hqsize) t rfl
    dsimp only [sizeContour] at hgood
    rw [treeSize_toLocallyFinite] at hgood hbad
    exact (not_le_of_gt hbad) (hbound hgood)
  have hpK := hp k
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_sizeContour B 1) hK.measurableSet.compl] at hpK
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono_ae hsub).trans hpK)
  rw [ENNReal.toReal_ofReal (half_pos hη).le] at hr
  exact hr.trans_lt (half_lt_self hη)

set_option backward.isDefEq.respectTransparency false in
private theorem tendsto_contour_height_stableDomain {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ => (codingTriple B τ).2))
      atTop (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_sizeContour h hap hnl hqtop hq) (continuous_id.prodMk continuous_id)
  have hlim : ((excLaw θ).map Prod.snd).map (fun f => (f, f)) =
      (excLaw θ).map (fun p => (p.2, p.2)) := by
    apply Subtype.ext
    exact Measure.map_map (measurable_id.prodMk measurable_id) measurable_snd
  erw [hlim] at ht
  have hseq (k : ℕ) : ((leafTreeLaw μ (q k)).map (sizeContour B 1)).map (fun f => (f, f)) =
      (leafTreeLaw μ (q k)).map (fun τ => (sizeContour B 1 τ, sizeContour B 1 τ)) := by
    apply Subtype.ext
    exact Measure.map_map (measurable_id.prodMk measurable_id) (measurable_sizeContour B 1)
  have ht' := ht.congr fun k => hseq k
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => leafTreeLaw μ (q k)) (fun _ => measurable_snd.comp (measurable_codingTriple B))
    (fun _ => (measurable_sizeContour B 1).prodMk (measurable_sizeContour B 1)) ?_ ht'
  intro ε hε
  have heq (τ : LocallyFinite.Tree) : (codingTriple B τ).2 =
      (sizeContour B 1 τ, sizeHeight B 1 τ) := by
    simp only [codingTriple, rescaledContour_eq_treeContourPath,
      rescaledHeight_eq_treeHeightPath, sizeContour, sizeHeight]
  have herr := tendsto_global_contour_error h hap hnl hqtop hq hε
  simp only [contourHeightError_eq_dist] at herr
  simpa only [Function.comp_apply, heq, dist_prod_same_left, sizeContour, sizeHeight, dist_comm] using herr

private theorem probability_size_tendsto {μ : PMF ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {f : ℕ → ℝ} {c : ℝ} (hf : Tendsto f atTop (𝓝 c)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < dist (f (treeSize τ)) c}) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hf) ε hε)
  filter_upwards [hqtop.eventually_ge_atTop N] with k hk
  have hmem : ∀ᵐ τ ∂(leafTreeLaw μ (q k)).toMeasure, τ ∈ leafCountEvent (q k) := by
    rw [coe_leafTreeLaw (hq k)]
    exact ae_cond_mem (measurableSet_leafCountEvent _)
  have hz : (leafTreeLaw μ (q k)).toMeasure
      {τ | ε < dist (f (treeSize τ)) c} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hmem] with τ hτ
    obtain ⟨t, rfl, ht⟩ := hτ
    rw [treeSize_toLocallyFinite]
    exact not_lt_of_ge (hN t.size (hk.trans (ht ▸ t.degreeCount_le_size 0))).le
  simp only [Measure.real, hz, ENNReal.toReal_zero]

private theorem codingPair_scale {μ : PMF ℕ} {θ : ℝ} {B B' : ℕ → ℝ}
    (h : StableDomain μ θ B') (τ : LocallyFinite.Tree) :
    (codingTriple B τ).2 =
      ((B (treeSize τ) / B' (treeSize τ)) • (codingTriple B' τ).2.1,
       (B (treeSize τ) / B' (treeSize τ)) • (codingTriple B' τ).2.2) := by
  have hfactor : B (treeSize τ) / treeSize τ =
      (B (treeSize τ) / B' (treeSize τ)) * (B' (treeSize τ) / treeSize τ) := by
    by_cases hz : treeSize τ = 0
    · simp [hz]
    · field_simp [(h.pos _ (Nat.pos_of_ne_zero hz)).ne']
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    simp only [codingTriple, rescaledContour, ContinuousMap.coe_mk,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [hfactor, mul_assoc]
  · apply ContinuousMap.ext
    intro t
    simp only [codingTriple, rescaledHeight, ContinuousMap.coe_mk,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [hfactor, mul_assoc]

/-- Theorem 5.9(ii): joint contour/height convergence on the whole unit interval. -/
theorem thm_cvG_ii {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ => (codingTriple B τ).2))
      atTop (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  obtain ⟨B', hdom, hratio⟩ := exists_stableDomain_ratio hc hne hB
  let R : LocallyFinite.Tree → ℝ := fun τ => B (treeSize τ) / B' (treeSize τ)
  have hR : Measurable R :=
    (measurable_from_top : Measurable (fun n : ℕ => B n / B' n)).comp measurable_treeSize
  have ht := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error
    (fun k => leafTreeLaw μ (q k))
    (fun _ => measurable_snd.comp (measurable_codingTriple B')) (fun _ => hR)
    (tendsto_contour_height_stableDomain hdom hap hnl hqtop hq)
    (fun ε hε => probability_size_tendsto hqtop hq hratio hε)
  let G : (C(unitInterval, ℝ) × C(unitInterval, ℝ)) × ℝ →
      C(unitInterval, ℝ) × C(unitInterval, ℝ) := fun p => (p.2 • p.1.1, p.2 • p.1.2)
  have hG : Continuous G :=
    (continuous_snd.smul continuous_fst.fst).prodMk (continuous_snd.smul continuous_fst.snd)
  have hs := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ ht hG
  have hseq (k : ℕ) : ((leafTreeLaw μ (q k)).map
      (fun τ => ((codingTriple B' τ).2, R τ))).map G =
      (leafTreeLaw μ (q k)).map (fun τ => (codingTriple B τ).2) := by
    apply Subtype.ext
    change ((leafTreeLaw μ (q k)).toMeasure.map _).map G = _
    erw [Measure.map_map hG.measurable
      ((measurable_snd.comp (measurable_codingTriple B')).prodMk hR)]
    congr 1
    funext τ
    exact (codingPair_scale hdom τ).symm
  have hlim : (((excLaw θ).map (fun p => (p.2, p.2))).map
      (fun p => (p, (1 : ℝ)))).map G = (excLaw θ).map (fun p => (p.2, p.2)) := by
    apply Subtype.ext
    change ((((excLaw θ).toMeasure.map (fun p => (p.2, p.2))).map
      (fun p => (p, (1 : ℝ)))).map G) = _
    erw [Measure.map_map hG.measurable (measurable_id.prodMk measurable_const),
      Measure.map_map (hG.measurable.comp (measurable_id.prodMk measurable_const))
        (measurable_snd.prodMk measurable_snd)]
    simp only [Function.comp_def, G, one_smul, id_eq]
    rfl
  erw [hlim] at hs
  exact hs.congr fun k => hseq k

/-- Joint local walk/height convergence, retaining the coupling for Introduction (II). -/
theorem tendsto_treePairPath_treeSize {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
      (fun τ => TailPair.treePairPath B (treeSize τ) a τ)) atTop
      (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  exact tendsto_sizePair hc hne hap hB hnl ha hqtop hq

end BGWLeaves.LeafLimits.ContourHeight
