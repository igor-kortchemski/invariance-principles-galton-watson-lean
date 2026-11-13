module

public import BGWLeaves.GeneralAFunctional.TreeMarks
public import BGWLeaves.GeneralAFunctional.TreeSurvival

/-! Deterministic prefix marks under the total-size-tail tree law. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeMarkTail

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeLocal
open BGWLeaves.GeneralAFunctional.TreeMarks
open scoped ENNReal Topology Classical

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

theorem measurable_prefix_marks (A : Set ℕ) (m : ℕ) :
    Measurable (fun T => prefixMarks A (treePrefix m T)) :=
  (measurable_of_countable _).comp (measurable_treePrefix m)

/-- Passing from an iid prefix event to a tree conditioned on a size tail
costs at most the reciprocal total-size-tail mass. -/
theorem tail_prefix_marks_bound {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) {r m : ℕ} (hmr : m < r) (ε : ℝ) :
    (tailTreeLaw μ r).toMeasure.real
      {T | ε < |(prefixMarks A (treePrefix m T) : ℝ) / m - (μ.toMeasure A).toReal|} ≤
    (offspringSeqLaw μ).toMeasure.real
      {ω | ε < |(prefixMarks A (seqPrefix m ω) : ℝ) / m - (μ.toMeasure A).toReal|} /
        forestTail μ 1 r := by
  let E := {T : LocallyFinite.Tree | ε <
    |(prefixMarks A (treePrefix m T) : ℝ) / m - (μ.toMeasure A).toReal|}
  have hcount : Measurable (fun T => (prefixMarks A (treePrefix m T) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_prefix_marks A m)
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((hcount.div_const m).sub_const _))
  have hnum : (bienaymeLaw μ.toMeasure).real (Attraction.sizeGeEvent r ∩ E) ≤
      (offspringSeqLaw μ).toMeasure.real
        {ω | ε < |(prefixMarks A (seqPrefix m ω) : ℝ) / m - (μ.toMeasure A).toReal|} := by
    rw [← first_block_law μ hc hne, measureReal_def,
      Measure.map_apply measurable_blockLF.eval
        ((measurableSet_sizeGeEvent r).inter hE)]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [ae_ladderFinite μ hc hne] with ω hω
    intro h
    change (blockLF ω 0 ∈ Attraction.sizeGeEvent r) ∧ blockLF ω 0 ∈ E at h
    have hsz : r ≤ ladderTime ω 1 := by
      rw [blockLF, toLocallyFinite_mem_sizeGe] at h
      simpa only [first_block_size hω] using h.1
    change ε < |(prefixMarks A (seqPrefix m ω) : ℝ) / m - (μ.toMeasure A).toReal|
    have hbad := h.2
    change ε < |(prefixMarks A (treePrefix m (blockLF ω 0)) : ℝ) / m -
      (μ.toMeasure A).toReal| at hbad
    rwa [treePrefix_first_block hω m (by omega)] at hbad
  rw [tailTreeLaw_toMeasure μ r (bienaymeLaw_sizeGeEvent_ne_zero μ hc hne r),
    measureReal_def, cond_apply' hE, ENNReal.toReal_mul, ENNReal.toReal_inv,
    tailMass_eq_forestTail μ hc hne r]
  change (forestTail μ 1 r)⁻¹ * (bienaymeLaw μ.toMeasure).real
    (Attraction.sizeGeEvent r ∩ E) ≤ _
  rw [← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right hnum (forestTail_pos μ hc hne r).le

/-- Total-size-tail denominator with the canonical norming. -/
theorem normalized_tail_tendsto {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n => norming (stepLaw μ) θ n * forestTail μ 1 n) atTop
      (𝓝 (θ * Scalar.stableDensity θ 0)) := by
  have ht := (BGWLeaves.StableAnalysis.lem_locallimit hc hne hap hDA).2
  apply ht.congr
  intro n
  rw [← tailMass_eq_forestTail μ hc hne n]
  rfl

/-- Linear-prefix exponential errors survive total-size-tail conditioning. -/
theorem exp_div_tail_tendsto {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {r m : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) {b : ℝ} (hb : 0 < b)
    (hmr : Tendsto (fun k => (m k : ℝ) / r k) atTop (𝓝 b))
    {C c : ℝ} (hC : 0 ≤ C) (hc' : 0 < c) :
    Tendsto (fun k => C * Real.exp (-c * m k) / forestTail μ 1 (r k)) atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := hDA
  have hcan := isRealStableAttracted_norming hc hne ⟨a, ha⟩
  obtain ⟨K, hK, hbound⟩ := LeafLimits.Bridge.attracted_norming_poly_bound hcan
  have hnum : Tendsto (fun k => norming (stepLaw μ) θ (r k) *
      (C * Real.exp (-c * m k))) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => K * C * ((n : ℝ)^2 * Real.exp (-(c * b / 2) * n)))
        atTop (𝓝 0) := by
      have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (c * b / 2) (by positivity)).comp
        tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def, Real.rpow_ofNat, mul_zero] using ht.const_mul (K * C)
    apply squeeze_zero' ?_ ?_ (hp.comp hr)
    · filter_upwards [hr.eventually hcan.pos] with k hk
      positivity
    · filter_upwards [hr.eventually hbound,
        hmr.eventually (eventually_gt_nhds (half_lt_self hb)), hr.eventually_ge_atTop 1] with k hk hmk hrk
      have hrpos : (0 : ℝ) < r k := by exact_mod_cast hrk
      have hml : b / 2 * r k ≤ m k := ((lt_div_iff₀ hrpos).mp hmk).le
      have he : Real.exp (-c * m k) ≤ Real.exp (-(c * b / 2) * r k) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hbound' := mul_le_mul hk (mul_le_mul_of_nonneg_left he hC)
        (mul_nonneg hC (Real.exp_pos _).le) (by positivity : 0 ≤ K * (r k : ℝ)^2)
      dsimp only [Function.comp_def]
      convert hbound' using 1
      ring
  have hden := (normalized_tail_tendsto hc hne hap ⟨a, ha⟩).comp hr
  have hpos : 0 < θ * Scalar.stableDensity θ 0 :=
    mul_pos (by linarith [ha.alpha_mem.1]) (Scalar.stableDensity_zero_pos ha.alpha_mem)
  have ht := hnum.div hden hpos.ne'
  rw [zero_div] at ht
  apply ht.congr'
  filter_upwards [hr.eventually hcan.pos] with k hk
  dsimp only [Pi.div_apply, Function.comp_def]
  field_simp [hk.ne']

/-- Prefix mark proportions concentrate under the existing total-size-tail law (B). -/
theorem tail_prefix_marks_concentration {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ}
    (hA0 : μ.toMeasure A ≠ 0) (hA1 : μ.toMeasure A ≠ 1)
    {r m : ℕ → ℕ} (hr : Tendsto r atTop atTop) {b : ℝ} (hb : 0 < b)
    (hmr : Tendsto (fun k => (m k : ℝ) / r k) atTop (𝓝 b))
    (hlt : ∀ᶠ k in atTop, m k < r k) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (tailTreeLaw μ (r k)).toMeasure.real
      {T | ε < |(prefixMarks A (treePrefix (m k) T) : ℝ) / m k - (μ.toMeasure A).toReal|})
      atTop (𝓝 0) := by
  obtain ⟨c, hc', hbnd⟩ := prefix_marks_chernoff hA0 hA1 hε
  have hmtop : Tendsto m atTop atTop := by
    have ht := hmr.pos_mul_atTop hb (tendsto_natCast_atTop_atTop.comp hr)
    have he : ∀ᶠ k in atTop, ((m k : ℝ) / r k) * r k = m k := by
      filter_upwards [hr.eventually_ne_atTop 0] with k hk
      have hn : (r k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp
    exact tendsto_natCast_atTop_iff.mp (ht.congr' he)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (exp_div_tail_tendsto hc hne hap hDA hr hb hmr (C := 4) (by norm_num) hc')
  filter_upwards [hlt, hmtop.eventually_ge_atTop 1] with k hk hmk
  exact (tail_prefix_marks_bound hc hne A hk ε).trans
    (div_le_div_of_nonneg_right (hbnd (m k) hmk) (forestTail_pos μ hc hne (r k)).le)

/-- Prefix mark counts on a reference marked-count scale. In particular, when
`r_k/q_k → 1/μ(A)` and `m_k/r_k → b`, this gives `K_A(m_k)/q_k → b`. -/
theorem tail_prefix_marks_scaled {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ}
    (hA0 : μ.toMeasure A ≠ 0) (hA1 : μ.toMeasure A ≠ 1)
    {r m q : ℕ → ℕ} (hr : Tendsto r atTop atTop) (_hq : Tendsto q atTop atTop)
    {b t : ℝ} (hb : 0 < b)
    (hmr : Tendsto (fun k => (m k : ℝ) / r k) atTop (𝓝 b))
    (hmq : Tendsto (fun k => (m k : ℝ) / q k) atTop (𝓝 t))
    (hlt : ∀ᶠ k in atTop, m k < r k) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (tailTreeLaw μ (r k)).toMeasure.real
      {T | ε < |(prefixMarks A (treePrefix (m k) T) : ℝ) / q k - (μ.toMeasure A).toReal * t|})
      atTop (𝓝 0) := by
  let p := (μ.toMeasure A).toReal
  let L := |t| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hδ : 0 < ε / (2 * L) := by positivity
  have ht := tail_prefix_marks_concentration hc hne hap hDA hA0 hA1 hr hb hmr hlt hδ
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ ht
  have hdet : Tendsto (fun k => |p * ((m k : ℝ) / q k) - p * t|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using ((hmq.const_mul p).sub_const (p * t)).abs
  have hmtop : Tendsto m atTop atTop := by
    have ht' := hmr.pos_mul_atTop hb (tendsto_natCast_atTop_atTop.comp hr)
    have he : ∀ᶠ k in atTop, ((m k : ℝ) / r k) * r k = m k := by
      filter_upwards [hr.eventually_ne_atTop 0] with k hk
      have hn : (r k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp
    exact tendsto_natCast_atTop_iff.mp (ht'.congr' he)
  have htL : t < L := by dsimp [L]; linarith [le_abs_self t]
  filter_upwards [hmq.eventually (eventually_lt_nhds htL),
    hdet.eventually (eventually_lt_nhds (half_pos hε)),
    hmtop.eventually_ne_atTop 0] with k hratio hdk hmk
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro T hbad
  change ε < |(prefixMarks A (treePrefix (m k) T) : ℝ) / q k - p * t| at hbad
  change ε / (2 * L) < |(prefixMarks A (treePrefix (m k) T) : ℝ) / m k - p|
  by_contra hnot
  have hsmall : |(prefixMarks A (treePrefix (m k) T) : ℝ) / m k - p| ≤ ε / (2 * L) :=
    le_of_not_gt hnot
  have hmR : (m k : ℝ) ≠ 0 := by exact_mod_cast hmk
  have hid : (prefixMarks A (treePrefix (m k) T) : ℝ) / q k - p * t =
      ((prefixMarks A (treePrefix (m k) T) : ℝ) / m k - p) * ((m k : ℝ) / q k) +
        (p * ((m k : ℝ) / q k) - p * t) := by field_simp; ring
  have hratio0 : 0 ≤ (m k : ℝ) / q k := by positivity
  have hprod : |((prefixMarks A (treePrefix (m k) T) : ℝ) / m k - p) * ((m k : ℝ) / q k)| ≤ ε / 2 := by
    rw [abs_mul, abs_of_nonneg hratio0]
    calc
      _ ≤ (ε / (2 * L)) * L := mul_le_mul hsmall hratio.le hratio0 (by positivity)
      _ = _ := by field_simp
  rw [hid] at hbad
  have htriangle := abs_add_le
    (((prefixMarks A (treePrefix (m k) T) : ℝ) / m k - p) * ((m k : ℝ) / q k))
    (p * ((m k : ℝ) / q k) - p * t)
  linarith

end BGWLeaves.GeneralAFunctional.TreeMarkTail
