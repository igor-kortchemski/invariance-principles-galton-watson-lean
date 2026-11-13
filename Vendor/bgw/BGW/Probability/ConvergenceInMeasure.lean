/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Constructing and transferring limits in measure

General tools for convergence in measure on finite measures: absolutely continuous and mapped
measures, Cauchy completeness, joint fiber limits, uniform approximation, and diagonal extraction.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace BGW.Probability

/-- Convergence in measure transfers to a finite absolutely continuous measure along
any countably generated filter. -/
theorem tendstoInMeasure_of_absolutelyContinuous {Ω ι : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure ν] {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → Ω → ℝ} {g : Ω → ℝ} (hν : ν ≪ μ) (hf : ∀ i, Measurable (f i))
    (hconv : TendstoInMeasure μ f l g) : TendstoInMeasure ν f l g := by
  intro ε hε
  apply tendsto_of_seq_tendsto
  intro ns hns
  have hseq : TendstoInMeasure ν (fun n => f (ns n)) atTop g := by
    apply (exists_seq_tendstoInMeasure_atTop_iff
      (fun n => (hf (ns n)).aestronglyMeasurable)).mpr
    intro ks hks
    obtain ⟨ms, hms, hlim⟩ :=
      ((hconv.comp hns).comp hks.tendsto_atTop).exists_seq_tendsto_ae
    exact ⟨ms, hms, hν.ae_le hlim⟩
  exact hseq ε hε

/-- Convergence in measure on a pushforward measure is convergence of the composed tests. -/
theorem tendstoInMeasure_map_iff {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {p : Ω → Ξ} (hp : Measurable p)
    {f : ι → Ξ → ℝ} {g : Ξ → ℝ} {l : Filter ι}
    (hf : ∀ i, Measurable (f i)) (hg : Measurable g) :
    TendstoInMeasure (μ.map p) f l g ↔
      TendstoInMeasure μ (fun i x => f i (p x)) l (fun x => g (p x)) := by
  have he (i : ι) (ε : ℝ≥0∞) :
      μ.map p {x | ε ≤ edist (f i x) (g x)} =
        μ {x | ε ≤ edist (f i (p x)) (g (p x))} := by
    exact Measure.map_apply hp (measurableSet_le measurable_const ((hf i).edist hg))
  simp only [TendstoInMeasure, he]

/-- Existence of a measurable limit transfers through absolutely continuous prefix laws.
The original limit need not have been chosen as a function of the prefix. -/
theorem exists_tendstoInMeasure_of_prefix_absolutelyContinuous {Ω Ξ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ ν : Measure Ω} [IsFiniteMeasure ν]
    {p : Ω → Ξ} (hp : Measurable p) {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    {f : ι → Ξ → ℝ} {g : Ω → ℝ} (hf : ∀ i, Measurable (f i))
    (hconv : TendstoInMeasure μ (fun i x => f i (p x)) l g)
    (hν : ν.map p ≪ μ.map p) :
    ∃ L : Ω → ℝ, Measurable L ∧ TendstoInMeasure ν (fun i x => f i (p x)) l L := by
  obtain ⟨ns, _, hlim⟩ := hconv.exists_seq_tendsto_ae'
  let M : Ξ → ℝ := fun x => limsup (fun n => f (ns n) x) atTop
  have hM : Measurable M := Measurable.limsup fun n => hf (ns n)
  have heq : (fun x => M (p x)) =ᵐ[μ] g :=
    hlim.mono fun _ h => h.limsup_eq
  have hbase := (tendstoInMeasure_map_iff hp hf hM).mpr
    (TendstoInMeasure.congr_right heq.symm hconv)
  refine ⟨fun x => M (p x), hM.comp hp, ?_⟩
  exact (tendstoInMeasure_map_iff hp hf hM).mp
    (tendstoInMeasure_of_absolutelyContinuous hν hf hbase)

/-- A measurable real Cauchy family in a finite measure space has a measurable limit in measure. -/
theorem exists_tendstoInMeasure_of_cauchy {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {l : Filter ι} [l.NeBot]
    {f : ι → Ω → ℝ} (hf : ∀ i, Measurable (f i))
    (hc : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ≥0∞, 0 < η →
      ∃ S ∈ l, ∀ i ∈ S, ∀ j ∈ S, μ {x | δ ≤ dist (f i x) (f j x)} ≤ η) :
    ∃ L : Ω → ℝ, Measurable L ∧ TendstoInMeasure μ f l L := by
  classical
  let d : ℕ → ℝ := fun n => (1 / 2) ^ n
  let b : ℕ → ℝ≥0∞ := fun n => (2 : ℝ≥0∞)⁻¹ ^ n
  have hdpos (n : ℕ) : 0 < d n := pow_pos (by norm_num) n
  have hbpos (n : ℕ) : 0 < b n :=
    pos_iff_ne_zero.mpr (pow_ne_zero n (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0))
  choose S hSl hS using fun n => hc (d n) (hdpos n) (b n) (hbpos n)
  have hfinite (n : ℕ) : (⋂ k ∈ Finset.range (n + 1), S k) ∈ l :=
    Filter.biInter_mem (Finset.range (n + 1)).finite_toSet |>.mpr fun k _ => hSl k
  choose a ha using fun n => Filter.nonempty_of_mem (hfinite n)
  have hamem (n k : ℕ) (hkn : k ≤ n) : a n ∈ S k :=
    mem_iInter₂.mp (ha n) k (Finset.mem_range.mpr (by omega))
  let E : ℕ → Set Ω := fun n => {x | d n ≤ dist (f (a n) x) (f (a (n + 1)) x)}
  have hE (n : ℕ) : μ (E n) ≤ b n :=
    hS n (a n) (hamem n n le_rfl) (a (n + 1)) (hamem (n + 1) n (by omega))
  have hgeom : (∑' n, b n) ≠ ⊤ := by
    rw [show b = fun n => (2 : ℝ≥0∞)⁻¹ ^ n from rfl, ENNReal.tsum_geometric]
    norm_num
  let L : Ω → ℝ := fun x => limsup (fun n => f (a n) x) atTop
  have hL : Measurable L := Measurable.limsup fun n => hf (a n)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f (a n) x) atTop (𝓝 (L x)) := by
    filter_upwards [ae_eventually_notMem (ne_top_of_le_ne_top hgeom
      (ENNReal.tsum_le_tsum hE))] with x hx
    obtain ⟨N, hN⟩ := eventually_atTop.mp hx
    have hC : CauchySeq (fun n => f (a (n + N)) x) := by
      apply cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
      intro n
      have hn : dist (f (a (n + N)) x) (f (a (n + N + 1)) x) < d (n + N) :=
        lt_of_not_ge (hN (n + N) (by omega))
      have hdle : d (n + N) ≤ d n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      simpa only [one_mul, Nat.add_right_comm n 1 N] using hn.le.trans hdle
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hC
    have ht : Tendsto (fun n => f (a n) x) atTop (𝓝 z) :=
      (tendsto_add_atTop_iff_nat N).mp hz
    have hLx : L x = z := ht.limsup_eq
    rw [hLx]
    exact ht
  have hseq := tendstoInMeasure_of_tendsto_ae (fun n => (hf (a n)).aestronglyMeasurable) hlim
  refine ⟨L, hL, tendstoInMeasure_iff_dist.mpr fun δ hδ => ?_⟩
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  have hbzero : Tendsto b atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hgeom
  have hsumzero : Tendsto (fun n => b n + b n + b n) atTop (𝓝 0) := by
    simpa using (hbzero.add hbzero).add hbzero
  obtain ⟨m, hm⟩ := (hsumzero.eventually (eventually_lt_nhds hη)).exists
  let κ := b m
  obtain ⟨S', hS'l, hS'⟩ := hc (δ / 3) (by positivity) κ (hbpos m)
  have hdzero : Tendsto d atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hseqδ := (tendstoInMeasure_iff_dist.mp hseq) (δ / 3) (by positivity)
  obtain ⟨n, ⟨hdn, hbn⟩, hn⟩ := (((hdzero.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < δ / 3))).and
      (hbzero.eventually (eventually_lt_nhds (hbpos m)))).and
        (hseqδ.eventually (eventually_lt_nhds (hbpos m)))).exists
  obtain ⟨i, hi, hi'⟩ := Filter.nonempty_of_mem (inter_mem (hSl n) hS'l)
  have hmid : μ {x | δ / 3 ≤ dist (f i x) (f (a n) x)} ≤ κ := by
    refine le_trans (measure_mono ?_) ((hS n i hi (a n) (hamem n n le_rfl)).trans hbn.le)
    intro x hx
    exact hdn.le.trans hx
  filter_upwards [hS'l] with j hj
  calc
    μ {x | δ ≤ dist (f j x) (L x)} ≤
        μ {x | δ / 3 ≤ dist (f j x) (f i x)} +
          (μ {x | δ / 3 ≤ dist (f i x) (f (a n) x)} +
            μ {x | δ / 3 ≤ dist (f (a n) x) (L x)}) := by
      apply le_trans (measure_mono ?_)
        ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
      intro x hx
      change δ ≤ dist (f j x) (L x) at hx
      simp only [mem_union, mem_ofPred_eq]
      by_contra! h
      have ht := (dist_triangle (f j x) (f i x) (L x)).trans
        (add_le_add le_rfl (dist_triangle (f i x) (f (a n) x) (L x)))
      linarith only [hx, ht, h.1, h.2.1, h.2.2]
    _ ≤ κ + (κ + κ) := add_le_add (hS' j hj i hi') (add_le_add hmid hn.le)
    _ ≤ η := by simpa only [κ, add_assoc] using hm.le

/-- A convergent family satisfies the uniform-set Cauchy criterion in measure. -/
theorem tendstoInMeasure_cauchy {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {l : Filter ι} {F : ι → Ω → ℝ} {L : Ω → ℝ} (h : TendstoInMeasure μ F l L)
    (δ : ℝ) (hδ : 0 < δ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ A ∈ l, ∀ i ∈ A, ∀ j ∈ A, μ {x | δ ≤ dist (F i x) (F j x)} ≤ η := by
  have hκ : 0 < η / 2 := ENNReal.div_pos hη.ne' (by norm_num)
  have he := ((tendstoInMeasure_iff_dist.mp h) (δ / 2) (half_pos hδ)).eventually
    (eventually_lt_nhds hκ)
  refine ⟨{i | μ {x | δ / 2 ≤ dist (F i x) (L x)} < η / 2}, he, ?_⟩
  intro i hi j hj
  calc
    _ ≤ μ {x | δ / 2 ≤ dist (F i x) (L x)} +
        μ {x | δ / 2 ≤ dist (F j x) (L x)} := by
      apply le_trans (measure_mono ?_) (measure_union_le _ _)
      intro x hx
      change δ ≤ dist (F i x) (F j x) at hx
      simp only [mem_union, mem_ofPred_eq]
      by_contra! hn
      have ht := dist_triangle (F i x) (L x) (F j x)
      rw [dist_comm (L x) (F j x)] at ht
      linarith only [hx, ht, hn.1, hn.2]
    _ ≤ η / 2 + η / 2 := add_le_add hi.le hj.le
    _ = η := ENNReal.add_halves η

/-- Fiberwise convergence gives a jointly measurable limit on a finite restriction of a
product measure. No measurable choice of the individual fiber limits is assumed. -/
theorem exists_joint_tendstoInMeasure_of_fiber_limits {A Ω ι : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] (ν : Measure A) (μ : Measure Ω)
    [SFinite μ] {S : Set (A × Ω)} (hS : MeasurableSet S)
    [IsFiniteMeasure ((ν.prod μ).restrict S)] {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    (F : ι → A × Ω → ℝ) (hF : ∀ i, Measurable (F i))
    (hlim : ∀ᵐ s ∂ν, ∃ L : Ω → ℝ,
      TendstoInMeasure (μ.restrict {x | (s, x) ∈ S}) (fun i x => F i (s, x)) l L) :
    ∃ L : A × Ω → ℝ, Measurable L ∧ TendstoInMeasure ((ν.prod μ).restrict S) F l L := by
  apply exists_tendstoInMeasure_of_cauchy hF
  intro δ hδ η hη
  let E : ι × ι → Set (A × Ω) := fun p => {q | δ ≤ dist (F p.1 q) (F p.2 q)}
  have hE (p : ι × ι) : MeasurableSet (E p) :=
    measurableSet_le measurable_const ((hF p.1).dist (hF p.2))
  let b : A → ℝ≥0∞ := fun s => μ {x | (s, x) ∈ S}
  let v : ι × ι → A → ℝ≥0∞ := fun p s => μ {x | (s, x) ∈ E p ∩ S}
  have hv (p : ι × ι) : Measurable (v p) :=
    measurable_measure_prodMk_left ((hE p).inter hS)
  have hb : (∫⁻ s, b s ∂ν) ≠ ⊤ := by
    have heq : ((ν.prod μ).restrict S) univ = ∫⁻ s, b s ∂ν := by
      rw [Measure.restrict_apply_univ]
      exact Measure.prod_apply hS
    rw [← heq]
    exact measure_ne_top ((ν.prod μ).restrict S) univ
  have hvlim : ∀ᵐ s ∂ν, Tendsto (fun p => v p s) (l ×ˢ l) (𝓝 0) := by
    filter_upwards [hlim] with s hs
    obtain ⟨L, hL⟩ := hs
    apply ENNReal.tendsto_nhds_zero.mpr
    intro κ hκ
    obtain ⟨B, hBl, hB⟩ := tendstoInMeasure_cauchy hL δ hδ κ hκ
    filter_upwards [prod_mem_prod hBl hBl] with p hp
    have hsec : MeasurableSet {x | (s, x) ∈ E p} :=
      (measurable_const.prodMk measurable_id) (hE p)
    have heq : v p s = (μ.restrict {x | (s, x) ∈ S})
        {x | δ ≤ dist (F p.1 (s, x)) (F p.2 (s, x))} := by
      change v p s = (μ.restrict {x | (s, x) ∈ S}) {x | (s, x) ∈ E p}
      rw [Measure.restrict_apply hsec]
      rfl
    rw [heq]
    exact hB p.1 hp.1 p.2 hp.2
  have hdom := tendsto_lintegral_filter_of_dominated_convergence b
    (Eventually.of_forall hv)
    (Eventually.of_forall fun p => ae_of_all ν fun _ => measure_mono inter_subset_right)
    hb hvlim
  have htotal (p : ι × ι) : ((ν.prod μ).restrict S) (E p) = ∫⁻ s, v p s ∂ν := by
    rw [Measure.restrict_apply (hE p), Measure.prod_apply ((hE p).inter hS)]
    rfl
  have ht : Tendsto (fun p => ((ν.prod μ).restrict S) (E p)) (l ×ˢ l) (𝓝 0) := by
    simpa only [htotal, lintegral_zero] using hdom
  obtain ⟨B, hB, C, hC, hBC⟩ := mem_prod_iff.mp
    (ht.eventually (eventually_lt_nhds hη))
  refine ⟨B ∩ C, inter_mem hB hC, fun i hi j hj => ?_⟩
  have hh := hBC (show (i, j) ∈ B ×ˢ C from ⟨hi.1, hj.2⟩)
  exact hh.le

/-- A real family uniformly approximated in first moment by convergent families has a
measurable limit in measure. -/
theorem exists_tendstoInMeasure_of_uniform_approximation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : ℝ → Ω → ℝ) (G : ℕ → ℝ → Ω → ℝ)
    (L : ℕ → Ω → ℝ) (b : ℕ → ℝ≥0∞)
    (hF : ∀ ε, Measurable (F ε)) (hG : ∀ n ε, Measurable (G n ε))
    (hconv : ∀ n, TendstoInMeasure μ (G n) (𝓝[>] (0 : ℝ)) (L n))
    (hb : Tendsto b atTop (𝓝 0))
    (herr : ∀ n ε, 0 < ε →
      ∫⁻ x, ENNReal.ofReal (dist (F ε x) (G n ε x)) ∂μ ≤ b n) :
    ∃ H : Ω → ℝ, Measurable H ∧ TendstoInMeasure μ F (𝓝[>] (0 : ℝ)) H := by
  apply exists_tendstoInMeasure_of_cauchy hF
  intro δ hδ η hη
  let κ := η / 2 / 2
  have hκ : 0 < κ := ENNReal.div_pos (ENNReal.div_pos hη.ne' (by norm_num)).ne'
    (by norm_num)
  have hsum : κ + κ + (κ + κ) = η := by
    simp only [κ, ENNReal.add_halves]
  let d := δ / 4
  have hd : 0 < d := by dsimp [d]; positivity
  have hdne : ENNReal.ofReal d ≠ 0 := (ENNReal.ofReal_pos.mpr hd).ne'
  have hbdiv : Tendsto (fun n => b n / ENNReal.ofReal d) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hb (Or.inr hdne)
  obtain ⟨n, hn⟩ := (hbdiv.eventually (eventually_lt_nhds hκ)).exists
  have hmarkov (ε : ℝ) (hε : 0 < ε) :
      μ {x | d ≤ dist (F ε x) (G n ε x)} ≤ κ := by
    have hm := meas_ge_le_lintegral_div (μ := μ)
      (((hF ε).dist (hG n ε)).ennreal_ofReal.aemeasurable) hdne ENNReal.ofReal_ne_top
    exact (measure_mono fun _ hx => ENNReal.ofReal_le_ofReal hx).trans
      (hm.trans ((ENNReal.div_le_div_right (herr n ε hε) _).trans hn.le))
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ μ {x | d ≤ dist (G n ε x) (L n x)} ≤ κ := by
    filter_upwards [self_mem_nhdsWithin,
      ((tendstoInMeasure_iff_dist.mp (hconv n)) d hd).eventually
        (eventually_lt_nhds hκ)] with ε hε hbound
    exact ⟨hε, hbound.le⟩
  refine ⟨{ε | 0 < ε ∧ μ {x | d ≤ dist (G n ε x) (L n x)} ≤ κ}, hevent, ?_⟩
  intro ε hε ε' hε'
  calc
    μ {x | δ ≤ dist (F ε x) (F ε' x)} ≤
        μ {x | d ≤ dist (F ε x) (G n ε x)} +
          μ {x | d ≤ dist (G n ε x) (L n x)} +
            (μ {x | d ≤ dist (G n ε' x) (L n x)} +
              μ {x | d ≤ dist (F ε' x) (G n ε' x)}) := by
      apply le_trans (measure_mono ?_)
        ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) (measure_union_le _ _)))
      intro x hx
      change δ ≤ dist (F ε x) (F ε' x) at hx
      simp only [mem_union, mem_ofPred_eq]
      by_contra! h
      have ht := (dist_triangle (F ε x) (L n x) (F ε' x)).trans
        (add_le_add (dist_triangle (F ε x) (G n ε x) (L n x))
          (dist_triangle (L n x) (G n ε' x) (F ε' x)))
      rw [dist_comm (L n x) (G n ε' x), dist_comm (G n ε' x) (F ε' x)] at ht
      dsimp [d] at h
      linarith only [hx, ht, h.1.1, h.1.2, h.2.1, h.2.2]
    _ ≤ κ + κ + (κ + κ) :=
      add_le_add (add_le_add (hmarkov ε hε.1) hε.2)
        (add_le_add hε'.2 (hmarkov ε' hε'.1))
    _ = η := hsum

/-- Countably many extractable predicates, inherited by eventual subsequences, have one
common strictly increasing subsequence. -/
theorem exists_diagonal_subseq {ι : Type*} [Countable ι] (Good : ι → (ℕ → ℕ) → Prop)
    (htail : ∀ (i : ι) (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ →
      (∃ N, ∀ k ≥ N, ∃ j, ψ k = φ j) → Good i φ → Good i ψ)
    (hext : ∀ (i : ι) (φ : ℕ → ℕ),
      StrictMono φ → ∃ ψ, StrictMono ψ ∧ Good i (φ ∘ ψ)) :
    ∃ φ, StrictMono φ ∧ ∀ i, Good i φ := by
  classical
  by_cases hι : Nonempty ι
  · let _ : Nonempty ι := hι
    obtain ⟨e, he⟩ := exists_surjective_nat ι
    let S := {φ : ℕ → ℕ // StrictMono φ}
    let ψ (n : ℕ) (φ : S) : ℕ → ℕ := Classical.choose (hext (e n) φ.1 φ.2)
    have hψ (n : ℕ) (φ : S) : StrictMono (ψ n φ) ∧ Good (e n) (φ.1 ∘ ψ n φ) :=
      Classical.choose_spec (hext (e n) φ.1 φ.2)
    let stage : ℕ → S := Nat.rec ⟨id, strictMono_id⟩
      (fun n φ => ⟨φ.1 ∘ ψ n φ, φ.2.comp (hψ n φ).1⟩)
    have hstep (n k : ℕ) : (stage (n + 1)).1 k =
        (stage n).1 (ψ n (stage n) k) := rfl
    have hnest (m n : ℕ) (hmn : m ≤ n) :
        ∀ k, ∃ j, (stage n).1 k = (stage m).1 j := by
      induction n, hmn using Nat.le_induction with
      | base => exact fun k => ⟨k, rfl⟩
      | succ n _ ih =>
        intro k
        rw [hstep]
        exact ih _
    let φ : ℕ → ℕ := fun n => (stage n).1 n
    have hφ : StrictMono φ := by
      apply strictMono_nat_of_lt_succ
      intro n
      change (stage n).1 n < (stage (n + 1)).1 (n + 1)
      rw [hstep]
      exact (stage n).2 ((Nat.lt_succ_self n).trans_le ((hψ n (stage n)).1.id_le _))
    refine ⟨φ, hφ, fun i => ?_⟩
    obtain ⟨n, rfl⟩ := he i
    apply htail (e n) (stage (n + 1)).1 φ (stage (n + 1)).2 hφ
      ⟨n + 1, fun k hk => hnest (n + 1) k hk k⟩
    exact (hψ n (stage n)).2
  · exact ⟨id, strictMono_id, fun i => False.elim (hι ⟨i⟩)⟩

/-- Continuous real tests preserve convergence in measure along a countably generated filter. -/
theorem tendstoInMeasure_continuous_comp_filter {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ i, Measurable (f i))
    (hg : TendstoInMeasure μ f l g) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    TendstoInMeasure μ (fun i ω => φ (f i ω)) l (fun ω => φ (g ω)) := by
  have key (f' : ℕ → Ω → ℝ) (hf' : ∀ n, Measurable (f' n))
      (hg' : TendstoInMeasure μ f' atTop g) :
      TendstoInMeasure μ (fun n ω => φ (f' n ω)) atTop (fun ω => φ (g ω)) := by
    apply (exists_seq_tendstoInMeasure_atTop_iff
      (fun n => (hφ.measurable.comp (hf' n)).aestronglyMeasurable)).mpr
    intro ns hns
    obtain ⟨ms, hms, hlim⟩ := (hg'.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    exact ⟨ms, hms, hlim.mono fun _ h => hφ.continuousAt.tendsto.comp h⟩
  intro ε hε
  apply tendsto_of_seq_tendsto
  intro ns hns
  exact key (fun n => f (ns n)) (fun n => hf _) (hg.comp hns) ε hε

end BGW.Probability
