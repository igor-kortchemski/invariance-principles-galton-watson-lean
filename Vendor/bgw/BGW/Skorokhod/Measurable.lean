/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import BGW.Skorokhod.StepApprox
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Borel structure on the Skorokhod space

The measurable structure on `D` is the Borel structure of the J1 metric.
-/

@[expose] public section

namespace BGW.Skorokhod

open Filter Topology

variable {T : ℝ} {E : Type*}

/-- Evaluation at the terminal time is nonexpansive for the J1 metric. -/
theorem dist_eval_top_le [MetricSpace E] (hT : 0 ≤ T) (f g : D T E) :
    dist (f ⟨T, hT, le_rfl⟩) (g ⟨T, hT, le_rfl⟩) ≤ dist f g := by
  rw [dist_eq_j1Dist]
  change dist (f ⟨T, hT, le_rfl⟩) (g ⟨T, hT, le_rfl⟩) ≤
    ⨅ σ : TimeChange T,
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t)))
  apply le_ciInf
  intro σ
  have htop := TimeChange.apply_top σ hT
  have hval := le_ciSup_of_le (bddAbove_range_dist f g σ)
    (⟨T, hT, le_rfl⟩ : Set.Icc (0 : ℝ) T) le_rfl
  calc
    dist (f ⟨T, hT, le_rfl⟩) (g ⟨T, hT, le_rfl⟩) =
        dist (f ⟨T, hT, le_rfl⟩) (g (σ ⟨T, hT, le_rfl⟩)) := by rw [htop]
    _ ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t)) := hval
    _ ≤ max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t))) :=
      le_max_of_le_right le_rfl

/-- The measurable structure on the Skorokhod space is the Borel structure of J1. -/
noncomputable instance instMeasurableSpace [MetricSpace E] : MeasurableSpace (D T E) :=
  borel (D T E)

/-- The measurable structure on the Skorokhod space is its Borel structure. -/
instance instBorelSpace [MetricSpace E] : BorelSpace (D T E) := ⟨rfl⟩

/-- The terminal evaluation map is Lipschitz, hence Borel measurable. -/
theorem measurable_eval_top [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (hT : 0 ≤ T) : Measurable (fun f : D T E => f ⟨T, hT, le_rfl⟩) := by
  have hlip : LipschitzWith 1 (fun f : D T E => f ⟨T, hT, le_rfl⟩) :=
    LipschitzWith.of_dist_le_mul fun f g => by
      simpa using dist_eval_top_le hT f g
  exact hlip.continuous.measurable

/-- Evaluation at the initial time is nonexpansive for the J1 metric. -/
theorem dist_eval_zero_le [MetricSpace E] (hT : 0 ≤ T) (f g : D T E) :
    dist (f ⟨0, by simp [hT]⟩) (g ⟨0, by simp [hT]⟩) ≤ dist f g := by
  rw [dist_eq_j1Dist]
  change dist (f ⟨0, by simp [hT]⟩) (g ⟨0, by simp [hT]⟩) ≤
    ⨅ σ : TimeChange T,
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t)))
  apply le_ciInf
  intro σ
  have hzero := TimeChange.apply_zero σ hT
  have hval := le_ciSup_of_le (bddAbove_range_dist f g σ)
    (⟨0, by simp [hT]⟩ : Set.Icc (0 : ℝ) T) le_rfl
  calc
    dist (f ⟨0, by simp [hT]⟩) (g ⟨0, by simp [hT]⟩) =
        dist (f ⟨0, by simp [hT]⟩) (g (σ ⟨0, by simp [hT]⟩)) := by rw [hzero]
    _ ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t)) := hval
    _ ≤ max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t))) :=
      le_max_of_le_right le_rfl

/-- The initial evaluation map is Lipschitz, hence Borel measurable. -/
theorem measurable_eval_zero [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (hT : 0 ≤ T) : Measurable (fun f : D T E => f ⟨0, by simp [hT]⟩) := by
  have hlip : LipschitzWith 1 (fun f : D T E => f ⟨0, by simp [hT]⟩) :=
    LipschitzWith.of_dist_le_mul fun f g => by simpa using dist_eval_zero_le hT f g
  exact hlip.continuous.measurable

/-- Measurability of all fixed evaluations implies measurability of fixed left limits. -/
theorem measurable_leftLim_eval_of_measurable_eval [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (hEval : ∀ s : Set.Icc (0 : ℝ) T,
      Measurable (fun f : D T E => f s)) (t : Set.Icc (0 : ℝ) T) :
    Measurable (fun f : D T E => Function.leftLim f t) := by
  classical
  by_cases hzero : (t : ℝ) = 0
  · have hbot : IsBot t := by
      change ∀ s, t ≤ s
      intro s
      change (t : ℝ) ≤ (s : ℝ)
      rw [hzero]
      exact s.property.1
    rw [show (fun f : D T E => Function.leftLim f t) =
      (fun f : D T E => f t) by
        funext f
        exact leftLim_eq_of_isBot hbot]
    exact hEval t
  · have htpos : 0 < (t : ℝ) :=
      lt_of_le_of_ne t.property.1 (by simpa [eq_comm] using hzero)
    have hT0 : 0 ≤ T := le_trans t.property.1 t.property.2
    let q : ℕ → Set.Icc (0 : ℝ) T := fun n =>
      ⟨max 0 ((t : ℝ) - (n + 1 : ℝ)⁻¹),
        le_max_left _ _,
        max_le hT0 (le_trans (sub_le_self _ (by positivity)) t.property.2)⟩
    have hq_lt (n : ℕ) : q n < t := by
      apply Subtype.coe_lt_coe.mpr
      change max 0 ((t : ℝ) - (n + 1 : ℝ)⁻¹) < (t : ℝ)
      apply max_lt_iff.mpr
      constructor
      · exact htpos
      · have hpos : 0 < (n + 1 : ℝ)⁻¹ := by positivity
        linarith
    have hnat : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hnat
    have hconst : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (𝓝 (t : ℝ)) :=
      tendsto_const_nhds
    have hraw : Tendsto (fun n : ℕ => (t : ℝ) - (n + 1 : ℝ)⁻¹) atTop
        (𝓝 (t : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one] using hconst.sub hinv
    have hmaxcont : Continuous (fun x : ℝ => max (0 : ℝ) x) :=
      continuous_const.max continuous_id
    have hqval : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝 (t : ℝ)) := by
      have hmax : Tendsto (fun n : ℕ => max (0 : ℝ) ((t : ℝ) - (n + 1 : ℝ)⁻¹))
          atTop (𝓝 (max (0 : ℝ) (t : ℝ))) := (hmaxcont.tendsto _).comp hraw
      simpa [q, max_eq_right t.property.1] using hmax
    have hqSubtype : Tendsto q atTop (𝓝 t) := tendsto_subtype_rng.mpr hqval
    have hqwithin : Tendsto q atTop (𝓝[Set.Iio t] t) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hqSubtype, Filter.Eventually.of_forall hq_lt⟩
    let g : ℕ → D T E → E := fun n f => f (q n)
    have hlim : Tendsto g atTop (𝓝 (fun f : D T E => Function.leftLim f t)) := by
      rw [tendsto_pi_nhds]
      intro f
      exact ((isCadlag f).tendsto_nhdsLT_leftLim t).comp hqwithin
    have hg : ∀ n, Measurable (fun f : D T E => f (q n)) := fun n => hEval (q n)
    exact measurable_of_tendsto_metrizable hg hlim

/-- Evaluation is measurable when the time argument has countable range. -/
theorem measurable_eval_on_countable_range [MetricSpace E] [MeasurableSpace E]
    {R : Type*} [MeasurableSpace R] [Countable R] [MeasurableSingletonClass R]
    (τ : R → Set.Icc (0 : ℝ) T)
    (hEval : ∀ t : Set.Icc (0 : ℝ) T, Measurable (fun f : D T E => f t)) :
    Measurable (fun p : D T E × R => p.1 (τ p.2)) := by
  classical
  intro s hs
  have heq : {p : D T E × R | p.1 (τ p.2) ∈ s} =
      ⋃ r : R, (Prod.snd ⁻¹' ({r} : Set R)) ∩
        {p : D T E × R | p.1 (τ r) ∈ s} := by
    ext ⟨f, r⟩
    simp
  change MeasurableSet {p : D T E × R | p.1 (τ p.2) ∈ s}
  rw [heq]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.inter
  · exact measurable_snd (measurableSet_singleton r)
  · exact (hEval (τ r)).comp measurable_fst hs

/-- Joint evaluation is a pointwise limit of evaluations at dyadic right times. -/
theorem measurable_eval₂_of_measurable_eval [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (hEval : ∀ t : Set.Icc (0 : ℝ) T,
      Measurable (fun f : D T E => f t)) :
    Measurable (fun p : D T E × Set.Icc (0 : ℝ) T => p.1 p.2) := by
  classical
  by_cases hT : 0 ≤ T
  · let q : ℕ → Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) T :=
      fun n => dyadicRightTime hT n
    let g : ℕ → D T E × Set.Icc (0 : ℝ) T → E := fun n p => p.1 (q n p.2)
    have hg : ∀ n, Measurable (g n) := by
      intro n
      let R := Set.range (q n)
      let _ : Countable R := countable_range_dyadicRightTime hT n
      let τ : R → Set.Icc (0 : ℝ) T := fun r => r
      let rmap : Set.Icc (0 : ℝ) T → R := fun t => ⟨q n t, ⟨t, rfl⟩⟩
      have hrmap : Measurable rmap := by
        apply Measurable.subtype_mk
        exact (measurable_dyadicRightTime hT n)
      have hpair : Measurable (fun p : D T E × Set.Icc (0 : ℝ) T =>
          (p.1, rmap p.2)) := measurable_fst.prodMk (hrmap.comp measurable_snd)
      have hEvalR : Measurable (fun p : D T E × R => p.1 (τ p.2)) :=
        measurable_eval_on_countable_range τ hEval
      have hfunc : (fun p : D T E × Set.Icc (0 : ℝ) T => p.1 (q n p.2)) =
          (fun p => p.1 (τ (rmap p.2))) := by
        funext p
        rfl
      change Measurable (fun p : D T E × Set.Icc (0 : ℝ) T => p.1 (q n p.2))
      rw [hfunc]
      exact hEvalR.comp hpair
    have hlim : Tendsto g atTop (𝓝 (fun p : D T E × Set.Icc (0 : ℝ) T => p.1 p.2)) := by
      rw [tendsto_pi_nhds]
      intro p
      by_cases ht : (p.2 : ℝ) = T
      · have hqt : ∀ n, q n p.2 = p.2 := by
          intro n
          apply Subtype.ext
          have hle := (q n p.2).property.2
          have hge := (le_dyadicRightTime hT n p.2)
          exact le_antisymm (by simpa [q, ht] using hle) (by exact_mod_cast hge)
        simp [g, hqt]
      · have htT : (p.2 : ℝ) < T := lt_of_le_of_ne p.2.property.2 ht
        have hwithin : Tendsto (fun n => q n p.2) atTop (𝓝[Set.Ioi p.2] p.2) := by
          apply tendsto_nhdsWithin_iff.mpr
          exact ⟨tendsto_dyadicRightTime hT p.2,
            Filter.Eventually.of_forall fun n => lt_dyadicRightTime hT n htT⟩
        exact ((isCadlag p.1).isRightContinuous p.2).tendsto.comp hwithin
    exact measurable_of_tendsto_metrizable hg hlim
  · let _ : IsEmpty (D T E × Set.Icc (0 : ℝ) T) := ⟨fun p => by
      have ht0 : 0 ≤ (p.2 : ℝ) := p.2.property.1
      have htT : (p.2 : ℝ) ≤ T := p.2.property.2
      linarith [lt_of_not_ge hT]⟩
    exact measurable_of_countable _

/-- Hitting an open spatial set during an open time interval is J1-open. -/
theorem isOpen_setOf_exists_eval_mem [MetricSpace E] {U : Set E} (hU : IsOpen U)
    (a b : ℝ) :
    IsOpen {f : D T E | ∃ s : Set.Icc (0 : ℝ) T, a < s ∧ (s : ℝ) < b ∧ f s ∈ U} := by
  classical
  apply Metric.isOpen_iff.mpr
  rintro f ⟨s, has, hsb, hfs⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (f s) hfs
  let δ := min ε (min ((s : ℝ) - a) (b - s))
  have hδ : 0 < δ := lt_min hε (lt_min (sub_pos.mpr has) (sub_pos.mpr hsb))
  refine ⟨δ, hδ, ?_⟩
  intro g hg
  have hfg : dist f g < δ := by simpa [dist_comm] using hg
  have hex : ∃ σ : TimeChange T,
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t))) < δ := by
    have : Nonempty (TimeChange T) := ⟨OrderIso.refl _⟩
    apply (ciInf_lt_iff ?_).mp hfg
    refine ⟨0, ?_⟩
    rintro _ ⟨σ, rfl⟩
    apply le_max_of_le_right
    exact le_ciSup_of_le (bddAbove_range_dist f g σ) s dist_nonneg
  obtain ⟨σ, hσ⟩ := hex
  have htime : |((σ s : ℝ)) - s| < δ := by
    apply lt_of_le_of_lt ?_ (lt_of_le_of_lt (le_max_left _ _) hσ)
    apply le_ciSup_of_le (c := s) _ le_rfl
    refine ⟨T, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact TimeChange.abs_sub_le σ (s.2.1.trans s.2.2) t
  have hspace : dist (f s) (g (σ s)) < δ :=
    lt_of_le_of_lt (le_ciSup (bddAbove_range_dist f g σ) s)
      (lt_of_le_of_lt (le_max_right _ _) hσ)
  refine ⟨σ s, ?_, ?_, ?_⟩
  · have := (abs_lt.mp htime).1
    have := (min_le_right ε (min ((s : ℝ) - a) (b - s))).trans
      (min_le_left ((s : ℝ) - a) (b - s))
    dsimp [δ] at *
    linarith
  · have := (abs_lt.mp htime).2
    have := (min_le_right ε (min ((s : ℝ) - a) (b - s))).trans
      (min_le_right ((s : ℝ) - a) (b - s))
    dsimp [δ] at *
    linarith
  · apply hball
    change dist (g (σ s)) (f s) < ε
    rw [dist_comm]
    exact hspace.trans_le (min_le_left _ _)

/-- Each evaluation map is Borel for J1 (C4.1). -/
theorem measurable_eval [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (t : Set.Icc (0 : ℝ) T) : Measurable (fun f : D T E => f t) := by
  classical
  by_cases ht : (t : ℝ) = T
  · have heq : t = ⟨T, t.2.1.trans t.2.2, le_rfl⟩ := Subtype.ext ht
    simpa only [heq] using measurable_eval_top (E := E) (t.2.1.trans t.2.2)
  have htT : (t : ℝ) < T := lt_of_le_of_ne t.2.2 ht
  apply measurable_of_isClosed
  intro C hC
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · simp
  let r : ℕ → ℝ := fun n => (n + 1 : ℝ)⁻¹
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hn
  let A : ℕ → Set (D T E) := fun n =>
    {f | ∃ s : Set.Icc (0 : ℝ) T,
      (t : ℝ) < s ∧ (s : ℝ) < (t : ℝ) + r n ∧ Metric.infDist (f s) C < r n}
  have hA (n : ℕ) : IsOpen (A n) :=
    isOpen_setOf_exists_eval_mem
      (isOpen_lt (Metric.continuous_infDist_pt C) continuous_const) _ _
  have heq : (fun f : D T E => f t) ⁻¹' C = ⋂ n, A n := by
    ext f
    simp only [Set.mem_preimage, Set.mem_iInter]
    constructor
    · intro hf n
      obtain ⟨δ, hδ, hclose⟩ := exists_right_oscillation f t (hr n)
      let d := min δ (min (r n) (T - t)) / 2
      have hd : 0 < d := by
        dsimp [d]
        exact half_pos (lt_min hδ (lt_min (hr n) (sub_pos.mpr htT)))
      have hdδ : d < δ := by
        have := min_le_left δ (min (r n) (T - t))
        dsimp [d] at *
        linarith
      have hdr : d < r n := by
        have := (min_le_right δ (min (r n) (T - t))).trans (min_le_left _ _)
        dsimp [d] at *
        linarith
      have hdT : d < T - t := by
        have := (min_le_right δ (min (r n) (T - t))).trans (min_le_right _ _)
        dsimp [d] at *
        linarith
      let s : Set.Icc (0 : ℝ) T := ⟨t + d, by linarith [t.2.1], by linarith⟩
      refine ⟨s, by dsimp [s]; linarith, by dsimp [s]; linarith, ?_⟩
      exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hf)
        (hclose s (by dsimp [s]; linarith) (by dsimp [s]; linarith))
    · intro hf
      choose s hslo hshi hsC using hf
      have hst : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (t : ℝ)) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (by simpa using tendsto_const_nhds.add hr0)
          (fun n => (hslo n).le) (fun n => (hshi n).le)
      have hswithin : Tendsto s atTop (𝓝[Set.Ioi t] t) :=
        tendsto_nhdsWithin_iff.mpr ⟨tendsto_subtype_rng.mpr hst,
          Filter.Eventually.of_forall hslo⟩
      have hfs := ((isCadlag f).isRightContinuous t).tendsto.comp hswithin
      have hinf := (Metric.continuous_infDist_pt C).continuousAt.tendsto.comp hfs
      have hz : Tendsto (fun n => Metric.infDist (f (s n)) C) atTop (𝓝 0) :=
        squeeze_zero (fun _ => Metric.infDist_nonneg) (fun n => (hsC n).le) hr0
      exact (hC.mem_iff_infDist_zero hCne).mpr (tendsto_nhds_unique hinf hz)
  rw [heq]
  exact MeasurableSet.iInter fun n => (hA n).measurableSet

/-- Joint evaluation `(f, t) ↦ f t` is measurable (C4.3). -/
theorem measurable_eval₂ [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (fun p : D T E × Set.Icc (0 : ℝ) T => p.1 p.2) :=
  measurable_eval₂_of_measurable_eval measurable_eval

/-- The left limit at a fixed time is a measurable functional (C4.4). -/
theorem measurable_leftLim_eval [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (t : Set.Icc (0 : ℝ) T) : Measurable (fun f : D T E => Function.leftLim f t) :=
  measurable_leftLim_eval_of_measurable_eval measurable_eval t

end BGW.Skorokhod
