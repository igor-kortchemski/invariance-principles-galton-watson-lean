/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.BridgeProjectiveMarginal
public import BGW.StableTrees.BridgeProjectiveClose
import BGW.Skorokhod.MeasurableExtrema

/-!
# Terminal pinning of the projective bridge

Centered prefix reversal bounds late excursions by an initial excursion and an endpoint tail.
The one-dimensional endpoint density identifies that tail with a small-time tail. Continuity
from above then gives the full path limit at one.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open BGW.Skorokhod
open scoped ENNReal

namespace BGW.StableTrees

private def earlyBad (a δ ε : ℝ) : Set (D a ℝ) :=
  {g | ∃ t : Icc (0 : ℝ) a, (t : ℝ) ≤ δ ∧ ε < |g t|}

private def lateBad (a b ε : ℝ) : Set (D a ℝ) :=
  {g | ∃ t : Icc (0 : ℝ) a, b < (t : ℝ) ∧ ε < |g t|}

private theorem measurableSet_visit {a : ℝ} (J : Set (Icc (0 : ℝ) a))
    (hJ : J.OrdConnected) (ε : ℝ) :
    MeasurableSet {g : D a ℝ | ∃ t : J, ε < |g t|} := by
  obtain ⟨K, hKc, hK⟩ := exists_countable_detecting_times hJ
  let : Countable K := hKc
  have heq : {g : D a ℝ | ∃ t : J, ε < |g t|} =
      ⋃ t : K, {g : D a ℝ | ε < |g t.val.val|} := by
    ext g
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨q, hq, hval⟩ := hK ℝ g {x | ε < |x|}
        (isOpen_lt continuous_const continuous_abs) t ht
      exact ⟨⟨q, hq⟩, hval⟩
    · rintro ⟨t, ht⟩
      exact ⟨t.val, ht⟩
  rw [heq]
  exact MeasurableSet.iUnion fun t => measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (BGW.Skorokhod.measurable_eval _))

private theorem measurableSet_earlyBad (a δ ε : ℝ) : MeasurableSet (earlyBad a δ ε) := by
  let J : Set (Icc (0 : ℝ) a) := {t | (t : ℝ) ≤ δ}
  have hJ : J.OrdConnected := by
    constructor
    intro x _ y hy u hu
    change (y : ℝ) ≤ δ at hy
    exact (show (u : ℝ) ≤ (y : ℝ) from hu.2).trans hy
  have heq : earlyBad a δ ε = {g : D a ℝ | ∃ t : J, ε < |g t|} := by
    ext g
    constructor
    · rintro ⟨t, ht, hv⟩
      exact ⟨⟨t, ht⟩, hv⟩
    · rintro ⟨t, ht⟩
      exact ⟨t.val, t.property, ht⟩
  rw [heq]
  exact measurableSet_visit J hJ ε

private theorem measurableSet_lateBad (a b ε : ℝ) : MeasurableSet (lateBad a b ε) := by
  let J : Set (Icc (0 : ℝ) a) := {t | b < (t : ℝ)}
  have hJ : J.OrdConnected := by
    constructor
    intro x hx y _ u hu
    change b < (x : ℝ) at hx
    exact hx.trans_le hu.1
  have heq : lateBad a b ε = {g : D a ℝ | ∃ t : J, ε < |g t|} := by
    ext g
    constructor
    · rintro ⟨t, ht, hv⟩
      exact ⟨⟨t, ht⟩, hv⟩
    · rintro ⟨t, ht⟩
      exact ⟨t.val, t.property, ht⟩
  rw [heq]
  exact measurableSet_visit J hJ ε

private theorem earlyBad_restrict {a b δ ε : ℝ} (hab : b ≤ a) (hδ : δ ≤ b) :
    earlyBad a δ ε = (restrict hab) ⁻¹' earlyBad b δ ε := by
  ext g
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨⟨t, t.property.1, ht.trans hδ⟩, ht, hv⟩
  · rintro ⟨t, ht, hv⟩
    exact ⟨⟨t, t.property.1, t.property.2.trans hab⟩, ht, hv⟩

private theorem lateBad_reversal_bound {θ a b ε : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1)
    {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ)) (lateBad a b (2 * ε)) ≤
      bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))
        {g | ε < |g ⟨a, ha.le, le_rfl⟩|} +
      bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ)) (earlyBad a (1 - b) ε) := by
  let μ := bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))
  let J : Set (Icc (0 : ℝ) a) := {t | b < (t : ℝ)}
  have hJ : J.OrdConnected := by
    constructor
    intro x hx y _ u hu
    change b < (x : ℝ) at hx
    exact hx.trans_le hu.1
  obtain ⟨K, hKc, hK⟩ := exists_countable_detecting_times hJ
  let : Countable K := hKc
  have hcont : ∀ᵐ g : D a ℝ ∂μ, ∀ t : K, Function.leftLim g t.val.val = g t.val.val := by
    apply ae_all_iff.mpr
    intro t
    filter_upwards [(bridgePrefixLaw_absolutelyContinuous θ a ha.le P).ae_le
      (hP.ae_continuousAt hθ ha t.val.val)] with g hg
    exact hg.continuousWithinAt.leftLim_eq
  have hsub : lateBad a b (2 * ε) ≤ᵐ[μ]
      {g | ε < |g ⟨a, ha.le, le_rfl⟩|} ∪
        reverseIncrements ha.le ⁻¹' earlyBad a (1 - b) ε := by
    filter_upwards [hcont] with g hg
    rintro ⟨t, ht, hv⟩
    by_cases hend : ε < |g ⟨a, ha.le, le_rfl⟩|
    · exact Or.inl hend
    right
    obtain ⟨q, hq, hqv⟩ := hK ℝ g {x | 2 * ε < |x|}
      (isOpen_lt continuous_const continuous_abs) ⟨t, ht⟩ hv
    let s : Icc (0 : ℝ) a := q.val
    have hs : b < (s : ℝ) := q.property
    let u : Icc (0 : ℝ) a :=
      ⟨a - (s : ℝ), sub_nonneg.mpr s.property.2, sub_le_self _ s.property.1⟩
    have hu : (u : ℝ) ≤ 1 - b := by
      dsimp [u]
      linarith
    refine ⟨u, hu, ?_⟩
    have heq : reverseIncrements ha.le g u = g ⟨a, ha.le, le_rfl⟩ - g s := by
      rw [reverseIncrements_apply]
      have hpoint : (⟨a - (u : ℝ), by linarith [u.property.2],
          sub_le_self _ u.property.1⟩ : Icc (0 : ℝ) a) = s := by
        apply Subtype.ext
        dsimp [u]
        ring
      rw [hpoint, hg ⟨q, hq⟩]
    rw [heq]
    have htri := abs_add_le (g ⟨a, ha.le, le_rfl⟩)
      (g s - g ⟨a, ha.le, le_rfl⟩)
    have hv' : 2 * ε < |g s| := hqv
    have hend' := le_of_not_gt hend
    rw [abs_sub_comm] at htri
    have he : g ⟨a, ha.le, le_rfl⟩ +
        (g s - g ⟨a, ha.le, le_rfl⟩) = g s := by ring
    rw [he] at htri
    linarith
  calc
    μ (lateBad a b (2 * ε)) ≤ μ ({g | ε < |g ⟨a, ha.le, le_rfl⟩|} ∪
        reverseIncrements ha.le ⁻¹' earlyBad a (1 - b) ε) := measure_mono_ae hsub
    _ ≤ μ {g | ε < |g ⟨a, ha.le, le_rfl⟩|} +
        μ (reverseIncrements ha.le ⁻¹' earlyBad a (1 - b) ε) := measure_union_le _ _
    _ = _ := by
      rw [← Measure.map_apply (measurable_reverseIncrements ha.le)
        (measurableSet_earlyBad _ _ _), map_reverseIncrements_bridgePrefixLaw hθ ha hP]

private def initialBad (n : ℕ) (ε : ℝ) : Set BridgeOpen :=
  CompatiblePaths.coord 0 ⁻¹' earlyBad (bridgeHorizon 0) (1 - bridgeHorizon n) ε

private def terminalBad (n : ℕ) (ε : ℝ) : Set BridgeOpen :=
  ⋃ m : ℕ, CompatiblePaths.coord m ⁻¹' lateBad (bridgeHorizon m) (bridgeHorizon n) ε

private theorem measurableSet_initialBad (n : ℕ) (ε : ℝ) :
    MeasurableSet (initialBad n ε) :=
  (measurableSet_earlyBad _ _ _).preimage
    (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon 0)

private theorem measurableSet_terminalBad (n : ℕ) (ε : ℝ) :
    MeasurableSet (terminalBad n ε) :=
  MeasurableSet.iUnion fun m => (measurableSet_lateBad _ _ _).preimage
    (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon m)

private theorem initialBad_antitone (ε : ℝ) : Antitone (fun n => initialBad n ε) := by
  intro n m hnm f hf
  obtain ⟨t, ht, hv⟩ := hf
  exact ⟨t, ht.trans (sub_le_sub_left (strictMono_bridgeHorizon.monotone hnm) 1), hv⟩

private theorem initialBad_eventually_not (f : BridgeOpen)
    (hf : f.1 0 ⟨0, le_rfl, (bridgeHorizon_pos 0).le⟩ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, f ∉ initialBad n ε := by
  let z : Icc (0 : ℝ) (bridgeHorizon 0) := ⟨0, le_rfl, (bridgeHorizon_pos 0).le⟩
  have hset : insert z (Ioi z) = univ := by
    ext t
    simp only [mem_insert_iff, mem_Ioi, mem_univ, iff_true]
    have hz : z ≤ t := t.property.1
    rcases eq_or_lt_of_le hz with ht | ht
    · exact Or.inl ht.symm
    · exact Or.inr ht
  have hc : ContinuousAt (f.1 0) z := by
    have hi := ((isCadlag (f.1 0)).isRightContinuous z).insert
    simpa only [hset, continuousWithinAt_univ] using hi
  obtain ⟨η, hη, hbound⟩ := (Metric.continuousAt_iff.mp hc) ε hε
  obtain ⟨n, hn⟩ := exists_bridgeHorizon_ge (show 1 - η / 2 < 1 by linarith)
  refine ⟨n, ?_⟩
  rintro ⟨t, ht, hv⟩
  have hdist : dist t z < η := by
    have heq : dist t z = (t : ℝ) := by
      simp only [Subtype.dist_eq, Real.dist_eq, z, sub_zero, abs_of_nonneg t.property.1]
    rw [heq]
    linarith
  have hval := hbound hdist
  have hz : f.1 0 z = 0 := hf
  rw [hz, Real.dist_eq, sub_zero] at hval
  exact not_lt_of_ge hval.le hv

private theorem initialBad_tendsto_zero (Q : ProbabilityMeasure BridgeOpen)
    (hstart : ∀ᵐ f : BridgeOpen ∂(Q : Measure BridgeOpen),
      f.1 0 ⟨0, le_rfl, (bridgeHorizon_pos 0).le⟩ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Q : Measure BridgeOpen) (initialBad n ε)) atTop (𝓝 0) := by
  have hinter : (Q : Measure BridgeOpen) (⋂ n, initialBad n ε) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hstart] with f hf
    obtain ⟨n, hn⟩ := initialBad_eventually_not f hf hε
    intro hall
    exact hn (mem_iInter.mp hall n)
  simpa only [Function.comp_def, hinter] using
    tendsto_measure_iInter_atTop (μ := (Q : Measure BridgeOpen))
      (fun n => (measurableSet_initialBad n ε).nullMeasurableSet)
      (initialBad_antitone ε) ⟨0, measure_ne_top _ _⟩

private theorem one_sub_bridgeHorizon_le (n : ℕ) :
    1 - bridgeHorizon n ≤ bridgeHorizon 0 := by
  have hn := strictMono_bridgeHorizon.monotone (Nat.zero_le n)
  have hz : bridgeHorizon 0 = 1 / 2 := by norm_num [bridgeHorizon]
  linarith

section Abstract

variable {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
  (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ))
  (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a))
  (Q : ProbabilityMeasure BridgeOpen)
  (hQ : ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
    bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
      (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)))

include hθ hP hQ

private theorem open_eval_tail {a ε : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (Q : Measure BridgeOpen) {f | ε < |f.eval a|} =
      bridgePrefixLaw θ a ha.le (P a : Measure (D a ℝ))
        {g | ε < |g ⟨a, ha.le, le_rfl⟩|} := by
  let A : Set (D a ℝ) := {g | ε < |g ⟨a, ha.le, le_rfl⟩|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (BGW.Skorokhod.measurable_eval _))
  have heq : {f : BridgeOpen | ε < |f.eval a|} = BridgeOpen.prefix a ha1 ⁻¹' A := by
    ext f
    change (ε < |f.eval a|) ↔ ε < |f.prefix a ha1 ⟨a, ha.le, le_rfl⟩|
    rw [BridgeOpen.prefix_eval]
  rw [heq, ← Measure.map_apply (BridgeOpen.measurable_prefix a ha1) hA,
    map_prefix_bridgeOpen hθ P hP Q hQ ha ha1]

private theorem prefix_earlyBad (n m : ℕ) (ε : ℝ) :
    bridgePrefixLaw θ (bridgeHorizon m) (bridgeHorizon_pos m).le
        (P (bridgeHorizon m) : Measure (D (bridgeHorizon m) ℝ))
        (earlyBad (bridgeHorizon m) (1 - bridgeHorizon n) ε) =
      (Q : Measure BridgeOpen) (initialBad n ε) := by
  have hrestrict := earlyBad_restrict
    (strictMono_bridgeHorizon.monotone (Nat.zero_le m)) (one_sub_bridgeHorizon_le n)
    (ε := ε)
  rw [hrestrict, ← Measure.map_apply (measurable_restrict _)
    (measurableSet_earlyBad _ _ _)]
  rw [bridgePrefix_consistent hθ (bridgeHorizon_pos 0)
    (strictMono_bridgeHorizon.monotone (Nat.zero_le m)) (bridgeHorizon_lt_one m)
    (hP _ (bridgeHorizon_pos 0) (bridgeHorizon_lt_one 0))
    (hP _ (bridgeHorizon_pos m) (bridgeHorizon_lt_one m))]
  change _ = (Q : Measure BridgeOpen)
    (CompatiblePaths.coord 0 ⁻¹' earlyBad (bridgeHorizon 0) (1 - bridgeHorizon n) ε)
  rw [← Measure.map_apply
    (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon 0)
    (measurableSet_earlyBad _ _ _), hQ 0]

private theorem prefix_endpoint_tail_le (m : ℕ) (ε : ℝ) :
    bridgePrefixLaw θ (bridgeHorizon m) (bridgeHorizon_pos m).le
        (P (bridgeHorizon m) : Measure (D (bridgeHorizon m) ℝ))
        {g | ε < |g ⟨bridgeHorizon m, (bridgeHorizon_pos m).le, le_rfl⟩|} ≤
      (Q : Measure BridgeOpen) (initialBad m ε) := by
  have hb : 0 < 1 - bridgeHorizon m := sub_pos.mpr (bridgeHorizon_lt_one m)
  have hb1 : 1 - bridgeHorizon m < 1 := by linarith [bridgeHorizon_pos m]
  rw [bridgePrefix_endpoint_abs_tail_symm hθ (bridgeHorizon_pos m) (bridgeHorizon_lt_one m)
    (hP _ (bridgeHorizon_pos m) (bridgeHorizon_lt_one m)) (hP _ hb hb1),
    ← open_eval_tail hθ P hP Q hQ hb hb1]
  apply measure_mono
  intro f hf
  refine ⟨⟨1 - bridgeHorizon m, hb.le, one_sub_bridgeHorizon_le m⟩, le_rfl, ?_⟩
  have heq := BridgeOpen.eval_eq_coord f 0
    ⟨1 - bridgeHorizon m, hb.le, one_sub_bridgeHorizon_le m⟩
  change ε < |f.1 0 _|
  change ε < |f.eval (1 - bridgeHorizon m)| at hf
  change f.eval (1 - bridgeHorizon m) = _ at heq
  rwa [heq] at hf

private theorem finite_terminalBad_le (n m : ℕ) (ε : ℝ) :
    (Q : Measure BridgeOpen)
        (CompatiblePaths.coord m ⁻¹' lateBad (bridgeHorizon m) (bridgeHorizon n) (2 * ε)) ≤
      (Q : Measure BridgeOpen) (initialBad n ε) +
        (Q : Measure BridgeOpen) (initialBad n ε) := by
  by_cases hnm : n ≤ m
  · rw [← Measure.map_apply
      (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon m)
      (measurableSet_lateBad _ _ _), hQ m]
    calc
      _ ≤ _ := lateBad_reversal_bound hθ (bridgeHorizon_pos m) (bridgeHorizon_lt_one m)
        (hP _ (bridgeHorizon_pos m) (bridgeHorizon_lt_one m))
      _ ≤ (Q : Measure BridgeOpen) (initialBad m ε) +
          (Q : Measure BridgeOpen) (initialBad n ε) :=
        add_le_add (prefix_endpoint_tail_le hθ P hP Q hQ m ε)
          (prefix_earlyBad hθ P hP Q hQ n m ε).le
      _ ≤ _ := add_le_add (measure_mono (initialBad_antitone ε hnm)) le_rfl
  · have hempty : CompatiblePaths.coord (hb := strictMono_bridgeHorizon) m ⁻¹'
        lateBad (bridgeHorizon m) (bridgeHorizon n) (2 * ε) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro f ⟨t, ht, _⟩
      have hmn := strictMono_bridgeHorizon.monotone (le_of_not_ge hnm)
      exact not_lt_of_ge (t.property.2.trans hmn) ht
    rw [hempty, measure_empty]
    exact bot_le

private theorem terminalBad_le (n : ℕ) (ε : ℝ) :
    (Q : Measure BridgeOpen) (terminalBad n (2 * ε)) ≤
      (Q : Measure BridgeOpen) (initialBad n ε) +
        (Q : Measure BridgeOpen) (initialBad n ε) := by
  have hmono : Monotone (fun m => CompatiblePaths.coord (hb := strictMono_bridgeHorizon) m ⁻¹'
      lateBad (bridgeHorizon m) (bridgeHorizon n) (2 * ε)) := by
    intro i j hij f hf
    obtain ⟨t, ht, hv⟩ := hf
    refine ⟨⟨t, t.property.1,
      t.property.2.trans (strictMono_bridgeHorizon.monotone hij)⟩, ht, ?_⟩
    have heq := congrArg (fun g : D (bridgeHorizon i) ℝ => g t)
      (BridgeOpen.coord_restrict f hij)
    change (f.1 j) ⟨t, t.property.1,
      t.property.2.trans (strictMono_bridgeHorizon.monotone hij)⟩ = (f.1 i) t at heq
    exact lt_of_lt_of_eq hv (congrArg abs heq).symm
  change (Q : Measure BridgeOpen) (⋃ m, CompatiblePaths.coord m ⁻¹'
    lateBad (bridgeHorizon m) (bridgeHorizon n) (2 * ε)) ≤ _
  rw [hmono.measure_iUnion]
  exact iSup_le fun m => finite_terminalBad_le hθ P hP Q hQ n m ε

end Abstract

/-- **Terminal pinning, abstract form.** Any law on the open carrier with the tilted prefix
marginals has full path limit `0` at the terminal time, almost surely. -/
theorem bridgeOpen_ae_terminal_limit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ))
    (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a))
    (Q : ProbabilityMeasure BridgeOpen)
    (hQ : ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ))) :
    ∀ᵐ f ∂(Q : Measure BridgeOpen), Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  classical
  have hstart : ∀ᵐ f : BridgeOpen ∂(Q : Measure BridgeOpen),
      f.1 0 ⟨0, le_rfl, (bridgeHorizon_pos 0).le⟩ = 0 := by
    have hz := bridgePrefixLaw_ae_zero (bridgeHorizon_pos 0).le
      (hP _ (bridgeHorizon_pos 0) (bridgeHorizon_lt_one 0))
    rw [← hQ 0] at hz
    have hs : MeasurableSet {g : D (bridgeHorizon 0) ℝ |
        g ⟨0, le_rfl, (bridgeHorizon_pos 0).le⟩ = 0} :=
      (BGW.Skorokhod.measurable_eval _) (measurableSet_singleton 0)
    exact (ae_map_iff
      (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon 0).aemeasurable
      hs).mp hz
  have hbad (ε : ℝ) (hε : 0 < ε) :
      (Q : Measure BridgeOpen) (⋂ n, terminalBad n (2 * ε)) = 0 := by
    have hlim := initialBad_tendsto_zero Q hstart hε
    have hlim2 : Tendsto (fun n => (Q : Measure BridgeOpen) (initialBad n ε) +
        (Q : Measure BridgeOpen) (initialBad n ε)) atTop (𝓝 0) := by
      simpa only [add_zero] using hlim.add hlim
    have hle (n : ℕ) : (Q : Measure BridgeOpen) (⋂ n, terminalBad n (2 * ε)) ≤
        (Q : Measure BridgeOpen) (initialBad n ε) +
          (Q : Measure BridgeOpen) (initialBad n ε) :=
      (measure_mono (iInter_subset _ n)).trans (terminalBad_le hθ P hP Q hQ n ε)
    have hzero := le_of_tendsto_of_tendsto tendsto_const_nhds hlim2
      (Filter.Eventually.of_forall hle)
    exact le_antisymm hzero bot_le
  have hgood (k : ℕ) : ∀ᵐ f : BridgeOpen ∂(Q : Measure BridgeOpen),
      ∃ n, f ∉ terminalBad n (1 / (k + 1 : ℝ)) := by
    have hz := hbad ((1 / (k + 1 : ℝ)) / 2) (by positivity)
    have heq : 2 * ((1 / (k + 1 : ℝ)) / 2) = 1 / (k + 1 : ℝ) := by ring
    rw [heq] at hz
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with f hf
    simpa only [mem_iInter, not_forall] using hf
  filter_upwards [ae_all_iff.mpr hgood] with f hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn⟩ := hf k
  filter_upwards [Ioo_mem_nhdsLT (bridgeHorizon_lt_one n)] with t ht
  obtain ⟨m, hm⟩ := exists_bridgeHorizon_ge ht.2
  have ht0 : 0 ≤ t := (bridgeHorizon_pos n).le.trans ht.1.le
  have hval : |f.eval t| ≤ 1 / (k + 1 : ℝ) := by
    by_contra! hgt
    apply hn
    apply mem_iUnion.mpr
    refine ⟨m, ⟨⟨t, ht0, hm⟩, ht.1, ?_⟩⟩
    have heval := BridgeOpen.eval_eq_coord f m ⟨t, ht0, hm⟩
    change f.eval t = _ at heval
    rwa [heval] at hgt
  simpa only [Real.dist_eq, sub_zero] using hval.trans_lt hk

/-- **Terminal pinning for the stable bridge**: the open stable bridge converges to `0` at time
`1` almost surely. -/
theorem bridgeOpenLaw_ae_terminal_limit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(bridgeOpenLaw θ : Measure BridgeOpen), Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  exact bridgeOpen_ae_terminal_limit hθ (fun a => stableProcessLaw θ a)
    (fun _ ha _ => isStableLevyLaw_stableProcessLaw hθ ha)
    (bridgeOpenLaw θ) (map_coord_bridgeOpenLaw hθ)

end BGW.StableTrees
