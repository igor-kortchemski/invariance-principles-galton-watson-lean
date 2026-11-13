/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsSupport
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Summing excursion lifetimes

Disjoint passage intervals have total length at most the passage time. The null zero set
removes the possible drift term and also proves summability in the nonnegative reals.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem ae_lifetime_sum_volume {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ K : ℝ≥0,
      (∑' x : {x ∈ passageJumpSet f | x ≤ K}, ((jumpExcursion x f).lifetime : ℝ≥0∞)) =
        (passageTime K f : ℝ≥0∞) := by
  filter_upwards [ae_passageJumpSet_countable hθ, ae_jump_intervals_disjoint hθ,
    ae_jumpExcursion_spec hθ, ae_isCadlag_monotone_passage hθ,
    ae_pos_set_eq_iUnion_jump_intervals hθ, ae_zeroSet_volume_zero hθ,
    ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ]
    with f hc hd hs hT hp hz hfinite hcreep
  classical
  intro K
  let A : Set ℝ≥0 := {x ∈ passageJumpSet f | x ≤ K}
  let := (hc.mono (fun _ hx => hx.1) : A.Countable).to_subtype
  let U : A → Set ℝ := fun x => Ioo (passageTimeMinus x f : ℝ) (passageTime x f : ℝ)
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro x y hne
    have hxy : (x : ℝ≥0) ≠ y := fun h => hne (Subtype.ext h)
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · apply Set.disjoint_left.mpr
      intro t ht ht'
      have hsep : (passageTime x f : ℝ) < passageTimeMinus y f := by
        exact_mod_cast hd x x.2.1 y y.2.1 hlt
      exact (ht.2.trans hsep).not_gt ht'.1
    · apply Set.disjoint_left.mpr
      intro t ht ht'
      have hsep : (passageTime y f : ℝ) < passageTimeMinus x f := by
        exact_mod_cast hd y y.2.1 x x.2.1 hgt
      exact (ht'.2.trans hsep).not_gt ht.1
  have hsub : (⋃ x, U x) ⊆ Ioo (0 : ℝ) (passageTime K f : ℝ) := by
    intro t ht
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp ht
    exact ⟨(passageTimeMinus x f).coe_nonneg.trans_lt hx.1,
      hx.2.trans_le (by exact_mod_cast hT.2.1 x.2.2)⟩
  have hnull : volume (Ioo (0 : ℝ) (passageTime K f : ℝ) \ (⋃ x, U x)) = 0 := by
    apply measure_mono_null _ hz
    intro t ht
    let u : ℝ≥0 := ⟨t, ht.1.1.le⟩
    refine ⟨u, ?_, rfl⟩
    change (reflectedFrom 0 f).1 u = 0
    apply le_antisymm _ (reflectedFrom_nonneg 0 f u)
    apply le_of_not_gt
    intro hpos
    have hmem : u ∈ ⋃ x ∈ passageJumpSet f,
        Ioo (passageTimeMinus x f) (passageTime x f) := hp ▸ hpos
    obtain ⟨x, hx, hux⟩ := Set.mem_iUnion₂.mp hmem
    have hxK : x ≤ K := by
      by_contra hn
      have hKx : K < x := lt_of_not_ge hn
      have hsep : passageTime K f < passageTimeMinus x f :=
        passageTime_lt_passageTimeMinus
          hfinite.1 (strictMono_passageTime_of_creeping hfinite.1 hcreep) hKx
      have hut : (u : ℝ) < passageTime K f := ht.1.2
      have hsep' : (passageTime K f : ℝ) < passageTimeMinus x f := by exact_mod_cast hsep
      have hux' : (passageTimeMinus x f : ℝ) < u := by exact_mod_cast hux.1
      linarith
    exact ht.2 (Set.mem_iUnion.mpr ⟨⟨x, hx, hxK⟩, hux⟩)
  have hvol : volume (⋃ x, U x) = (passageTime K f : ℝ≥0∞) := by
    calc
      _ = volume (Ioo (0 : ℝ) (passageTime K f : ℝ)) := by
        apply measure_congr
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht
        exact propext ⟨fun hu => hsub hu, fun hi => by
          by_contra hu
          exact ht ⟨hi, hu⟩⟩
      _ = _ := by simp only [Real.volume_Ioo, sub_zero, ENNReal.ofReal_coe_nnreal]
  rw [measure_iUnion hdisj (fun _ => measurableSet_Ioo)] at hvol
  convert hvol using 1
  apply tsum_congr
  intro x
  rw [(hs x x.2.1).2.1, Real.volume_Ioo]
  rw [← NNReal.coe_sub x.2.1.2.le, ENNReal.ofReal_coe_nnreal]

/-- **Pure-jump passage time**: a.s., simultaneously for all `K`, `T_K` is the sum of the
lifetimes of the excursions at jump levels `x ≤ K` (no drift). -/
theorem ae_passageTime_eq_tsum_lifetime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ K : ℝ≥0,
      passageTime K f =
        ∑' x : {x ∈ passageJumpSet f | x ≤ K}, (jumpExcursion x f).lifetime  := by
  filter_upwards [ae_lifetime_sum_volume hθ] with f hf
  intro K
  have hsumm : Summable (fun x : {x ∈ passageJumpSet f | x ≤ K} =>
      (jumpExcursion x f).lifetime) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (by rw [hf K]; exact ENNReal.coe_ne_top)
  apply ENNReal.coe_injective
  rw [ENNReal.coe_tsum hsumm, hf K]

/-- **Finite counts of long excursions** and the passage-time bound `ε * count ≤ T_K`:
for all `K, ε > 0` simultaneously. -/
theorem ae_finite_excursionCount {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ K ε : ℝ≥0, 0 < K → 0 < ε →
      (ε : ℝ≥0∞) * excursionPointMeasure f (Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}) ≤
          (passageTime K f : ℝ≥0∞) ∧
        excursionPointMeasure f (Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}) < ⊤  := by
  filter_upwards [ae_lifetime_sum_volume hθ, ae_passageJumpSet_countable hθ] with f hsum hc
  classical
  intro K ε _hK hε
  let S : Set ℝ≥0 := {x ∈ passageJumpSet f |
    (x, jumpExcursion x f) ∈ Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}}
  have hm : MeasurableSet (Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}) :=
    measurableSet_Ioc.prod (measurableSet_lt (α := ℝ≥0)
      measurable_const measurable_excursion_lifetime)
  have hbound : (ε : ℝ≥0∞) * excursionPointMeasure f
      (Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}) ≤ (passageTime K f : ℝ≥0∞) := by
    rw [excursionPointMeasure_apply hc hm, mul_comm,
      ← ENNReal.tsum_set_const S (ε : ℝ≥0∞), ← hsum K]
    rw [tsum_subtype S (fun _ => (ε : ℝ≥0∞)),
      tsum_subtype {x ∈ passageJumpSet f | x ≤ K}
        (fun x => ((jumpExcursion x f).lifetime : ℝ≥0∞))]
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hx : x ∈ S
    · have hmem : x ∈ passageJumpSet f ∧
          (0 < x ∧ x ≤ K) ∧ ε < (jumpExcursion x f).lifetime := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem
        (show x ∈ {x ∈ passageJumpSet f | x ≤ K} from
          ⟨hmem.1, hmem.2.1.2⟩)]
      exact_mod_cast hmem.2.2.le
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  refine ⟨hbound, lt_top_iff_ne_top.mpr ?_⟩
  intro hinf
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  rw [hinf, ENNReal.mul_top hε0] at hbound
  exact (not_le_of_gt ENNReal.coe_lt_top) hbound

end BGW.StableTrees
