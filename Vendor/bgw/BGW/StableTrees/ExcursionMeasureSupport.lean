/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureSupportTransfer
public import BGW.StableTrees.ExcursionMeasureSupportPath
import Mathlib.Data.NNRat.Encodable

/-! Support of the excursion measure, transferred through measurable compact-window lower bounds.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem windowInf_le_eval {e : Excursion} {a b t : ℝ≥0} (ht : t ∈ Icc a b) :
    excursionWindowInf a b e ≤ e.path.1 t := by
  let W := DLoc.restrict (b - a) (DLoc.shift a e.path)
  let s : Icc (0 : ℝ) ((b - a : ℝ≥0) : ℝ) :=
    ⟨((t - a : ℝ≥0) : ℝ), (t - a).2, by exact_mod_cast tsub_le_tsub_right ht.2 a⟩
  calc
    excursionWindowInf a b e ≤ W s + e.path.1 a := by
      change (⨅ s, W s) + e.path.1 a ≤ _
      exact add_le_add (ciInf_le (isBounded_range W).bddBelow s) le_rfl
    _ = e.path.1 t := by
      change e.path.1 (a + (t - a)) - e.path.1 a + e.path.1 a = _
      rw [add_tsub_cancel_of_le ht.1, sub_add_cancel]

private def compactInteriorPositive (e : Excursion) : Prop :=
  ∀ a b : ℚ≥0, 0 < (a : ℝ≥0) → (a : ℝ≥0) < (b : ℝ≥0) →
    (b : ℝ≥0) < e.lifetime → 0 < excursionWindowInf a b e

private theorem measurableSet_compactInteriorPositive :
    MeasurableSet {e | compactInteriorPositive e} := by
  simp only [compactInteriorPositive, ofPred_forall]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_lt measurable_const measurable_excursion_lifetime).imp
    (measurableSet_lt measurable_const (measurable_excursionWindowInf a b))

private theorem compactInteriorPositive_pos {e : Excursion} (he : compactInteriorPositive e)
    (t : ℝ≥0) (ht : 0 < t) (htl : t < e.lifetime) : 0 < e.path.1 t := by
  obtain ⟨a, ha0, hat⟩ := exists_rat_btwn (show (0 : ℝ) < t by exact_mod_cast ht)
  obtain ⟨b, htb, hbl⟩ := exists_rat_btwn (show (t : ℝ) < e.lifetime by exact_mod_cast htl)
  let a' : ℚ≥0 := ⟨a, by exact_mod_cast ha0.le⟩
  let b' : ℚ≥0 := ⟨b, by exact_mod_cast (t.2.trans htb.le)⟩
  have ha' : (0 : ℝ≥0) < a' := by exact_mod_cast ha0
  have hat' : (a' : ℝ≥0) < t := by exact_mod_cast hat
  have htb' : t < (b' : ℝ≥0) := by exact_mod_cast htb
  have hbl' : (b' : ℝ≥0) < e.lifetime := by exact_mod_cast hbl
  exact (he a' b' ha' (hat'.trans htb') hbl').trans_le
    (windowInf_le_eval ⟨hat'.le, htb'.le⟩)

private theorem measurable_terminal_leftLim :
    Measurable (fun e : Excursion => Function.leftLim e.path.1 e.lifetime) := by
  let u : ℕ → Excursion → ℝ≥0 := fun n e => e.lifetime - 1 / (n + 1 : ℝ≥0)
  have hmeas (n : ℕ) : Measurable (fun e : Excursion => e.path.1 (u n e)) :=
    measurable_excursion_eval₂.comp
      (measurable_id.prodMk (measurable_excursion_lifetime.sub measurable_const))
  apply measurable_of_tendsto_metrizable hmeas
  apply tendsto_pi_nhds.mpr
  intro e
  have hu : Tendsto (fun n => u n e) atTop (𝓝[<] e.lifetime) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [tsub_zero] using
        (tendsto_const_nhds (x := e.lifetime)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    · exact Eventually.of_forall fun n => tsub_lt_self e.lifetime_pos (by positivity)
  exact (e.path.2.tendsto_nhdsLT_leftLim e.lifetime).comp hu

/-- **Support of `N`**: `N`-a.e. excursion is positive on `(0, ζ)`, its tag is
`sup {t | 0 < e t}`, `e 0 = 0`, `e` is continuous (right-continuous) at `0`, and `e t → 0` as
`t ↑ ζ`. (The carrier only supplies a positive *tag*; this support theorem identifies the tag with
the actual lifetime `sup {t | 0 < e t}`.) -/
theorem ae_excursionMeasure_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ),
      (∀ t : ℝ≥0, 0 < t → t < e.lifetime → 0 < e.path.1 t) ∧
        e.lifetime = sSup {t : ℝ≥0 | 0 < e.path.1 t} ∧
        e.path.1 0 = 0 ∧ ContinuousAt e.path.1 0 ∧
        Tendsto e.path.1 (𝓝[<] e.lifetime) (𝓝 0) := by
  have hpos : ∀ᵐ e ∂(excursionMeasure θ), compactInteriorPositive e := by
    apply ae_excursionMeasure_of_ae_jumpExcursion hθ measurableSet_compactInteriorPositive
    exact (ae_jumpExcursion_windowInf_pos hθ).mono fun f hf x hx a b ha hab hb =>
      hf x hx a b ha hab.le hb
  have hterm : ∀ᵐ e ∂(excursionMeasure θ), Function.leftLim e.path.1 e.lifetime = 0 := by
    apply ae_excursionMeasure_of_ae_jumpExcursion hθ
      (measurableSet_eq_fun measurable_terminal_leftLim measurable_const)
    filter_upwards [ae_jumpExcursion_support hθ] with f hf
    intro x hx
    let e := jumpExcursion x f
    let _ : (𝓝[<] e.lifetime).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, e.lifetime_pos⟩
    exact tendsto_nhds_unique (e.path.2.tendsto_nhdsLT_leftLim e.lifetime) (hf x hx).2.2.2.2
  filter_upwards [hpos, hterm] with e hp ht
  have hval := compactInteriorPositive_pos hp
  refine ⟨hval, ?_, e.2.1, ?_, ?_⟩
  · have hs : {t : ℝ≥0 | 0 < e.path.1 t} = Ioo 0 e.lifetime := by
      ext t
      constructor
      · intro h
        change 0 < e.path.1 t at h
        have ht0 : 0 < t := by
          by_contra hn
          have heq : t = 0 := le_antisymm (le_of_not_gt hn) bot_le
          have hz : e.path.1 0 = 0 := e.2.1
          rw [heq, hz] at h
          exact lt_irrefl 0 h
        refine ⟨ht0, ?_⟩
        by_contra hn
        have hz : e.path.1 t = 0 := e.2.2.2 t (le_of_not_gt hn)
        rw [hz] at h
        exact lt_irrefl 0 h
      · exact fun h => hval t h.1 h.2
    rw [hs, csSup_Ioo e.lifetime_pos]
  · apply continuousAt_iff_continuous_left'_right'.mpr
    exact ⟨by apply continuousWithinAt_of_notMem_closure; simp,
      e.path.2.isRightContinuous 0⟩
  · rw [← ht]
    exact e.path.2.tendsto_nhdsLT_leftLim e.lifetime

end BGW.StableTrees
