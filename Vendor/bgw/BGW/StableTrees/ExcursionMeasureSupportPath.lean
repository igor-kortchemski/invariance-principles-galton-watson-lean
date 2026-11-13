/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureBasic
import BGW.Skorokhod.Vervaat

/-! Compact interior lower bounds for excursion paths, using rational-window uniqueness.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem tendsto_add_nhdsLT (a t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => a + u) (𝓝[<] t) (𝓝[<] (a + t)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_const.add continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact (add_lt_add_iff_left a).mpr hu

private theorem leftLim_cut_interior {f : DLoc} {g d t : ℝ≥0}
    (hv : cutValid g d f) (ht : 0 < t) (htd : g + t < d) :
    Function.leftLim (excursionCut g d f).path.1 t =
      Function.leftLim f.1 (g + t) - f.1 g := by
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  apply leftLim_eq_of_tendsto
  have hh := ((f.2.tendsto_nhdsLT_leftLim (g + t)).comp
    (tendsto_add_nhdsLT g t)).sub_const (f.1 g)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [excursionCut_eval hv, min_eq_left (((add_lt_add_iff_left g).mpr hu).trans htd).le]
  rfl

private theorem leftLim_window {f : DLoc} (a b : ℝ≥0)
    (s : Icc (0 : ℝ) (b : ℝ)) (hs : 0 < (s : ℝ)) :
    Function.leftLim (DLoc.restrict b (DLoc.shift a f)) s =
      Function.leftLim f.1 (a + NNReal.mk s s.2.1) - f.1 a := by
  let inc : Icc (0 : ℝ) (b : ℝ) → ℝ≥0 := fun u => a + NNReal.mk u u.2.1
  have hc : Continuous inc := continuous_const.add
    (Continuous.subtype_mk continuous_subtype_val fun u => u.2.1)
  have hm : Tendsto inc (𝓝[<] s) (𝓝[<] (inc s)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    change a + (NNReal.mk u u.2.1) < a + (NNReal.mk s s.2.1)
    exact (add_lt_add_iff_left a).mpr (show NNReal.mk u u.2.1 < NNReal.mk s s.2.1 from hu)
  let z : Icc (0 : ℝ) (b : ℝ) := ⟨0, le_rfl, b.2⟩
  let _ : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hs⟩
  apply leftLim_eq_of_tendsto
  exact ((f.2.tendsto_nhdsLT_leftLim (inc s)).comp hm).sub_const (f.1 a)

/-- The infimum of the path on the compact window `[a,b]`, expressed with a centered
Skorokhod restriction so that its dependence on the path is measurable. -/
noncomputable def excursionWindowInf (a b : ℝ≥0) (e : Excursion) : ℝ :=
  (⨅ s, DLoc.restrict (b - a) (DLoc.shift a e.path) s) + e.path.1 a

/-- Compact window infima are measurable functions of the excursion mark. -/
theorem measurable_excursionWindowInf (a b : ℝ≥0) : Measurable (excursionWindowInf a b) := by
  exact (((lipschitzWith_one_iInf (b - a).2).continuous.measurable.comp
    ((DLoc.measurable_restrict (b - a)).comp
      ((DLoc.measurable_shift_fixed a).comp measurable_excursion_path))).add
        (measurable_excursion_eval a))

private theorem windowInf_pos {e : Excursion} {a b : ℝ≥0} (hab : a ≤ b)
    (hval : ∀ t ∈ Icc a b, 0 < e.path.1 t)
    (hleft : ∀ t ∈ Icc a b, 0 < Function.leftLim e.path.1 t) :
    0 < excursionWindowInf a b e := by
  let W := DLoc.restrict (b - a) (DLoc.shift a e.path)
  obtain ⟨s, hs⟩ := exists_min_leftLim W (b - a).2
  have htime : a + (NNReal.mk s s.2.1) ∈ Icc a b := by
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · exact ((add_le_add_iff_left a).mpr
        (show NNReal.mk s s.2.1 ≤ b - a from s.2.2)).trans_eq
          (add_tsub_cancel_of_le hab)
  have hv : 0 < W s + e.path.1 a := by
    change 0 < e.path.1 (a + (NNReal.mk s s.2.1)) - e.path.1 a + e.path.1 a
    simpa only [sub_add_cancel] using hval _ htime
  have hl : 0 < Function.leftLim W s + e.path.1 a := by
    by_cases hz : (s : ℝ) = 0
    · have hb : IsBot s := fun u => by change (s : ℝ) ≤ u; rw [hz]; exact u.2.1
      rwa [leftLim_eq_of_isBot hb]
    · rw [leftLim_window a (b - a) s (lt_of_le_of_ne s.2.1 (Ne.symm hz))]
      simpa only [sub_add_cancel] using hleft _ htime
  change 0 < (⨅ s, W s) + e.path.1 a
  rw [← hs, ← min_add_add_right]
  exact lt_min hl hv

/-- Almost surely, every marked excursion has a strictly positive left limit at every
strictly interior time. This excludes a second generalized minimizer in a rational window. -/
theorem ae_jumpExcursion_leftLim_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      ∀ t : ℝ≥0, 0 < t → t < (jumpExcursion x f).lifetime →
        0 < Function.leftLim (jumpExcursion x f).path.1 t := by
  filter_upwards [ae_jumpExcursion_spec hθ, ae_jump_window_inf hθ,
    ae_rationalWindowMinima hθ, ae_leftLim_le_stableLocalLaw hθ,
    ae_passageTime_eq_firstPassageBelow hθ, ae_continuousAt_jumpStart hθ]
      with f he hw hm hn hT hc
  intro x hx t ht htl
  let g := passageTimeMinus x f
  let d := passageTime x f
  have hgd : g < d := hx.2
  have hgt : g < g + t := lt_add_of_pos_right g ht
  have htd : g + t < d := by
    rw [(he x hx).2.1] at htl
    exact (lt_tsub_iff_left_of_le hgd.le).mp htl
  obtain ⟨_, q, _, htq, hqd⟩ := exists_supportWindow ((hw x hx).1.trans hgt) htd
  obtain ⟨r, _, hrg, _, _⟩ := exists_supportWindow (hw x hx).1 hgd
  have hgq : g < (q : ℝ≥0) := hgt.trans htq
  have hb (u : ℝ≥0) (hu : u ≤ (q : ℝ≥0)) : -(x : ℝ) ≤ f.1 u := by
    apply le_eval_of_lt_strictPassageBelow
    change (u : WithTop ℝ≥0) < firstPassageBelow x f
    rw [hT.1 x]
    exact_mod_cast hu.trans_lt hqd
  have hlow : -(x : ℝ) ≤ Function.leftLim f.1 (g + t) := by
    let _ : (𝓝[<] (g + t)).NeBot := nhdsLT_neBot_of_exists_lt
      ⟨0, (hw x hx).1.trans hgt⟩
    apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim (g + t))
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hb u (hu.le.trans htq.le)
  have hne : Function.leftLim f.1 (g + t) ≠ -(x : ℝ) := by
    intro hz
    have hgenG := isGenMinimizer_supportWindow hn hrg hgq (hw x hx).2.1 hb
    have hgenT := isGenMinimizer_supportWindow hn (hrg.trans hgt) htq hz hb
    have heq := congrArg Subtype.val ((hm r q (hrg.trans hgq) _ hgenG).2 _ hgenT)
    dsimp [shiftedWindowTime] at heq
    change (g : ℝ) + (t : ℝ) - (r : ℝ) = (g : ℝ) - (r : ℝ) at heq
    have htime : (g + t : ℝ≥0) = g := NNReal.coe_injective (by
      rw [NNReal.coe_add]
      linarith)
    exact hgt.ne htime.symm
  change 0 < Function.leftLim (excursionCut g d f).path.1 t
  rw [leftLim_cut_interior (he x hx).1 ht htd, (hc x hx).2.1]
  exact sub_pos.mpr (lt_of_le_of_ne hlow hne.symm)

/-- Every compact window strictly inside a jump excursion has a positive lower bound. -/
theorem ae_jumpExcursion_windowInf_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      ∀ a b : ℝ≥0, 0 < a → a ≤ b → b < (jumpExcursion x f).lifetime →
        0 < excursionWindowInf a b (jumpExcursion x f) := by
  filter_upwards [ae_jumpExcursion_support hθ, ae_jumpExcursion_leftLim_pos hθ]
    with f hv hl
  intro x hx a b ha hab hb
  exact windowInf_pos hab
    (fun t ht => (hv x hx).1 t (ha.trans_le ht.1) (ht.2.trans_lt hb))
    (fun t ht => hl x hx t (ha.trans_le ht.1) (ht.2.trans_lt hb))

end BGW.StableTrees
