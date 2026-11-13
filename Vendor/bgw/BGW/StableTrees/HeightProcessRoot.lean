/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessContact
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Order.IsLUB

/-!
# Absence of an exploration atom at the root

Strict growth after upward passages transfers through bounded prefix laws. At a fixed
horizon, zero-height ancestors lie at the initial future-infimum level. Rational horizons
extend this statement simultaneously; upward jumps and continuous endpoints handle atoms.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Joint prefix measurability of the clock and its bounded evaluation time. -/
theorem measurable_supLocalTime_prefix_eval (θ : ℝ) (T : ℝ≥0) :
    Measurable[(MeasurableSpace.comap (DLoc.restrict T) inferInstance).prod inferInstance]
      (fun p : DLoc × Iic T => supLocalTime θ p.1 p.2) := by
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp (by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)))
  let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict T) inferInstance
  let F (k : ℕ) (f : DLoc) : C(Iic T, ℝ) :=
    ⟨fun u => supOccupation (supEps θ k) f u,
      (continuous_supOccupation (supEps_pos θ k) f).comp continuous_subtype_val⟩
  have hF (k : ℕ) : Measurable (F k) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro u
    exact (measurable_rawFiltration_supOccupation (supEps θ k) u).mono
      ((DLoc.rawFiltration.mono u.2).trans (rawFiltration_le_restrict_comap T)) le_rfl
  change Measurable (fun p : DLoc × Iic T =>
    limsup (fun k => supOccupation (supEps θ k) p.1 p.2) atTop)
  apply Measurable.limsup
  intro k
  have hp : Measurable (fun p : DLoc × Iic T => (F k p.1, p.2)) :=
    ((hF k).comp measurable_fst).prodMk measurable_snd
  exact Measurable.comp (g := fun q : C(Iic T, ℝ) × Iic T => q.1 q.2)
    (f := fun p : DLoc × Iic T => (F k p.1, p.2)) continuous_eval.measurable hp

private noncomputable def heightPassage (q : ℝ≥0) (f : DLoc) : ℝ≥0∞ :=
  DLoc.strictPassageAbove (q : ℝ) f

private noncomputable def boundedPassage (q T : ℝ≥0) (f : DLoc) : Iic T :=
  ⟨ENNReal.toNNReal (min (heightPassage q f) (T : ℝ≥0∞)), by
    change ENNReal.toNNReal (min (heightPassage q f) (T : ℝ≥0∞)) ≤ T
    have hh := ENNReal.toNNReal_mono (a := min (heightPassage q f) (T : ℝ≥0∞))
      (b := (T : ℝ≥0∞)) ENNReal.coe_ne_top (min_le_right _ _)
    simpa only [ENNReal.toNNReal_coe] using hh⟩

private theorem boundedPassage_lt_iff (q T : ℝ≥0) (f : DLoc) (r : Iic T) :
    boundedPassage q T f < r ↔ heightPassage q f < ((r : ℝ≥0) : ℝ≥0∞) := by
  have hfin : min (heightPassage q f) (T : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have he : ENNReal.toNNReal (min (heightPassage q f) (T : ℝ≥0∞)) < (r : ℝ≥0) ↔
      min (heightPassage q f) (T : ℝ≥0∞) < ((r : ℝ≥0) : ℝ≥0∞) := by
    simpa only [ENNReal.toNNReal_coe] using
      (ENNReal.toNNReal_lt_toNNReal (a := min (heightPassage q f) (T : ℝ≥0∞))
        (b := ((r : ℝ≥0) : ℝ≥0∞)) hfin ENNReal.coe_ne_top)
  apply he.trans
  rw [min_lt_iff]
  have hnot : ¬ (T : ℝ≥0∞) < ((r : ℝ≥0) : ℝ≥0∞) :=
    not_lt_of_ge (by exact_mod_cast r.2)
  simp only [hnot, or_false]

private theorem boundedPassage_eq (q T : ℝ≥0) (f : DLoc)
    (hτ : heightPassage q f < (T : ℝ≥0∞)) :
    (boundedPassage q T f : ℝ≥0) = ENNReal.toNNReal (heightPassage q f) := by
  change ENNReal.toNNReal (min (heightPassage q f) (T : ℝ≥0∞)) = _
  rw [min_eq_left hτ.le]

private theorem measurable_boundedPassage (q T : ℝ≥0) :
    Measurable[MeasurableSpace.comap (DLoc.restrict T) inferInstance] (boundedPassage q T) := by
  let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict T) inferInstance
  apply measurable_of_Iio
  intro r
  have he : (boundedPassage q T) ⁻¹' Iio r =
      ⋃ a : {a : ℚ // 0 ≤ a ∧ (a : ℝ) < (r : ℝ≥0)},
        {f : DLoc | (q : ℝ) < f.1 (a.1 : ℝ).toNNReal} := by
    ext f
    change boundedPassage q T f < r ↔ _
    rw [boundedPassage_lt_iff]
    change DLoc.strictPassageAbove (q : ℝ) f < ((r : ℝ≥0) : WithTop ℝ≥0) ↔ _
    rw [DLoc.strictPassageAbove_lt_iff]
    constructor
    · rintro ⟨a, ha0, har, ha⟩
      exact mem_iUnion.mpr ⟨⟨a, ha0, har⟩, ha⟩
    · intro h
      obtain ⟨a, ha⟩ := mem_iUnion.mp h
      exact ⟨a.1, a.2.1, a.2.2, ha⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro a
  have haT : (a.1 : ℝ).toNNReal ≤ T :=
    Real.toNNReal_le_iff_le_coe.mpr (a.2.2.le.trans (show (r : ℝ≥0) ≤ T from r.2))
  have hm : Measurable (fun f : DLoc => f.1 (a.1 : ℝ).toNNReal) :=
    (BGW.Skorokhod.measurable_eval
      ⟨(a.1 : ℝ).toNNReal, (a.1 : ℝ).toNNReal.2, haT⟩).comp
        (comap_measurable (DLoc.restrict T))
  exact measurableSet_lt measurable_const hm

private noncomputable def futurePassage (q T : ℝ≥0) (n : ℕ) (f : DLoc) : Iic T :=
  ⟨min ((boundedPassage q T f : ℝ≥0) + 1 / (n + 1 : ℝ≥0)) T,
    show min ((boundedPassage q T f : ℝ≥0) + 1 / (n + 1 : ℝ≥0)) T ≤ T from min_le_right _ _⟩

private theorem measurable_futurePassage (q T : ℝ≥0) (n : ℕ) :
    Measurable[MeasurableSpace.comap (DLoc.restrict T) inferInstance] (futurePassage q T n) := by
  let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict T) inferInstance
  apply Measurable.subtype_mk
  exact ((measurable_subtype_coe.comp (measurable_boundedPassage q T)).add_const _).min
    measurable_const

/-- Upward-passage clock growth is available inside a reversed prefix. -/
theorem ae_reversed_passage_clock_growth {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ,
      let g := reversedAt T f
      let τ : ℝ≥0∞ := DLoc.strictPassageAbove ((q : ℝ).toNNReal : ℝ) g
      τ < (T : ℝ≥0∞) → ∀ r : ℝ≥0, ENNReal.toNNReal τ < r → r ≤ T →
        supLocalTime θ g (ENNReal.toNNReal τ) < supLocalTime θ g r := by
  have hmeas (q : ℝ≥0) (n : ℕ) :
      MeasurableSet[MeasurableSpace.comap (DLoc.restrict T) inferInstance]
        {f : DLoc | (boundedPassage q T f : ℝ≥0) < T →
          supLocalTime θ f (boundedPassage q T f) < supLocalTime θ f (futurePassage q T n f)} := by
    let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict T) inferInstance
    have hm0 : Measurable (fun f : DLoc => supLocalTime θ f (boundedPassage q T f)) :=
      Measurable.comp (g := fun p : DLoc × Iic T => supLocalTime θ p.1 p.2)
        (f := fun f : DLoc => (f, boundedPassage q T f))
        (measurable_supLocalTime_prefix_eval θ T)
        (measurable_id.prodMk (measurable_boundedPassage q T))
    have hm1 : Measurable (fun f : DLoc => supLocalTime θ f (futurePassage q T n f)) :=
      Measurable.comp (g := fun p : DLoc × Iic T => supLocalTime θ p.1 p.2)
        (f := fun f : DLoc => (f, futurePassage q T n f))
        (measurable_supLocalTime_prefix_eval θ T)
        (measurable_id.prodMk (measurable_futurePassage q T n))
    have he : {f : DLoc | (boundedPassage q T f : ℝ≥0) < T →
          supLocalTime θ f (boundedPassage q T f) < supLocalTime θ f (futurePassage q T n f)} =
        {f : DLoc | (boundedPassage q T f : ℝ≥0) < T}ᶜ ∪
          {f : DLoc | supLocalTime θ f (boundedPassage q T f) <
            supLocalTime θ f (futurePassage q T n f)} := by
      ext f
      exact imp_iff_not_or
    rw [he]
    exact (measurableSet_lt
      (measurable_subtype_coe.comp (measurable_boundedPassage q T)) measurable_const).compl.union
        (measurableSet_lt hm0 hm1)
  have hp : MeasurableSet[MeasurableSpace.comap (DLoc.restrict T) inferInstance]
      {f : DLoc | ∀ q : ℚ, ∀ n : ℕ, (boundedPassage (q : ℝ).toNNReal T f : ℝ≥0) < T →
        supLocalTime θ f (boundedPassage (q : ℝ).toNNReal T f) <
          supLocalTime θ f (futurePassage (q : ℝ).toNNReal T n f)} := by
    simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter (fun q : ℚ => MeasurableSet.iInter
        (fun n : ℕ => hmeas (q : ℝ).toNNReal n))
  have ha : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ, ∀ n : ℕ,
      (boundedPassage (q : ℝ).toNNReal T f : ℝ≥0) < T →
      supLocalTime θ f (boundedPassage (q : ℝ).toNNReal T f) <
        supLocalTime θ f (futurePassage (q : ℝ).toNNReal T n f) := by
    have haq : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ,
        heightPassage (q : ℝ).toNNReal f < ⊤ →
        ∀ u : ℝ≥0, 0 < u →
          supLocalTime θ f (ENNReal.toNNReal (heightPassage (q : ℝ).toNNReal f)) <
            supLocalTime θ f (ENNReal.toNNReal (heightPassage (q : ℝ).toNNReal f) + u) :=
      ae_all_iff.mpr (fun q => ae_clock_increases_after_passage hθ (q : ℝ).toNNReal)
    filter_upwards [haq] with f hf
    intro q n hs
    have hτ := (boundedPassage_lt_iff (q : ℝ).toNNReal T f
      ⟨T, show T ≤ T from le_rfl⟩).mp hs
    have he := boundedPassage_eq (q : ℝ).toNNReal T f hτ
    have hsv : (boundedPassage (q : ℝ).toNNReal T f : ℝ≥0) <
        (futurePassage (q : ℝ).toNNReal T n f : ℝ≥0) :=
      lt_min (lt_add_of_pos_right _ (by positivity)) hs
    have hi := hf q (lt_of_lt_of_le hτ le_top)
      ((futurePassage (q : ℝ).toNNReal T n f : ℝ≥0) - boundedPassage (q : ℝ).toNNReal T f)
      (tsub_pos_iff_lt.mpr hsv)
    rw [← he, add_tsub_cancel_of_le hsv.le] at hi
    exact hi
  filter_upwards [ae_reversedAt_of_prefix hθ hT hp ha, ae_reversed_clock_prefix hθ hT]
    with f hf hg
  intro q
  dsimp only
  intro hτ r hsr hrT
  have he := boundedPassage_eq (q : ℝ).toNNReal T (reversedAt T f) hτ
  have hsT : (boundedPassage (q : ℝ).toNNReal T (reversedAt T f) : ℝ≥0) < T := by
    rw [he]
    exact ENNReal.toNNReal_lt_of_lt_coe hτ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_iff_lt.mpr hsr)
  have hsR : (boundedPassage (q : ℝ).toNNReal T (reversedAt T f) : ℝ≥0) < r := by
    simpa only [he, heightPassage] using hsr
  have hvR : (futurePassage (q : ℝ).toNNReal T n (reversedAt T f) : ℝ≥0) ≤ r := by
    apply (min_le_left _ _).trans
    have hδ : 1 / (n + 1 : ℝ≥0) ≤ r - boundedPassage (q : ℝ).toNNReal T (reversedAt T f) := by
      simpa only [he, heightPassage] using hn.le
    exact (le_tsub_iff_left hsR.le).mp hδ
  have hi := hf q n hsT
  have hm := hg.2.2.1 (show futurePassage (q : ℝ).toNNReal T n (reversedAt T f) ≤
      (⟨r, hrT⟩ : Iic T) from hvR)
  rw [he] at hi
  exact hi.trans_le hm

private theorem tendsto_leftLim_right_height (f : DLoc) (s : ℝ≥0) :
    Tendsto (Function.leftLim f.1) (𝓝[>] s) (𝓝 (f.1 s)) := by
  apply (closed_nhds_basis (f.1 s)).tendsto_right_iff.2
  rintro A ⟨hA, hclosed⟩
  obtain ⟨b, hsb, hb⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (lt_add_one s)).mp
    ((f.2.isRightContinuous s).eventually hA)
  filter_upwards [Ioo_mem_nhdsGT hsb] with x hx
  apply hclosed.mem_of_mapClusterPt (mapClusterPt_leftLim f.1 x)
  filter_upwards [Ioo_mem_nhdsLE_of_mem hx] with y hy using hb hy

/-- Left limits of the reversed supremum are terminal value minus the future infimum. -/
theorem leftLim_supRunning_reversedAt (f : DLoc) {t s : ℝ≥0} (hst : s < t)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r) :
    Function.leftLim (supRunning (reversedAt t f)) (t - s) = f.1 t - futureInf f t s := by
  let v := t - s
  let d : ℕ → ℝ≥0 := fun n => 1 / (n + 1 : ℝ≥0)
  let u : ℕ → ℝ≥0 := fun n => v - d n
  let r : ℕ → ℝ≥0 := fun n => t - u n
  have hv : 0 < v := tsub_pos_iff_lt.mpr hst
  have hdt : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hu : Tendsto u atTop (𝓝 v) := by
    simpa only [tsub_zero] using (tendsto_const_nhds (x := v)).sub hdt
  have hu_lt (n : ℕ) : u n < v := tsub_lt_self hv (by dsimp [d]; positivity)
  have hult : Tendsto u atTop (𝓝[<] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall hu_lt⟩
  have hr : Tendsto r atTop (𝓝 s) := by
    have hh := (tendsto_const_nhds (x := t)).sub hu
    simpa only [v, tsub_tsub_cancel_of_le hst.le] using hh
  have hsr (n : ℕ) : s < r n := by
    have hh := tsub_lt_tsub_left_of_le (show v ≤ t from tsub_le_self) (hu_lt n)
    simpa only [v, tsub_tsub_cancel_of_le hst.le] using hh
  have hrgt : Tendsto r atTop (𝓝[>] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr, Eventually.of_forall hsr⟩
  have hFc : ContinuousWithinAt (futureInf f t) (Ici s) s := by
    have hh := ((explorationStieltjes_spec f t).2 (s : ℝ)).comp
      continuous_subtype_val.continuousAt.continuousWithinAt
      (fun _ hu => hu)
    change ContinuousWithinAt (fun u : ℝ≥0 => futureInfFun f t (u : ℝ)) (Ici s) s at hh
    simpa only [futureInfFun, Real.toNNReal_coe] using hh
  have hFt : Tendsto (fun n => futureInf f t (r n)) atTop (𝓝 (futureInf f t s)) :=
    hFc.tendsto.comp (hrgt.mono_right (nhdsWithin_mono _ Ioi_subset_Ici_self))
  have hleft := (tendsto_leftLim_right_height f s).comp hrgt
  have hmin : Tendsto (fun n => min (Function.leftLim f.1 (r n)) (futureInf f t (r n)))
      atTop (𝓝 (futureInf f t s)) := by
    simpa only [Function.comp_def,
      min_eq_right (futureInf_le_eval f t s s ⟨min_le_left _ _, hst.le⟩)]
      using hleft.min hFt
  have he (n : ℕ) : supRunning (reversedAt t f) (u n) =
      f.1 t - min (Function.leftLim f.1 (r n)) (futureInf f t (r n)) := by
    have h := supRunning_reversedAt_window_left f (s := r n)
      (show r n ≤ t from tsub_le_self) hf
    have hut : u n ≤ t := (show u n ≤ v from tsub_le_self).trans tsub_le_self
    simpa only [r, tsub_tsub_cancel_of_le hut] using h
  have ht : Tendsto (fun n => supRunning (reversedAt t f) (u n)) atTop
      (𝓝 (f.1 t - futureInf f t s)) :=
    (tendsto_congr he).mpr (tendsto_const_nhds.sub hmin)
  exact tendsto_nhds_unique
    (((isCadlag_supRunning (reversedAt t f)).tendsto_nhdsLT_leftLim v).comp hult) ht

private theorem passage_le_of_sup_lt (g : DLoc) (q : ℝ≥0) (v : ℝ≥0)
    (hq : (q : ℝ) < supRunning g v) : heightPassage q g ≤ (v : ℝ≥0∞) := by
  rcases (lt_supRunning_iff (q : ℝ) g v).mp hq with h | h
  · exact h.le
  · exact iInf_le_of_le v (iInf_le _ h)

private theorem le_passage_of_sup_le (g : DLoc) (q : ℝ≥0) (v : ℝ≥0)
    (hq : supRunning g v ≤ (q : ℝ)) : (v : ℝ≥0∞) ≤ heightPassage q g := by
  change (v : WithTop ℝ≥0) ≤ ⨅ u : ℝ≥0, ⨅ (_ : (q : ℝ) < g.1 u), (u : WithTop ℝ≥0)
  apply le_iInf
  intro u
  apply le_iInf
  intro hqu
  have hvu : v ≤ u := by
    by_contra hnot
    exact (not_lt_of_ge ((eval_le_supRunning g (not_le.mp hnot).le).trans hq)) hqu
  exact_mod_cast hvu

private theorem le_passage_of_leftSup_le (g : DLoc) (q : ℝ≥0) (v : ℝ≥0)
    (hq : Function.leftLim (supRunning g) v ≤ (q : ℝ)) : (v : ℝ≥0∞) ≤ heightPassage q g := by
  change (v : WithTop ℝ≥0) ≤ ⨅ u : ℝ≥0, ⨅ (_ : (q : ℝ) < g.1 u), (u : WithTop ℝ≥0)
  apply le_iInf
  intro u
  apply le_iInf
  intro hqu
  have hvu : v ≤ u := by
    by_contra hnot
    have hlt : u < v := not_le.mp hnot
    have hh := (eval_le_supRunning g (t := u) le_rfl).trans
      (((monotone_supRunning g).le_leftLim hlt).trans hq)
    exact (not_lt_of_ge hh) hqu
  exact_mod_cast hvu

private theorem passage_lt_of_leftSup_lt (g : DLoc) (q : ℝ≥0) {v : ℝ≥0} (hv : 0 < v)
    (hq : (q : ℝ) < Function.leftLim (supRunning g) v) : heightPassage q g < (v : ℝ≥0∞) := by
  have : (𝓝[<] v).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hv⟩
  obtain ⟨u, hqu, huv⟩ := (((isCadlag_supRunning g).tendsto_nhdsLT_leftLim v).eventually
    (eventually_gt_nhds hq) |>.and self_mem_nhdsWithin).exists
  exact (passage_le_of_sup_lt g q u hqu).trans_lt (by exact_mod_cast huv)

private theorem stieltjes_initial_level_null (F : StieltjesFunction ℝ) (T : ℝ) :
    F.measure {x : ℝ | 0 < x ∧ x ≤ T ∧ F x = F 0} = 0 := by
  let E := {x : ℝ | 0 < x ∧ x ≤ T ∧ F x = F 0}
  have hzero (x : ℝ) (hx : x ∈ E) : F.measure (Ioc 0 x) = 0 := by
    rw [StieltjesFunction.measure_Ioc, hx.2.2, sub_self, ENNReal.ofReal_zero]
  by_cases hE : E.Nonempty
  · have hb : BddAbove E := ⟨T, fun _ hx => hx.2.1⟩
    let c := sSup E
    by_cases hc : c ∈ E
    · apply measure_mono_null (t := Ioc 0 c) _ (hzero c hc)
      intro x hx
      exact ⟨hx.1, le_csSup hb hx⟩
    · obtain ⟨u, _hu, ht, hun⟩ := exists_seq_tendsto_sSup hE hb
      apply measure_mono_null (t := ⋃ n, Ioc 0 (u n)) _
        (measure_iUnion_null (fun n => hzero (u n) (hun n)))
      intro x hx
      have hxc : x < c := lt_of_le_of_ne (le_csSup hb hx) (fun he => hc (he ▸ hx))
      obtain ⟨n, hn⟩ := (ht.eventually (eventually_gt_nhds hxc)).exists
      exact mem_iUnion.mpr ⟨n, hx.1, hn.le⟩
  · have he : E = ∅ := not_nonempty_iff_eq_empty.mp hE
    change F.measure E = 0
    rw [he, measure_empty]

private theorem sup_at_terminal_clock (θ : ℝ) (g : DLoc) {T v : ℝ≥0} (hvT : v < T)
    (hg0 : g.1 0 = 0)
    (hmono : Monotone (fun u : Iic T => supLocalTime θ g u))
    (hleftT : Function.leftLim (supRunning g) T = supRunning g T)
    (hgrowth : ∀ q : ℚ, heightPassage (q : ℝ).toNNReal g < (T : ℝ≥0∞) →
      ∀ r : ℝ≥0, ENNReal.toNNReal (heightPassage (q : ℝ).toNNReal g) < r → r ≤ T →
        supLocalTime θ g (ENNReal.toNNReal (heightPassage (q : ℝ).toNNReal g)) < supLocalTime θ g r)
    (he : supLocalTime θ g v = supLocalTime θ g T) :
    supRunning g v = supRunning g T ∧ Function.leftLim (supRunning g) v = supRunning g v := by
  have hnon (u : ℝ≥0) : 0 ≤ supRunning g u := by
    simpa only [hg0] using eval_le_supRunning g (u := 0) (show (0 : ℝ≥0) ≤ u from zero_le)
  have hSv : supRunning g v = supRunning g T := by
    apply le_antisymm (monotone_supRunning g hvT.le)
    by_contra hn
    obtain ⟨q, hvq, hqT⟩ := exists_rat_btwn (not_le.mp hn)
    have hq0 : 0 ≤ (q : ℝ) := (hnon v).trans hvq.le
    let Q := (q : ℝ).toNNReal
    have hQ : (Q : ℝ) = q := Real.coe_toNNReal _ hq0
    have hτT : heightPassage Q g < (T : ℝ≥0∞) := passage_lt_of_leftSup_lt g Q
      ((show (0 : ℝ≥0) ≤ v from zero_le).trans_lt hvT) (by rw [hleftT, hQ]; exact hqT)
    have hvτ : (v : ℝ≥0∞) ≤ heightPassage Q g :=
      le_passage_of_sup_le g Q v (by rw [hQ]; exact hvq.le)
    have hfinite : heightPassage Q g ≠ ⊤ := (lt_of_lt_of_le hτT le_top).ne
    have hvτN : v ≤ ENNReal.toNNReal (heightPassage Q g) :=
      ENNReal.le_toNNReal_of_coe_le hvτ hfinite
    have hτNT : ENNReal.toNNReal (heightPassage Q g) ≤ T :=
      (ENNReal.toNNReal_lt_of_lt_coe hτT).le
    have hh := hmono (show (⟨v, hvT.le⟩ : Iic T) ≤
      ⟨ENNReal.toNNReal (heightPassage Q g), hτNT⟩ from hvτN)
    change supLocalTime θ g v ≤ supLocalTime θ g (ENNReal.toNNReal (heightPassage Q g)) at hh
    rw [he] at hh
    have hi := hgrowth q hτT T (ENNReal.toNNReal_lt_of_lt_coe hτT) le_rfl
    exact (not_lt_of_ge hh) hi
  refine ⟨hSv, ?_⟩
  by_cases hv0 : v = 0
  · subst v
    exact leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ => zero_le)
  have hvpos : 0 < v := pos_iff_ne_zero.mpr hv0
  apply le_antisymm ((monotone_supRunning g).leftLim_le le_rfl)
  by_contra hn
  have hlnon : 0 ≤ Function.leftLim (supRunning g) v := by
    simpa only [supRunning_zero, hg0] using (monotone_supRunning g).le_leftLim hvpos
  obtain ⟨q, hlq, hqv⟩ := exists_rat_btwn (not_le.mp hn)
  have hq0 : 0 ≤ (q : ℝ) := hlnon.trans hlq.le
  let Q := (q : ℝ).toNNReal
  have hQ : (Q : ℝ) = q := Real.coe_toNNReal _ hq0
  have hlow : (v : ℝ≥0∞) ≤ heightPassage Q g :=
    le_passage_of_leftSup_le g Q v (by rw [hQ]; exact hlq.le)
  have hupp : heightPassage Q g ≤ (v : ℝ≥0∞) :=
    passage_le_of_sup_lt g Q v (by rw [hQ]; exact hqv)
  have hτeq : heightPassage Q g = (v : ℝ≥0∞) := le_antisymm hupp hlow
  have hτT : heightPassage Q g < (T : ℝ≥0∞) := by rw [hτeq]; exact_mod_cast hvT
  have hτN : ENNReal.toNNReal (heightPassage Q g) = v := by rw [hτeq, ENNReal.toNNReal_coe]
  have hi := hgrowth q hτT T (by rw [hτN]; exact hvT) le_rfl
  change supLocalTime θ g (ENNReal.toNNReal (heightPassage Q g)) < supLocalTime θ g T at hi
  rw [hτN, he] at hi
  have hh : supLocalTime θ g T < supLocalTime θ g T := hi
  exact (lt_irrefl _) hh

/-- A zero-height ancestor of a fixed horizon lies at the initial future-infimum level. -/
theorem ae_zero_height_ancestor_inf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0, 0 < s → s ≤ t →
      Function.leftLim f.1 s ≤ futureInf f t s → height θ f s = 0 →
        futureInf f t s = futureInf f t 0 := by
  filter_upwards [ae_reversed_clock_prefix hθ ht, ae_reversed_passage_clock_growth hθ ht,
    ae_height_ancestor_fixed hθ ht, ae_leftLim_le_stableLocalLaw hθ,
    ae_continuousAt_stableLocalLaw hθ t, ae_height_pos_fixed hθ ht]
    with f hg hgr ha hf htcont hpos
  let g := reversedAt t f
  have hg0 : g.1 0 = 0 := by
    change (reversedAt t f).1 0 = 0
    rw [reversedAt_apply]
    unfold reversedPath
    erw [zero_min, tsub_zero, htcont.continuousWithinAt.leftLim_eq]
    exact sub_self _
  have hs0 : Function.leftLim f.1 0 = f.1 0 :=
    leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ => zero_le)
  have hSt : supRunning g t = f.1 t - futureInf f t 0 := by
    simpa only [tsub_zero] using supRunning_reversedAt_window f
      (show (0 : ℝ≥0) ≤ t from zero_le) hf hs0
  have hLt : Function.leftLim (supRunning g) t = f.1 t - futureInf f t 0 := by
    simpa only [tsub_zero] using leftLim_supRunning_reversedAt f ht hf
  intro s hs hst hanc hz
  have hstlt : s < t := lt_of_le_of_ne hst (by
    intro he
    rw [he] at hz
    exact (ne_of_gt hpos) hz)
  have hM : supLocalTime θ g (t - s) = supLocalTime θ g t := by
    have hh := (ha s hst hanc).2.2.2
    rw [hz] at hh
    linarith only [hh]
  have hGR : ∀ q : ℚ, heightPassage (q : ℝ).toNNReal g < (t : ℝ≥0∞) →
      ∀ r : ℝ≥0, ENNReal.toNNReal (heightPassage (q : ℝ).toNNReal g) < r → r ≤ t →
        supLocalTime θ g (ENNReal.toNNReal (heightPassage (q : ℝ).toNNReal g)) <
          supLocalTime θ g r := by
    intro q
    exact hgr q
  have hSup := sup_at_terminal_clock θ g (tsub_lt_self ht hs) hg0 hg.2.2.1
    (hLt.trans hSt.symm) hGR hM
  have hFs := leftLim_supRunning_reversedAt f hstlt hf
  change Function.leftLim (supRunning g) (t - s) = f.1 t - futureInf f t s at hFs
  rw [hSup.2, hSup.1, hSt] at hFs
  linarith only [hFs]

/-- Splitting a future-infimum window at an intermediate horizon. -/
theorem futureInf_split (f : DLoc) {s q t : ℝ≥0} (hsq : s ≤ q) (hqt : q ≤ t) :
    futureInf f t s = min (futureInf f q s) (futureInf f t q) := by
  let : Nonempty (Icc (min s t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  have h₁ : futureInf f t s ≤ futureInf f q s := by
    let : Nonempty (Icc (min s q) q) := ⟨⟨q, min_le_right _ _, le_rfl⟩⟩
    apply le_ciInf
    intro u
    have hu : min s t ≤ (u : ℝ≥0) := by
      simpa only [min_eq_left (hsq.trans hqt), min_eq_left hsq] using u.2.1
    exact futureInf_le_eval f t s u ⟨hu, u.2.2.trans hqt⟩
  apply le_antisymm (le_min h₁ (monotone_futureInf f t hsq))
  apply le_ciInf
  intro u
  have hsu : s ≤ (u : ℝ≥0) := by
    simpa only [min_eq_left (hsq.trans hqt)] using u.2.1
  by_cases huq : (u : ℝ≥0) ≤ q
  · exact (min_le_left _ _).trans (futureInf_le_eval f q s u
      ⟨(min_le_left _ _).trans hsu, huq⟩)
  · exact (min_le_right _ _).trans (futureInf_le_eval f t q u
      ⟨(min_le_left _ _).trans (le_of_not_ge huq), u.2.2⟩)

/-- Upward jumps remain ancestral to some rational later horizon. -/
theorem exists_rat_ancestor_of_jump (f : DLoc) {s : ℝ≥0}
    (hs : Function.leftLim f.1 s < f.1 s) :
    ∃ q : ℚ, (s : ℝ) < q ∧ Function.leftLim f.1 s < futureInf f (q : ℝ).toNNReal s := by
  obtain ⟨a, hla, haf⟩ := exists_between hs
  have he := (continuousWithinAt_Ioi_iff_Ici.mp (f.2.isRightContinuous s)).eventually
    (eventually_gt_nhds haf)
  obtain ⟨b, hsb, hb⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (lt_add_one s)).mp he
  obtain ⟨q, hsq, hqb⟩ := exists_rat_btwn (show (s : ℝ) < b from by exact_mod_cast hsb)
  let Q := (q : ℝ).toNNReal
  have hQ : (Q : ℝ) = q := Real.coe_toNNReal _ ((show (0 : ℝ) ≤ s from s.2).trans hsq.le)
  have hsQ : s < Q := by exact_mod_cast (show (s : ℝ) < (Q : ℝ) by rw [hQ]; exact hsq)
  have hQb : Q < b := by exact_mod_cast (show (Q : ℝ) < (b : ℝ) by rw [hQ]; exact hqb)
  refine ⟨q, hsq, hla.trans_le ?_⟩
  let : Nonempty (Icc (min s Q) Q) := ⟨⟨Q, min_le_right _ _, le_rfl⟩⟩
  apply le_ciInf
  intro u
  apply (hb (show (u : ℝ≥0) ∈ Ico s b from ⟨by
    have hsu : min s Q ≤ (u : ℝ≥0) := u.2.1
    simpa only [min_eq_left hsQ.le] using hsu, u.2.2.trans_lt hQb⟩)).le

/-- A positive-time left limit bounds the future infimum from the root. -/
theorem futureInf_zero_le_leftLim (f : DLoc) {s t : ℝ≥0} (hs : 0 < s) (hst : s ≤ t) :
    futureInf f t 0 ≤ Function.leftLim f.1 s := by
  have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs⟩
  apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim s)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact futureInf_le_eval f t 0 u ⟨by simp only [zero_min]; exact zero_le, hu.le.trans hst⟩

/-- One null set controls zero-height ancestors at all strict later horizons. -/
theorem ae_zero_height_ancestor_inf_all {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t s : ℝ≥0, 0 < s → s < t →
      Function.leftLim f.1 s ≤ futureInf f t s → height θ f s = 0 →
        futureInf f t s = futureInf f t 0 := by
  have hrat (q : ℚ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < (q : ℝ) →
      ∀ s : ℝ≥0, 0 < s → s ≤ (q : ℝ).toNNReal →
        Function.leftLim f.1 s ≤ futureInf f (q : ℝ).toNNReal s → height θ f s = 0 →
          futureInf f (q : ℝ).toNNReal s = futureInf f (q : ℝ).toNNReal 0 := by
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [ae_zero_height_ancestor_inf hθ (Real.toNNReal_pos.mpr hq)] with f hf
      exact fun _ => hf
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [ae_all_iff.mpr hrat] with f hf
  intro t s hs hst ha hz
  obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn (show (s : ℝ) < t from by exact_mod_cast hst)
  let Q := (q : ℝ).toNNReal
  have hqpos : 0 < (q : ℝ) := (show (0 : ℝ) < s from by exact_mod_cast hs).trans hsq
  have hQ : (Q : ℝ) = q := Real.coe_toNNReal _ hqpos.le
  have hsQ : s ≤ Q := by exact_mod_cast (show (s : ℝ) ≤ (Q : ℝ) by rw [hQ]; exact hsq.le)
  have hQt : Q ≤ t := by exact_mod_cast (show (Q : ℝ) ≤ (t : ℝ) by rw [hQ]; exact hqt.le)
  have hsplit := futureInf_split f hsQ hQt
  have haq : Function.leftLim f.1 s ≤ futureInf f Q s :=
    ha.trans (hsplit.le.trans (min_le_left _ _))
  have he := hf q hqpos s hs hsQ haq hz
  rw [hsplit, he, futureInf_split f (show (0 : ℝ≥0) ≤ Q from zero_le) hQt]

/-- Every upward jump has positive height, on a single full-measure set. -/
theorem ae_height_pos_at_jumps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      Function.leftLim f.1 s < f.1 s → 0 < height θ f s := by
  filter_upwards [ae_zero_height_ancestor_inf_all hθ] with f hf
  intro s hs
  have hs0 : 0 < s := by
    by_contra hn
    have he : s = 0 := le_antisymm (not_lt.mp hn) (show (0 : ℝ≥0) ≤ s from zero_le)
    subst s
    rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ => zero_le)] at hs
    exact (lt_irrefl _) hs
  have hnon : 0 ≤ height θ f s := by
    rw [height, supLocalTime_eq_toReal]
    exact ENNReal.toReal_nonneg
  apply lt_of_le_of_ne hnon
  intro hz
  obtain ⟨q, hsq, haq⟩ := exists_rat_ancestor_of_jump f hs
  let Q := (q : ℝ).toNNReal
  have hQ : (Q : ℝ) = q := Real.coe_toNNReal _ ((show (0 : ℝ) ≤ s from s.2).trans hsq.le)
  have hsQ : s < Q := by exact_mod_cast (show (s : ℝ) < (Q : ℝ) by rw [hQ]; exact hsq)
  have he := hf Q s hs0 hsQ haq.le hz.symm
  have hh := (futureInf_zero_le_leftLim f hs0 hsQ.le)
  rw [← he] at hh
  exact (not_lt_of_ge hh) haq

/-- At a terminal continuity point, the future-infimum Stieltjes measure has no atom. -/
theorem explorationStieltjes_no_atom_of_leftLim_eq (f : DLoc) {t : ℝ≥0} (ht : 0 < t)
    (he : Function.leftLim f.1 t = f.1 t) :
    (explorationStieltjes f t).measure {(t : ℝ)} = 0 := by
  let F := explorationStieltjes f t
  have hF (u : ℝ≥0) : F (u : ℝ) = futureInf f t u := by
    simp only [F, explorationStieltjes, dite_eq_left (explorationStieltjes_spec f t),
      futureInfFun, Real.toNNReal_coe]
  have hFt : F (t : ℝ) = f.1 t := (hF t).trans (futureInf_self f t)
  have hleft : Function.leftLim F (t : ℝ) = f.1 t := by
    apply le_antisymm (by rw [← hFt]; exact F.mono.leftLim_le le_rfl)
    apply le_of_forall_lt
    intro a ha
    obtain ⟨b, hab, hbf⟩ := exists_between ha
    have hnear : ∀ᶠ u in 𝓝[<] t, b < f.1 u := by
      have hh := (f.2.tendsto_nhdsLT_leftLim t).eventually
        (eventually_gt_nhds (show b < Function.leftLim f.1 t by rw [he]; exact hbf))
      exact hh
    obtain ⟨l, hlt, hl⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' ht).mp hnear
    change l < t at hlt
    obtain ⟨v, hlv, hvt⟩ := exists_between hlt
    have hbI : b ≤ futureInf f t v := by
      let : Nonempty (Icc (min v t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
      apply le_ciInf
      intro u
      have hvu : v ≤ (u : ℝ≥0) := by simpa only [min_eq_left hvt.le] using u.2.1
      rcases u.2.2.eq_or_lt with hut | hut
      · simpa only [hut] using hbf.le
      · exact (hl ⟨hlv.trans_le hvu, hut⟩).le
    have hvl : F (v : ℝ) ≤ Function.leftLim F (t : ℝ) := F.mono.le_leftLim
      (show (v : ℝ) < t from by exact_mod_cast hvt)
    rw [hF] at hvl
    exact hab.trans_le (hbI.trans hvl)
  rw [StieltjesFunction.measure_singleton, hFt, hleft, sub_self, ENNReal.ofReal_zero]

/-- **No root atom**: a.s., simultaneously for all `t`, `ρ_t` has no atom at height `0`. -/
theorem ae_exploration_no_root_atom {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0, exploration θ f t {0} = 0 := by
  filter_upwards [ae_zero_height_ancestor_inf_all hθ, ae_height_pos_at_jumps hθ,
    ae_leftLim_le_stableLocalLaw hθ] with f ha hj hf
  intro t
  by_cases ht : t = 0
  · subst t
    have hz : exploration θ f 0 univ = 0 := by
      rw [exploration_univ, futureInf_self, sub_self, ENNReal.ofReal_zero]
    exact measure_mono_null (subset_univ _) hz
  let F := explorationStieltjes f t
  let μ := F.measure.restrict (Ioc 0 (t : ℝ))
  have hF (x : ℝ) : F x = futureInf f t x.toNNReal := by
    simp only [F, explorationStieltjes, dite_eq_left (explorationStieltjes_spec f t), futureInfFun]
  have hE := stieltjes_initial_level_null F (t : ℝ)
  have havoid := ae_restrict_of_ae (s := Ioc 0 (t : ℝ))
    (measure_eq_zero_iff_ae_notMem.mp hE)
  have hend : ∀ᵐ s ∂μ, s ≠ (t : ℝ) ∨ height θ f t ≠ 0 := by
    by_cases hJ : Function.leftLim f.1 t < f.1 t
    · exact Eventually.of_forall (fun _ => Or.inr (ne_of_gt (hj t hJ)))
    · have he : Function.leftLim f.1 t = f.1 t := le_antisymm (hf t) (not_lt.mp hJ)
      have hzero : μ {(t : ℝ)} = 0 := by
        apply le_antisymm _ (zero_le)
        calc μ {(t : ℝ)} ≤ F.measure {(t : ℝ)} := Measure.restrict_le_self _
             _ = 0 := explorationStieltjes_no_atom_of_leftLim_eq f
               (pos_iff_ne_zero.mpr ht) he
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with s hs
      exact Or.inl hs
  rw [exploration, Measure.map_apply (measurable_exploration_heightMap θ f)
    (measurableSet_singleton 0)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_exploration_ancestral_times f hf t, havoid, hend,
    ae_restrict_mem measurableSet_Ioc] with s hs hnot hend hst
  intro hroot
  have hnon : 0 ≤ height θ f s.toNNReal := by
    rw [height, supLocalTime_eq_toReal]
    exact ENNReal.toReal_nonneg
  have hz : height θ f s.toNNReal = 0 := by
    have hh := congrArg (fun x : ℝ≥0 => (x : ℝ))
      (show (height θ f s.toNNReal).toNNReal = 0 from hroot)
    simpa only [Real.coe_toNNReal _ hnon, NNReal.coe_zero] using hh
  have hstlt : s < (t : ℝ) := by
    apply lt_of_le_of_ne hst.2
    intro he
    rcases hend with hn | hn
    · exact hn he
    · apply hn
      simpa only [he, Real.toNNReal_coe] using hz
  have hlt : s.toNNReal < t := by
    exact_mod_cast (show (s.toNNReal : ℝ) < t by rw [Real.coe_toNNReal _ hst.1.le]; exact hstlt)
  have hh := ha t s.toNNReal (Real.toNNReal_pos.mpr hst.1) hlt hs hz
  apply hnot
  refine ⟨hst.1, hst.2, ?_⟩
  rw [hF, hF, Real.toNNReal_zero]
  exact hh

end BGW.StableTrees
