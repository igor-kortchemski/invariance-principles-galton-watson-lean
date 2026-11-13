/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableUniqueMinimum
public import BGW.StableTrees.StableRegularity
public import BGW.StableTrees.StableProcessReversal
public import BGW.Skorokhod.JumpStopping
public import BGW.Skorokhod.DLocShiftAt
public import BGW.Skorokhod.ReverseIncrements

import Mathlib.Data.NNRat.Encodable
import Mathlib.Data.Rat.Encodable

/-!
# Continuity and interior location of the stable minimum

Regularity after the countably many jump stopping times transfers from the local stable law to
compact horizons. Reversal of increments then excludes generalized minimizers at jump times, and
regularity at zero excludes the two endpoints. Together with uniqueness of generalized minimizers,
this gives a unique continuously attained interior minimum (P. W. Millar, Zero-one laws and the
minimum of a Markov process, Trans. Amer. Math. Soc. 226 (1977), 365–391).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

open BGW.Skorokhod

private theorem leftLim_dloc_restrict {f : DLoc} {t T : ℝ≥0} (ht : 0 < t) (htT : t < T) :
    Function.leftLim (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩ = Function.leftLim f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  let inc : Set.Icc (0 : ℝ) (T : ℝ) → ℝ≥0 := fun u => ⟨u, u.2.1⟩
  have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val fun u => u.2.1
  have hleft : Tendsto inc (𝓝[<] t') (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu
  let z : Set.Icc (0 : ℝ) (T : ℝ) := ⟨0, le_rfl, T.2⟩
  have hz : z < t' := ht
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  let _ : (𝓝[<] t').NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto
  exact (f.2.tendsto_nhdsLT_leftLim t).comp hleft

private def extendLocal (T : ℝ≥0) (f : D (T : ℝ) ℝ) : DLoc := by
  let κ : ℝ≥0 → Set.Icc (0 : ℝ) (T : ℝ) := fun u =>
    ⟨min (u : ℝ) T, le_min u.2 T.2, min_le_right _ _⟩
  have hκ : Continuous κ := Continuous.subtype_mk
    (continuous_subtype_val.min continuous_const) fun u => ⟨le_min u.2 T.2, min_le_right _ _⟩
  refine ⟨fun u => f (κ u), ?_⟩
  constructor
  · intro t
    by_cases ht : (t : ℝ) < T
    · have hmap : MapsTo κ (Set.Ioi t) (Set.Ioi (κ t)) := by
        intro u hu
        change (t : ℝ) < (u : ℝ) at hu
        change (κ t : ℝ) < (κ u : ℝ)
        simp only [κ, min_eq_left ht.le]
        exact lt_min_iff.mpr ⟨hu, ht⟩
      exact f.2.isRightContinuous (κ t) |>.comp
        hκ.continuousAt.continuousWithinAt hmap
    · have htT : T ≤ (t : ℝ) := le_of_not_gt ht
      have hconst : ∀ u ∈ Set.Ioi t, κ u = κ t := by
        intro u hu
        change (t : ℝ) < (u : ℝ) at hu
        apply Subtype.ext
        simp [κ, min_eq_right htT, min_eq_right (htT.trans hu.le)]
      exact tendsto_nhdsWithin_congr (fun u hu => congrArg f (hconst u hu).symm)
        tendsto_const_nhds
  · intro t
    by_cases ht : (t : ℝ) ≤ T
    · have hmap : MapsTo κ (Set.Iio t) (Set.Iio (κ t)) := by
        intro u hu
        change (u : ℝ) < (t : ℝ) at hu
        have huT : (u : ℝ) ≤ T := hu.le.trans ht
        change (κ u : ℝ) < (κ t : ℝ)
        simp only [κ, min_eq_left huT, min_eq_left ht]
        exact hu
      obtain ⟨l, hl⟩ := f.2.tendsto_nhdsLT (κ t)
      have hκleft : Tendsto κ (𝓝[Set.Iio t] t) (𝓝[Set.Iio (κ t)] (κ t)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hκ.continuousAt, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hmap hu
      exact ⟨l, hl.comp hκleft⟩
    · have htT : T < t := by exact_mod_cast (lt_of_not_ge ht)
      have hev : ∀ᶠ u in 𝓝[Set.Iio t] t, T < u :=
        (eventually_gt_nhds htT).filter_mono nhdsWithin_le_nhds
      have hconst : ∀ u : ℝ≥0, T < u → κ u = κ t := by
        intro u hu
        apply Subtype.ext
        have hu' : (T : ℝ) ≤ (u : ℝ) := hu.le
        simp [κ, min_eq_right hu', min_eq_right (show (T : ℝ) ≤ (t : ℝ) from htT.le)]
      have hfg : (fun u : ℝ≥0 => f (κ u)) =ᶠ[𝓝[Set.Iio t] t]
          fun _ => f (κ t) := by
        filter_upwards [hev] with u hu
        exact congrArg f (hconst u hu)
      exact ⟨f (κ t), (tendsto_congr' hfg).2 tendsto_const_nhds⟩

private theorem extendLocal_apply_of_le {T u : ℝ≥0} (hu : u ≤ T) (f : D (T : ℝ) ℝ) :
    (extendLocal T f).1 u = f ⟨u, u.2, hu⟩ := by
  change f _ = f _
  congr 1
  exact Subtype.ext (min_eq_left hu)

private theorem measurable_extendLocal (T : ℝ≥0) : Measurable (extendLocal T) := by
  rw [measurable_iff_comap_le]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance).comap
    (extendLocal T) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro t
  rw [MeasurableSpace.comap_comp]
  let κt : Set.Icc (0 : ℝ) (T : ℝ) :=
    ⟨min (t : ℝ) T, le_min t.2 T.2, min_le_right _ _⟩
  have hm : Measurable (fun f : D (T : ℝ) ℝ => f κt) := measurable_eval κt
  exact hm.comap_le

private theorem leftLim_extendLocal {T t : ℝ≥0} {f : D (T : ℝ) ℝ} (ht : 0 < t) (htT : t < T) :
    Function.leftLim (extendLocal T f).1 t = Function.leftLim f ⟨t, t.2, htT.le⟩ := by
  let inc : ℝ≥0 → Set.Icc (0 : ℝ) (T : ℝ) := fun u =>
    ⟨min (u : ℝ) T, le_min u.2 T.2, min_le_right _ _⟩
  have hinc : Continuous inc := Continuous.subtype_mk
    (continuous_subtype_val.min continuous_const) fun u => ⟨le_min u.2 T.2, min_le_right _ _⟩
  have hleft : Tendsto inc (𝓝[<] t) (𝓝[<] (⟨t, t.2, htT.le⟩ : Set.Icc (0 : ℝ) (T : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hcont : Tendsto inc (𝓝 t)
        (𝓝 (⟨t, t.2, htT.le⟩ : Set.Icc (0 : ℝ) (T : ℝ))) := by
      have hct : inc t = (⟨t, t.2, htT.le⟩ : Set.Icc (0 : ℝ) (T : ℝ)) :=
        Subtype.ext (min_eq_left htT.le)
      rw [← hct]
      exact hinc.continuousAt
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hcont, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    change min (u : ℝ) T < (t : ℝ)
    exact (min_eq_left (hu.le.trans htT.le)).trans_lt hu
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  let z : Set.Icc (0 : ℝ) (T : ℝ) := ⟨0, le_rfl, T.2⟩
  have hz : z < (⟨t, t.2, htT.le⟩ : Set.Icc (0 : ℝ) (T : ℝ)) := ht
  let _ : (𝓝[<] (⟨t, t.2, htT.le⟩ : Set.Icc (0 : ℝ) (T : ℝ))).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto
  have htend := (f.2.tendsto_nhdsLT_leftLim ⟨t, t.2, htT.le⟩).comp hleft
  have heq : (fun u => (extendLocal T f).1 u) =ᶠ[𝓝[<] t]
      (fun u => f (inc u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    calc
      (extendLocal T f).1 u = f ⟨u, u.2, hu.le.trans htT.le⟩ :=
        extendLocal_apply_of_le (hu.le.trans htT.le) f
      _ = f (inc u) := congrArg f (Subtype.ext (min_eq_left (hu.le.trans htT.le)).symm)
  exact (tendsto_congr' heq).2 htend

private theorem regularBelowAtZero_congr {f g : DLoc}
    (h : (fun u => DLoc.eval u f) =ᶠ[𝓝[>] (0 : ℝ≥0)] fun u => DLoc.eval u g) :
    DLoc.RegularBelowAtZero f ↔ DLoc.RegularBelowAtZero g := by
  obtain ⟨b, hb, hbg⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  constructor <;> intro hr ε hε
  · obtain ⟨t, ht, htε, hval⟩ := hr (min ε b) (lt_min hε hb)
    refine ⟨t, ht, htε.trans_le (min_le_left _ _), ?_⟩
    have heq := hbg ⟨ht, htε.trans_le (min_le_right _ _)⟩
    change DLoc.eval t f = DLoc.eval t g at heq
    rw [← heq]
    exact hval
  · obtain ⟨t, ht, htε, hval⟩ := hr (min ε b) (lt_min hε hb)
    refine ⟨t, ht, htε.trans_le (min_le_left _ _), ?_⟩
    have heq := hbg ⟨ht, htε.trans_le (min_le_right _ _)⟩
    change DLoc.eval t f = DLoc.eval t g at heq
    rw [heq]
    exact hval

private theorem regularAboveAtZero_congr {f g : DLoc}
    (h : (fun u => DLoc.eval u f) =ᶠ[𝓝[>] (0 : ℝ≥0)] fun u => DLoc.eval u g) :
    DLoc.RegularAboveAtZero f ↔ DLoc.RegularAboveAtZero g := by
  obtain ⟨b, hb, hbg⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  constructor <;> intro hr ε hε
  · obtain ⟨t, ht, htε, hval⟩ := hr (min ε b) (lt_min hε hb)
    refine ⟨t, ht, htε.trans_le (min_le_left _ _), ?_⟩
    have heq := hbg ⟨ht, htε.trans_le (min_le_right _ _)⟩
    change DLoc.eval t f = DLoc.eval t g at heq
    rw [← heq]
    exact hval
  · obtain ⟨t, ht, htε, hval⟩ := hr (min ε b) (lt_min hε hb)
    refine ⟨t, ht, htε.trans_le (min_le_left _ _), ?_⟩
    have heq := hbg ⟨ht, htε.trans_le (min_le_right _ _)⟩
    change DLoc.eval t f = DLoc.eval t g at heq
    rw [heq]
    exact hval

private theorem jumpSize_extendLocal {T t : ℝ≥0} (ht : 0 < t) (htT : t < T)
    (f : D (T : ℝ) ℝ) :
    jumpSize (extendLocal T f).1 t =
      |f ⟨t, t.2, htT.le⟩ - Function.leftLim f ⟨t, t.2, htT.le⟩| := by
  unfold jumpSize
  rw [extendLocal_apply_of_le htT.le, leftLim_extendLocal ht htT]

private theorem jumpSize_extendLocal_restrict {T t : ℝ≥0} (ht : 0 < t) (htT : t < T)
    (f : DLoc) :
    jumpSize (extendLocal T (DLoc.restrict T f)).1 t = jumpSize f.1 t := by
  unfold jumpSize
  rw [extendLocal_apply_of_le htT.le, leftLim_extendLocal ht htT,
    leftLim_dloc_restrict ht htT]
  rfl

private theorem firstJumpAbove_eq_of_lt {f g : DLoc} (q : ℝ≥0) {ε : ℝ} (hε : 0 < ε)
    {T : ℝ≥0} (hsize : ∀ s : ℝ≥0, 0 < s → s < T → jumpSize f.1 s = jumpSize g.1 s)
    (hlt : firstJumpAbove q ε f.1 < (T : ℝ≥0∞)) :
    firstJumpAbove q ε g.1 = firstJumpAbove q ε f.1 := by
  have hfin : firstJumpAbove q ε f.1 < ⊤ := hlt.trans (WithTop.coe_lt_top _)
  let r : ℝ≥0 := ENNReal.toNNReal (firstJumpAbove q ε f.1)
  have hr : firstJumpAbove q ε f.1 = (r : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hfin.ne).symm
  have hrt : r < T := by
    rw [hr] at hlt
    exact_mod_cast hlt
  obtain ⟨hqr, hrjump, hrmin⟩ := firstJumpAbove_attained f.2 q hε hr
  have hrpos : 0 < r := q.2.trans_lt hqr
  rw [hr]
  apply le_antisymm
  · rw [firstJumpAbove]
    refine iInf_le_of_le r (iInf_le_of_le ⟨hqr, ?_⟩ le_rfl)
    rw [← hsize r hrpos hrt]
    exact hrjump
  · rw [firstJumpAbove]
    apply le_iInf
    intro s
    apply le_iInf
    intro hs
    have hspos : 0 < s := q.2.trans_lt hs.1
    by_cases hst : s < T
    · have hs' : ε < jumpSize f.1 s := by
        rw [hsize s hspos hst]
        exact hs.2
      exact WithTop.coe_le_coe.mpr (hrmin s hs.1 hs')
    · exact WithTop.coe_le_coe.mpr (hrt.le.trans (le_of_not_gt hst))

private theorem regular_shift_extendLocal {T t : ℝ≥0} (htT : t < T) (f : DLoc)
    {τ : DLoc → ℝ≥0∞} (hτf : τ f = (t : ℝ≥0∞))
    (hτe : τ (extendLocal T (DLoc.restrict T f)) = (t : ℝ≥0∞)) :
    (DLoc.RegularBelowAtZero
        (DLoc.shiftAt τ (extendLocal T (DLoc.restrict T f))) ∧
        DLoc.RegularAboveAtZero
          (DLoc.shiftAt τ (extendLocal T (DLoc.restrict T f)))) ↔
      (DLoc.RegularBelowAtZero (DLoc.shiftAt τ f) ∧
        DLoc.RegularAboveAtZero (DLoc.shiftAt τ f)) := by
  have hfinf : τ f < ⊤ := by rw [hτf]; exact WithTop.coe_lt_top _
  have hfine : τ (extendLocal T (DLoc.restrict T f)) < ⊤ := by
    rw [hτe]
    exact WithTop.coe_lt_top _
  have htimef : ENNReal.toNNReal (τ f) = t := by simp [hτf]
  have htimee : ENNReal.toNNReal (τ (extendLocal T (DLoc.restrict T f))) = t := by
    simp [hτe]
  have heq : (fun u => DLoc.eval u (DLoc.shiftAt τ f)) =ᶠ[𝓝[>] (0 : ℝ≥0)]
      fun u => DLoc.eval u (DLoc.shiftAt τ (extendLocal T (DLoc.restrict T f))) := by
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    refine ⟨T - t, tsub_pos_of_lt htT, ?_⟩
    intro s hs
    have hst : t + s < T := by
      have hs' : (s : ℝ) < ((T - t : ℝ≥0) : ℝ) := hs.2
      rw [NNReal.coe_sub htT.le] at hs'
      exact_mod_cast (show (t : ℝ) + (s : ℝ) < T by linarith)
    change DLoc.eval s (DLoc.shiftAt τ f) =
      DLoc.eval s (DLoc.shiftAt τ (extendLocal T (DLoc.restrict T f)))
    rw [DLoc.eval_shiftAt _ _ hfinf, DLoc.eval_shiftAt _ _ hfine, htimef, htimee]
    change f.1 (t + s) - f.1 t =
      (extendLocal T (DLoc.restrict T f)).1 (t + s) -
        (extendLocal T (DLoc.restrict T f)).1 t
    rw [extendLocal_apply_of_le htT.le, extendLocal_apply_of_le hst.le]
    rfl
  exact (regularBelowAtZero_congr heq.symm).and (regularAboveAtZero_congr heq.symm)

/-- On `DLoc`: almost surely, immediately after every jump time `t > 0` the path takes values
strictly below and strictly above its post-jump value `f t` (strong Markov property at the jump
stopping times and regularity of `0`). -/
theorem ae_regular_after_jumps_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ t : ℝ≥0, 0 < t → f.1 t ≠ Function.leftLim f.1 t → ∀ ε : ℝ≥0, 0 < ε →
        (∃ s : ℝ≥0, 0 < s ∧ s < ε ∧ f.1 (t + s) < f.1 t) ∧
        (∃ s : ℝ≥0, 0 < s ∧ s < ε ∧ f.1 t < f.1 (t + s)) := by
  obtain ⟨J, hJstop, hJcover⟩ := exists_jumpStoppingTimes
  have hreg (n : ℕ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), J n f < ⊤ →
      DLoc.RegularBelowAtZero (DLoc.shiftAt (J n) f) ∧
        DLoc.RegularAboveAtZero (DLoc.shiftAt (J n) f) :=
    ae_regular_both_shiftAt_stableLocalLaw hθ (hJstop n)
  filter_upwards [ae_all_iff.mpr hreg] with f hf
  intro t ht hjump ε hε
  obtain ⟨n, hn⟩ := hJcover f t ht hjump
  have hfin : J n f < ⊤ := by rw [hn]; exact WithTop.coe_lt_top _
  have htime : ENNReal.toNNReal (J n f) = t := by simp [hn]
  have h := hf n hfin
  simp only [DLoc.RegularBelowAtZero, DLoc.RegularAboveAtZero,
    DLoc.eval_shiftAt _ _ hfin, htime, sub_neg, sub_pos] at h
  exact ⟨h.1 ε hε, h.2 ε hε⟩

/-- Regularity after jumps on a compact horizon: for a stable Lévy law on `[0,T]`, almost surely at
every jump time `t < T` the path takes values both below and above `f t` in `(t, t + ε)`, for
every `ε > 0`. -/
theorem IsStableLevyLaw.ae_regular_after_jumps {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ t : Set.Icc (0 : ℝ) T, (t : ℝ) < T → f t ≠ Function.leftLim f t → ∀ ε : ℝ, 0 < ε →
        (∃ s : Set.Icc (0 : ℝ) T, (t : ℝ) < s ∧ (s : ℝ) < t + ε ∧ f s < f t) ∧
        (∃ s : Set.Icc (0 : ℝ) T, (t : ℝ) < s ∧ (s : ℝ) < t + ε ∧ f t < f s) := by
  let Tnn : ℝ≥0 := ⟨T, hT.le⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ≥0 × {ε : ℚ // 0 < ε})
  let J : ℕ → DLoc → ℝ≥0∞ := fun n f =>
    firstJumpAbove ((e n).1 : ℝ≥0) (((e n).2 : ℚ) : ℝ) f.1
  have hJstop (n : ℕ) : IsStoppingTime DLoc.filtration (J n) :=
    isStoppingTime_firstJumpAbove (e n).1 (e n).2.2
  let A : DLoc → Prop := fun f => ∀ n, J n f < (Tnn : ℝ≥0∞) →
    DLoc.RegularBelowAtZero (DLoc.shiftAt (J n) f) ∧
      DLoc.RegularAboveAtZero (DLoc.shiftAt (J n) f)
  have hAae : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), A f := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [ae_regular_both_shiftAt_stableLocalLaw hθ (hJstop n)] with f hf hn
    exact hf (hn.trans (WithTop.coe_lt_top _))
  have hregmeas (n : ℕ) : MeasurableSet {f : DLoc |
      DLoc.RegularBelowAtZero (DLoc.shiftAt (J n) f) ∧
        DLoc.RegularAboveAtZero (DLoc.shiftAt (J n) f)} :=
    DLoc.measurable_shiftAt (hJstop n)
      (DLoc.measurableSet_regularBelowAtZero.inter DLoc.measurableSet_regularAboveAtZero)
  have hAmeas : MeasurableSet {f | A f} := by
    unfold A
    have hm := MeasurableSet.iInter fun n =>
      ((hJstop n).measurable'
        (measurableSet_Iio : MeasurableSet (Set.Iio (Tnn : ℝ≥0∞)))).imp (hregmeas n)
    convert hm using 1
    ext f
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor <;> intro h i hi
    · exact h i hi
    · exact h i hi
  let B : D (Tnn : ℝ) ℝ → Prop := fun g => A (extendLocal Tnn g)
  have hBmeas : MeasurableSet {g | B g} := hAmeas.preimage (measurable_extendLocal Tnn)
  have hpre (f : DLoc) : B (DLoc.restrict Tnn f) ↔ A f := by
    constructor
    · intro hB n hn
      have htime : J n (extendLocal Tnn (DLoc.restrict Tnn f)) = J n f := by
        apply firstJumpAbove_eq_of_lt ((e n).1 : ℝ≥0)
          (by exact_mod_cast (e n).2.2) _ hn
        intro s hs hsT
        exact (jumpSize_extendLocal_restrict hs hsT f).symm
      have hfin : J n f < ⊤ := hn.trans (WithTop.coe_lt_top _)
      let t : ℝ≥0 := ENNReal.toNNReal (J n f)
      have htf : J n f = (t : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
      have hte : J n (extendLocal Tnn (DLoc.restrict Tnn f)) = (t : ℝ≥0∞) := htime.trans htf
      have htT : t < Tnn := by
        have ht : (t : ℝ≥0∞) < (Tnn : ℝ≥0∞) := htf.symm.trans_lt hn
        exact_mod_cast ht
      apply (regular_shift_extendLocal htT f htf hte).mp
      apply hB n
      rwa [htime]
    · intro hA n hn
      have htime : J n f = J n (extendLocal Tnn (DLoc.restrict Tnn f)) := by
        apply firstJumpAbove_eq_of_lt ((e n).1 : ℝ≥0)
          (by exact_mod_cast (e n).2.2) _ hn
        intro s hs hsT
        exact jumpSize_extendLocal_restrict hs hsT f
      have htime' : J n (extendLocal Tnn (DLoc.restrict Tnn f)) = J n f := htime.symm
      have hfin : J n f < ⊤ := by
        rw [htime]
        exact hn.trans (WithTop.coe_lt_top _)
      let t : ℝ≥0 := ENNReal.toNNReal (J n f)
      have htf : J n f = (t : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
      have hte : J n (extendLocal Tnn (DLoc.restrict Tnn f)) = (t : ℝ≥0∞) := htime'.trans htf
      have htT : t < Tnn := by
        have ht : (t : ℝ≥0∞) < (Tnn : ℝ≥0∞) := htf.symm.trans_lt (htime.trans_lt hn)
        exact_mod_cast ht
      apply (regular_shift_extendLocal htT f htf hte).mpr
      apply hA n
      rwa [htime]
  have hmapped : ∀ᵐ g ∂((stableLocalLaw θ : Measure DLoc).map (DLoc.restrict Tnn)), B g := by
    apply (ae_map_iff (DLoc.measurable_restrict Tnn).aemeasurable hBmeas).mpr
    filter_upwards [hAae] with f hf
    exact (hpre f).mpr hf
  rw [map_restrict_stableLocalLaw hθ (T := Tnn) (by exact hT)] at hmapped
  rw [hP.unique hθ hT (isStableLevyLaw_stableProcessLaw hθ hT)]
  filter_upwards [hmapped] with g hg
  intro t htT hjump ε hε
  have ht0 : 0 < (t : ℝ) := by
    apply lt_of_le_of_ne t.2.1
    intro ht
    apply hjump
    have hbot : IsBot t := by
      intro u
      change (t : ℝ) ≤ (u : ℝ)
      rw [← ht]
      exact u.2.1
    exact (leftLim_eq_of_isBot hbot).symm
  let tn : ℝ≥0 := ⟨t, t.2.1⟩
  have htnT : tn < Tnn := htT
  let E : DLoc := extendLocal Tnn g
  have hjumpE : E.1 tn ≠ Function.leftLim E.1 tn := by
    intro heq
    apply hjump
    have hval : E.1 tn = g t := extendLocal_apply_of_le htnT.le g
    have hleft : Function.leftLim E.1 tn = Function.leftLim g t :=
      leftLim_extendLocal ht0 htnT
    exact hval.symm.trans (heq.trans hleft)
  obtain ⟨q, δ, hδpos, hfirst⟩ := exists_rat_firstJumpAbove_eq E.2 ht0 hjumpE
  obtain ⟨n, hn⟩ := he (q, ⟨δ, hδpos⟩)
  have hJE : J n E = (tn : ℝ≥0∞) := by
    dsimp [J]
    rw [hn]
    exact hfirst
  have hreg := hg n (by rw [hJE]; exact_mod_cast htnT)
  have hfin : J n E < ⊤ := by rw [hJE]; exact WithTop.coe_lt_top _
  have htime : ENNReal.toNNReal (J n E) = tn := by simp [hJE]
  change DLoc.RegularBelowAtZero (DLoc.shiftAt (J n) E) ∧
    DLoc.RegularAboveAtZero (DLoc.shiftAt (J n) E) at hreg
  simp only [DLoc.RegularBelowAtZero, DLoc.RegularAboveAtZero,
    DLoc.eval_shiftAt _ _ hfin, htime, sub_neg, sub_pos] at hreg
  let δr : ℝ := min ε (T - (t : ℝ))
  have hδr : 0 < δr := lt_min hε (sub_pos.mpr htT)
  let δnn : ℝ≥0 := ⟨δr, hδr.le⟩
  obtain ⟨sb, hb0, hbδ, hbbelow⟩ := hreg.1 δnn hδr
  obtain ⟨sa, ha0, haδ, haabove⟩ := hreg.2 δnn hδr
  have hbδR : (sb : ℝ) < δr := hbδ
  have haδR : (sa : ℝ) < δr := haδ
  have hbT : (t : ℝ) + (sb : ℝ) < T := by
    dsimp [δr] at hbδR
    linarith [hbδR.trans_le (min_le_right _ _)]
  have haT : (t : ℝ) + (sa : ℝ) < T := by
    dsimp [δr] at haδR
    linarith [haδR.trans_le (min_le_right _ _)]
  let ub : Set.Icc (0 : ℝ) T := ⟨(t : ℝ) + sb, add_nonneg t.2.1 sb.2, hbT.le⟩
  let ua : Set.Icc (0 : ℝ) T := ⟨(t : ℝ) + sa, add_nonneg t.2.1 sa.2, haT.le⟩
  have hbε : (sb : ℝ) < ε := hbδR.trans_le (min_le_left _ _)
  have haε : (sa : ℝ) < ε := haδR.trans_le (min_le_left _ _)
  have hbtime : tn + sb < Tnn := hbT
  have hatime : tn + sa < Tnn := haT
  have hbval : E.1 (tn + sb) = g ub := extendLocal_apply_of_le hbtime.le g
  have haval : E.1 (tn + sa) = g ua := extendLocal_apply_of_le hatime.le g
  have htval : E.1 tn = g t := extendLocal_apply_of_le htnT.le g
  refine ⟨⟨ub, lt_add_of_pos_right _ hb0, ?_, ?_⟩,
    ⟨ua, lt_add_of_pos_right _ ha0, ?_, ?_⟩⟩
  · change (t : ℝ) + (sb : ℝ) < (t : ℝ) + ε
    linarith
  · rw [← hbval, ← htval]
    exact hbbelow
  · change (t : ℝ) + (sa : ℝ) < (t : ℝ) + ε
    linarith
  · rw [← haval, ← htval]
    exact haabove

/-- Regularity on a compact horizon: almost surely, `0` is regular for both half-lines. -/
theorem IsStableLevyLaw.ae_regular_at_zero {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ ε : ℝ, 0 < ε →
        (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f s < f ⟨0, le_rfl, hT.le⟩) ∧
        (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f ⟨0, le_rfl, hT.le⟩ < f s) := by
  let Tnn : ℝ≥0 := ⟨T, hT.le⟩
  let τ : DLoc → ℝ≥0∞ := fun _ => 0
  have hτ : IsStoppingTime DLoc.filtration τ := isStoppingTime_const _ 0
  let A : DLoc → Prop := fun f => DLoc.RegularBelowAtZero (DLoc.shiftAt τ f) ∧
    DLoc.RegularAboveAtZero (DLoc.shiftAt τ f)
  let B : D (Tnn : ℝ) ℝ → Prop := fun g => A (extendLocal Tnn g)
  have hAmeas : MeasurableSet {f | A f} := DLoc.measurable_shiftAt hτ
    (DLoc.measurableSet_regularBelowAtZero.inter DLoc.measurableSet_regularAboveAtZero)
  have hBmeas : MeasurableSet {g | B g} := hAmeas.preimage (measurable_extendLocal Tnn)
  have hpre (f : DLoc) : B (DLoc.restrict Tnn f) ↔ A f :=
    regular_shift_extendLocal (T := Tnn) (t := 0) (by exact hT) f rfl rfl
  have hmapped : ∀ᵐ g ∂((stableLocalLaw θ : Measure DLoc).map (DLoc.restrict Tnn)), B g := by
    apply (ae_map_iff (DLoc.measurable_restrict Tnn).aemeasurable hBmeas).mpr
    filter_upwards [ae_regular_both_shiftAt_stableLocalLaw hθ hτ] with f hf
    exact (hpre f).mpr (hf (WithTop.coe_lt_top _))
  rw [map_restrict_stableLocalLaw hθ (T := Tnn) (by exact hT)] at hmapped
  rw [hP.unique hθ hT (isStableLevyLaw_stableProcessLaw hθ hT)]
  filter_upwards [hmapped] with g hg
  change DLoc.RegularBelowAtZero (DLoc.shiftAt τ (extendLocal Tnn g)) ∧
    DLoc.RegularAboveAtZero (DLoc.shiftAt τ (extendLocal Tnn g)) at hg
  have hfin : τ (extendLocal Tnn g) < ⊤ := WithTop.coe_lt_top _
  simp only [DLoc.RegularBelowAtZero, DLoc.RegularAboveAtZero,
    DLoc.eval_shiftAt _ _ hfin, τ, ENNReal.toNNReal_zero, zero_add, sub_neg, sub_pos] at hg
  intro ε hε
  let δ : ℝ := min ε T
  have hδ : 0 < δ := lt_min hε hT
  let δnn : ℝ≥0 := ⟨δ, hδ.le⟩
  obtain ⟨sb, hb0, hbδ, hbbelow⟩ := hg.1 δnn hδ
  obtain ⟨sa, ha0, haδ, haabove⟩ := hg.2 δnn hδ
  have hbδR : (sb : ℝ) < δ := hbδ
  have haδR : (sa : ℝ) < δ := haδ
  have hbT : sb < Tnn := by
    change (sb : ℝ) < T
    exact hbδR.trans_le (min_le_right _ _)
  have haT : sa < Tnn := by
    change (sa : ℝ) < T
    exact haδR.trans_le (min_le_right _ _)
  let ub : Set.Icc (0 : ℝ) T := ⟨sb, sb.2, hbT.le⟩
  let ua : Set.Icc (0 : ℝ) T := ⟨sa, sa.2, haT.le⟩
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  have hbval : (extendLocal Tnn g).1 sb = g ub := extendLocal_apply_of_le hbT.le g
  have haval : (extendLocal Tnn g).1 sa = g ua := extendLocal_apply_of_le haT.le g
  have hzval : (extendLocal Tnn g).1 0 = g z := extendLocal_apply_of_le (T := Tnn) (u := 0) Tnn.2 g
  refine ⟨⟨ub, hb0, hbδR.trans_le (min_le_left _ _), ?_⟩,
    ⟨ua, ha0, haδR.trans_le (min_le_left _ _), ?_⟩⟩
  · rw [← hbval, ← hzval]
    exact hbbelow
  · rw [← haval, ← hzval]
    exact haabove

/-- Deterministic: a path is continuous at `t` as soon as `f t = leftLim f t` (right-continuity is
automatic; at `t = 0` the left limit is `f 0`). -/
theorem continuousAt_of_eq_leftLim {T : ℝ} (f : D T ℝ) {t : Set.Icc (0 : ℝ) T}
    (h : f t = Function.leftLim f t) : ContinuousAt f t := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · change Tendsto f (𝓝[<] t) (𝓝 (f t))
    simpa only [← h] using (isCadlag f).tendsto_nhdsLT_leftLim t
  · exact (isCadlag f).isRightContinuous t

private theorem tendsto_leftLim_nhdsGT_min {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {g : α → ℝ} {a : α} (h : Tendsto g (𝓝[>] a) (𝓝 (g a))) :
    Tendsto (Function.leftLim g) (𝓝[>] a) (𝓝 (g a)) := by
  apply (closed_nhds_basis (g a)).tendsto_right_iff.2
  rintro S ⟨hS, hclosed⟩
  rcases eq_or_neBot (𝓝[>] a) with hbot | hne
  · simp [hbot]
  obtain ⟨b, hb⟩ : (Set.Ioi a).Nonempty :=
    Filter.nonempty_of_mem (self_mem_nhdsWithin : Set.Ioi a ∈ 𝓝[>] a)
  obtain ⟨c, hac, hc⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb).mp (h.eventually hS)
  filter_upwards [Ioo_mem_nhdsGT hac] with x hx
  apply hclosed.mem_of_mapClusterPt (mapClusterPt_leftLim g x)
  filter_upwards [Ioo_mem_nhdsLE_of_mem hx] with y hy using hc hy

private theorem leftLim_reverseIncrements_min {T : ℝ} (hT : 0 < T) (f : D T ℝ)
    (t : Set.Icc (0 : ℝ) T) (ht : 0 < (t : ℝ)) :
    Function.leftLim (reverseIncrements hT.le f) t =
      f ⟨T, hT.le, le_rfl⟩ - f ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩ := by
  let r : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) T := fun u =>
    ⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩
  have hr (u : Set.Icc (0 : ℝ) T) : Tendsto r (𝓝 u) (𝓝 (r u)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [r] using tendsto_const_nhds.sub continuous_subtype_val.continuousAt
  have hrev : Tendsto r (𝓝[<] t) (𝓝[>] r t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hr t).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    apply Subtype.coe_lt_coe.mpr
    change T - (v : ℝ) > T - (t : ℝ)
    exact sub_lt_sub_left hv T
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  have hz : z < t := ht
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto
  change Tendsto (fun u => f ⟨T, hT.le, le_rfl⟩ - Function.leftLim f (r u))
    (𝓝[<] t) (𝓝 (f ⟨T, hT.le, le_rfl⟩ - f (r t)))
  exact tendsto_const_nhds.sub
    ((tendsto_leftLim_nhdsGT_min ((isCadlag f).isRightContinuous (r t)).tendsto).comp hrev)

/-- Deterministic reversal step. If `0 < t < T` is a generalized minimizer at which `f` jumps up
(`leftLim f t < f t`), then the reversed path `reverseIncrements f` attains its global maximum at
`T - t` and jumps up there: its left limit at `T - t` is `f T - f t`, strictly below the maximum
value `f T - leftLim f t`. -/
theorem reverseIncrements_max_at_upward_jump {T : ℝ} (hT : 0 < T) (f : D T ℝ)
    {t : Set.Icc (0 : ℝ) T} (ht0 : 0 < (t : ℝ)) (htT : (t : ℝ) < T)
    (hup : Function.leftLim f t < f t) (hg : IsGenMinimizer f t) :
    (∀ s : Set.Icc (0 : ℝ) T,
        reverseIncrements hT.le f s ≤
          reverseIncrements hT.le f ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩) ∧
      Function.leftLim (reverseIncrements hT.le f)
        ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩ <
        reverseIncrements hT.le f ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩ := by
  let u : Set.Icc (0 : ℝ) T := ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩
  have hu0 : 0 < (u : ℝ) := by dsimp [u]; linarith
  have hru : (⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩ : Set.Icc (0 : ℝ) T) = t := by
    apply Subtype.ext
    dsimp [u]
    ring
  have hmin : Function.leftLim f t = ⨅ s, f s := by
    have hg' : min (Function.leftLim f t) (f t) = ⨅ s, f s := hg
    rw [min_eq_left hup.le] at hg'
    exact hg'
  have hleft (s : Set.Icc (0 : ℝ) T) : Function.leftLim f t ≤
      Function.leftLim f ⟨T - s, by linarith [s.2.2], by linarith [s.2.1]⟩ := by
    rw [hmin]
    exact (iInf_le_genVal f _).trans (min_le_left _ _)
  have hbound (s : Set.Icc (0 : ℝ) T) :
      reverseIncrements hT.le f s ≤ reverseIncrements hT.le f u := by
    rw [reverseIncrements_apply, reverseIncrements_apply, hru]
    have hs := hleft s
    linarith
  have hjump : Function.leftLim (reverseIncrements hT.le f) u < reverseIncrements hT.le f u := by
    rw [leftLim_reverseIncrements_min hT f u hu0, reverseIncrements_apply, hru]
    linarith
  simpa only [u] using And.intro hbound hjump

/-- Almost surely no generalized minimizer is a jump time (upward jumps via reversal of increments,
downward jumps via regularity after jumps; the terminal time is not a jump time a.s.). -/
theorem IsStableLevyLaw.ae_not_isGenMinimizer_of_jump {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ t : Set.Icc (0 : ℝ) T, f t ≠ Function.leftLim f t → ¬ IsGenMinimizer f t := by
  let top : Set.Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
  let Q : D T ℝ → Prop := fun f => ∀ t : Set.Icc (0 : ℝ) T, (t : ℝ) < T →
    f t ≠ Function.leftLim f t → ∀ ε : ℝ, 0 < ε →
      (∃ s : Set.Icc (0 : ℝ) T, (t : ℝ) < s ∧ (s : ℝ) < t + ε ∧ f s < f t) ∧
      (∃ s : Set.Icc (0 : ℝ) T, (t : ℝ) < s ∧ (s : ℝ) < t + ε ∧ f t < f s)
  have hreg : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), Q f :=
    hP.ae_regular_after_jumps hθ hT
  have hregrev : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), Q (reverseIncrements hT.le f) := by
    have hmap : (P : Measure (D T ℝ)).map (reverseIncrements hT.le) =
        (P : Measure (D T ℝ)) := congrArg
      (fun μ : ProbabilityMeasure (D T ℝ) => (μ : Measure (D T ℝ)))
      (hP.map_reverseIncrements hθ hT)
    have hmapped : ∀ᵐ f ∂((P : Measure (D T ℝ)).map (reverseIncrements hT.le)), Q f := by
      rw [hmap]
      exact hreg
    exact ae_of_ae_map (measurable_reverseIncrements hT.le).aemeasurable hmapped
  filter_upwards [hreg, hregrev, hP.ae_continuousAt hθ hT top] with f hreg hregrev hcont
  intro t hjump hg
  by_cases htT : (t : ℝ) < T
  · have ht0 : 0 < (t : ℝ) := by
      apply lt_of_le_of_ne t.2.1
      intro ht
      apply hjump
      have hbot : IsBot t := by
        intro u
        change (t : ℝ) ≤ (u : ℝ)
        rw [← ht]
        exact u.2.1
      exact (leftLim_eq_of_isBot hbot).symm
    rcases lt_or_gt_of_ne hjump with hdown | hup
    · have hmin : f t = ⨅ s, f s := by
        have hg' : min (Function.leftLim f t) (f t) = ⨅ s, f s := hg
        rw [min_eq_right hdown.le] at hg'
        exact hg'
      obtain ⟨s, -, -, hs⟩ := (hreg t htT hjump (T - (t : ℝ)) (sub_pos.mpr htT)).1
      have hle : (⨅ u, f u) ≤ f s := ciInf_le (isBounded_range f).bddBelow s
      rw [← hmin] at hle
      linarith
    · let u : Set.Icc (0 : ℝ) T := ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩
      obtain ⟨hmax, hRjump⟩ := reverseIncrements_max_at_upward_jump hT f ht0 htT hup hg
      have huT : (u : ℝ) < T := by dsimp [u]; linarith
      have hRneq : reverseIncrements hT.le f u ≠
          Function.leftLim (reverseIncrements hT.le f) u := ne_of_gt hRjump
      obtain ⟨s, -, -, hs⟩ :=
        (hregrev u huT hRneq (T - (u : ℝ)) (sub_pos.mpr huT)).2
      have hmaxu (v : Set.Icc (0 : ℝ) T) : reverseIncrements hT.le f v ≤
          reverseIncrements hT.le f u := by
        simpa only [u] using hmax v
      exact (not_lt_of_ge (hmaxu s)) hs
  · have ht : (t : ℝ) = T := le_antisymm t.2.2 (le_of_not_gt htT)
    have htop : t = top := Subtype.ext ht
    apply hjump
    rw [htop]
    exact hcont.continuousWithinAt.leftLim_eq.symm

/-- Consequence: every generalized minimizer is a continuity point. -/
theorem IsStableLevyLaw.ae_continuousAt_of_isGenMinimizer {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ g : Set.Icc (0 : ℝ) T, IsGenMinimizer f g → ContinuousAt f g := by
  filter_upwards [hP.ae_not_isGenMinimizer_of_jump hθ hT] with f hf
  intro g hg
  apply continuousAt_of_eq_leftLim
  by_contra hne
  exact hf g hne hg

/-- The minimizer is not at `0`: the path starts at `0` and takes negative values immediately. -/
theorem IsStableLevyLaw.ae_not_isGenMinimizer_zero {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ¬ IsGenMinimizer f ⟨0, le_rfl, hT.le⟩ := by
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  change ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ¬ IsGenMinimizer f z
  filter_upwards [hP.ae_regular_at_zero hθ hT, hP.start hT.le] with f hreg hstart
  intro hg
  have hbot : IsBot z := by
    intro u
    change (0 : ℝ) ≤ (u : ℝ)
    exact u.2.1
  have hleft : Function.leftLim f z = f z := leftLim_eq_of_isBot hbot
  have hgen : genVal f z = 0 := by
    unfold genVal
    rw [hleft, hstart, min_self]
  have hinf : (⨅ t, f t) = 0 := hg.symm.trans hgen
  obtain ⟨s, -, -, hs⟩ := (hreg 1 zero_lt_one).1
  have hle : (⨅ t, f t) ≤ f s := ciInf_le (isBounded_range f).bddBelow s
  rw [hinf] at hle
  change f s < f z at hs
  rw [hstart] at hs
  linarith

/-- The minimizer is not at `T`: there is no jump at `T` (`ae_continuousAt`), and the reversed path
(same law) is positive immediately after `0`, whereas a minimum at `T` would force it to be
`≤ 0`. -/
theorem IsStableLevyLaw.ae_not_isGenMinimizer_top {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ¬ IsGenMinimizer f ⟨T, hT.le, le_rfl⟩ := by
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  let top : Set.Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
  let Q : D T ℝ → Prop := fun f => ∀ ε : ℝ, 0 < ε →
    (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f s < f z) ∧
    (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f z < f s)
  have hreg : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), Q f :=
    hP.ae_regular_at_zero hθ hT
  have hregrev : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), Q (reverseIncrements hT.le f) := by
    have hmap : (P : Measure (D T ℝ)).map (reverseIncrements hT.le) =
        (P : Measure (D T ℝ)) := congrArg
      (fun μ : ProbabilityMeasure (D T ℝ) => (μ : Measure (D T ℝ)))
      (hP.map_reverseIncrements hθ hT)
    have hmapped : ∀ᵐ f ∂((P : Measure (D T ℝ)).map (reverseIncrements hT.le)), Q f := by
      rw [hmap]
      exact hreg
    exact ae_of_ae_map (measurable_reverseIncrements hT.le).aemeasurable hmapped
  change ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ¬ IsGenMinimizer f top
  filter_upwards [hregrev, hP.ae_continuousAt hθ hT top] with f hreg hcont
  intro hg
  have hleft : Function.leftLim f top = f top := hcont.continuousWithinAt.leftLim_eq
  have hmin : f top = ⨅ s, f s := by
    have hg' : min (Function.leftLim f top) (f top) = ⨅ s, f s := hg
    rw [hleft, min_self] at hg'
    exact hg'
  have hRzero : reverseIncrements hT.le f z = 0 := by
    rw [reverseIncrements_apply]
    have hrt : (⟨T - z, by linarith [z.2.2], by linarith [z.2.1]⟩ : Set.Icc (0 : ℝ) T) =
        top := by
      apply Subtype.ext
      change T - (0 : ℝ) = T
      ring
    rw [hrt, hleft, sub_self]
  obtain ⟨s, -, -, hs⟩ := (hreg 1 zero_lt_one).2
  have hleft_le : f top ≤ Function.leftLim f ⟨T - s, by linarith [s.2.2], by linarith [s.2.1]⟩ := by
    rw [hmin]
    exact (iInf_le_genVal f _).trans (min_le_left _ _)
  have hRle : reverseIncrements hT.le f s ≤ 0 := by
    rw [reverseIncrements_apply]
    linarith
  rw [hRzero] at hs
  linarith

/-- **Unique continuous interior minimum.** For fixed `T > 0`, the minimum, as a value or a left
limit, has exactly one minimizing time, this time is interior, and the path is continuous there. -/
theorem IsStableLevyLaw.ae_unique_continuous_minimum {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∃ g : Set.Icc (0 : ℝ) T,
        0 < (g : ℝ) ∧ (g : ℝ) < T ∧ ContinuousAt f g ∧
        min (Function.leftLim f g) (f g) = ⨅ t, f t ∧
        ∀ s : Set.Icc (0 : ℝ) T,
          min (Function.leftLim f s) (f s) = (⨅ t, f t) → s = g := by
  filter_upwards [hP.ae_existsUnique_generalizedMinimizer hθ hT,
    hP.ae_continuousAt_of_isGenMinimizer hθ hT, hP.ae_not_isGenMinimizer_zero hθ hT,
    hP.ae_not_isGenMinimizer_top hθ hT] with f hunique hcont hzero htop
  obtain ⟨g, hg, hgu⟩ := hunique
  have hg0 : (g : ℝ) ≠ 0 := by
    intro h
    apply hzero
    have hz : g = ⟨0, le_rfl, hT.le⟩ := Subtype.ext h
    rwa [← hz]
  have hgT : (g : ℝ) ≠ T := by
    intro h
    apply htop
    have ht : g = ⟨T, hT.le, le_rfl⟩ := Subtype.ext h
    rwa [← ht]
  exact ⟨g, lt_of_le_of_ne g.2.1 (Ne.symm hg0), lt_of_le_of_ne g.2.2 hgT,
    hcont g hg, hg, fun s hs => hgu s hs⟩

/-- The same for the canonical stable process law. -/
theorem stableProcessLaw_ae_unique_continuous_minimum {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      ∃ g : Set.Icc (0 : ℝ) T,
        0 < (g : ℝ) ∧ (g : ℝ) < T ∧ ContinuousAt f g ∧
        min (Function.leftLim f g) (f g) = ⨅ t, f t ∧
        ∀ s : Set.Icc (0 : ℝ) T,
          min (Function.leftLim f s) (f s) = (⨅ t, f t) → s = g :=
  (isStableLevyLaw_stableProcessLaw hθ hT).ae_unique_continuous_minimum hθ hT

/-- Transfer to any measure absolutely continuous with respect to a stable Lévy law (for instance
bridge prefixes). -/
theorem ae_unique_continuous_minimum_of_absolutelyContinuous {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {μ : Measure (D T ℝ)} (hμ : μ ≪ (P : Measure (D T ℝ))) :
    ∀ᵐ f : D T ℝ ∂μ,
      ∃ g : Set.Icc (0 : ℝ) T,
        0 < (g : ℝ) ∧ (g : ℝ) < T ∧ ContinuousAt f g ∧
        min (Function.leftLim f g) (f g) = ⨅ t, f t ∧
        ∀ s : Set.Icc (0 : ℝ) T,
          min (Function.leftLim f s) (f s) = (⨅ t, f t) → s = g :=
  hμ.ae_le (hP.ae_unique_continuous_minimum hθ hT)

end BGW.StableTrees
