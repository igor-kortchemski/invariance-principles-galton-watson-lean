/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTime
public import BGW.Skorokhod.MeasurableExtrema
public import BGW.StableTrees.StableStrongMarkov
public import BGW.StableTrees.StableLocalLaw

/-!
# Reflection at the running supremum

The measurable reflected family, occupation continuity, contact geometry, and transfer of the
stable Markov property. Deterministic restart formulas hold for every path; probabilistic
statements use spectral positivity or the sealed shift laws only where needed.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters III, IV and VI.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapters 3 and 6.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Reflected-at-supremum process started from `x ≥ 0`**: `t ↦ max x S_t - X_t`. -/
noncomputable def supReflectedFrom (x : ℝ≥0) (f : DLoc) (t : ℝ≥0) : ℝ :=
  max (x : ℝ) (supRunning f t) - f.1 t

/-- Right continuity of the running supremum of a càdlàg path. -/
private theorem isRightContinuous_supRunning (f : DLoc) :
    IsRightContinuous (supRunning f) := by
  intro t
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ha.trans_le (monotone_supRunning f hs.le)
  · intro b hb
    obtain ⟨b', hbb', hb'⟩ := exists_between hb
    have hf : f.1 t < b' := (eval_le_supRunning f le_rfl).trans_lt hbb'
    have he : {u : ℝ≥0 | f.1 u < b'} ∈ 𝓝[Set.Ioi t] t :=
      (f.2.isRightContinuous t).eventually (isOpen_Iio.mem_nhds hf)
    obtain ⟨d, htd, hd⟩ := (nhdsGT_basis t).mem_iff.mp he
    filter_upwards [Ioo_mem_nhdsGT htd] with s hs
    apply lt_of_le_of_lt _ hb'
    apply supRunning_le
    intro u
    by_cases hut : u ≤ t
    · exact (eval_le_supRunning f hut).trans hbb'.le
    · exact (hd ⟨lt_of_not_ge hut, lt_of_le_of_lt u.2 hs.2⟩).le

/-- The running supremum is càdlàg. -/
theorem isCadlag_supRunning (f : DLoc) : IsCadlag (supRunning f) where
  isRightContinuous := isRightContinuous_supRunning f
  tendsto_nhdsLT t := ⟨_, (monotone_supRunning f).tendsto_nhdsLT t⟩

/-- Càdlàg-ness of the reflected path for every càdlàg `f` and every start `x`. -/
theorem isCadlag_supReflectedFrom (x : ℝ≥0) (f : DLoc) :
    IsCadlag (supReflectedFrom x f) := by
  have hm : IsCadlag (fun t => max (x : ℝ) (supRunning f t)) := by
    simpa only [Function.comp_def, id_eq] using
      (isCadlag_supRunning f).continuous_comp (continuous_const.max continuous_id)
  exact hm.sub f.2

/-- The reflected path as a total `DLoc`-valued map (no junk case). -/
noncomputable def supReflectedFromLoc (x : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨supReflectedFrom x f, isCadlag_supReflectedFrom x f⟩

/-- The contact set `{t | S_t = X_t}` (equivalently `{R = 0}`, `R ≥ 0`). -/
def supContact (f : DLoc) : Set ℝ≥0 := {t | supReflected f t = 0}

/-- Started from `0` and with `f 0 = 0`, the family reduces to `supReflected`. -/
theorem supReflectedFrom_zero_apply {f : DLoc} (h0 : f.1 0 = 0) (t : ℝ≥0) :
    supReflectedFrom 0 f t = supReflected f t := by
  simp only [supReflectedFrom, NNReal.coe_zero, supReflected]
  rw [max_eq_right]
  rw [← h0, ← supRunning_zero f]
  exact monotone_supRunning f bot_le

/-- Restart formula for the running supremum. -/
private theorem supRunning_add_shift (f : DLoc) (s u : ℝ≥0) :
    supRunning f (s + u) = max (supRunning f s)
      (f.1 s + supRunning (DLoc.shift s f) u) := by
  apply le_antisymm
  · apply supRunning_le
    intro v
    by_cases hvs : (v : ℝ≥0) ≤ s
    · exact (eval_le_supRunning f hvs).trans (le_max_left _ _)
    · have hv : s ≤ (v : ℝ≥0) := le_of_not_ge hvs
      have hw : (v : ℝ≥0) - s ≤ u := by
        rw [← NNReal.coe_le_coe, NNReal.coe_sub hv]
        have hv' : (v : ℝ) ≤ ((s + u : ℝ≥0) : ℝ) := by exact_mod_cast v.2
        rw [NNReal.coe_add] at hv'
        linarith
      have h := eval_le_supRunning (DLoc.shift s f) hw
      change f.1 (s + ((v : ℝ≥0) - s)) - f.1 s ≤ _ at h
      rw [add_tsub_cancel_of_le hv] at h
      exact (by linarith : f.1 v ≤ f.1 s + supRunning (DLoc.shift s f) u) |>.trans
        (le_max_right _ _)
  · apply max_le
    · exact monotone_supRunning f (by simp)
    · have h : supRunning (DLoc.shift s f) u ≤ supRunning f (s + u) - f.1 s := by
        apply supRunning_le
        intro v
        have he := eval_le_supRunning f (show s + (v : ℝ≥0) ≤ s + u from add_le_add_right v.2 s)
        change f.1 (s + (v : ℝ≥0)) - f.1 s ≤ _
        linarith
      linarith

/-- The reflection is nonnegative, and `≥ x - X_t`. -/
theorem supReflectedFrom_nonneg (x : ℝ≥0) (f : DLoc) (t : ℝ≥0) : 0 ≤ supReflectedFrom x f t := by
  exact sub_nonneg.mpr ((eval_le_supRunning f le_rfl).trans (le_max_right _ _))

/-- **Deterministic restart (everywhere, no hypothesis).** The reflected path at time `s + u` is the
reflected path of the centered shifted path, started from the value `R^x_s`. -/
theorem supReflectedFrom_restart (x : ℝ≥0) (f : DLoc) (s u : ℝ≥0) :
    supReflectedFrom x f (s + u) =
      supReflectedFrom (supReflectedFrom x f s).toNNReal (DLoc.shift s f) u := by
  have hy : ((supReflectedFrom x f s).toNNReal : ℝ) = supReflectedFrom x f s :=
    Real.coe_toNNReal _ (supReflectedFrom_nonneg x f s)
  unfold supReflectedFrom
  change ((max (x : ℝ) (supRunning f s) - f.1 s).toNNReal : ℝ) = _ at hy
  rw [supRunning_add_shift, hy]
  change max (x : ℝ) (max (supRunning f s)
      (f.1 s + supRunning (DLoc.shift s f) u)) - f.1 (s + u) =
    max (max (x : ℝ) (supRunning f s) - f.1 s)
      (supRunning (DLoc.shift s f) u) - (f.1 (s + u) - f.1 s)
  calc
    _ = max (max (x : ℝ) (supRunning f s))
        (f.1 s + supRunning (DLoc.shift s f) u) - f.1 s -
        (f.1 (s + u) - f.1 s) := by rw [max_assoc]; ring
    _ = max (max (x : ℝ) (supRunning f s) - f.1 s)
        ((f.1 s + supRunning (DLoc.shift s f) u) - f.1 s) -
        (f.1 (s + u) - f.1 s) := by rw [max_sub_sub_right]
    _ = _ := by congr 2; ring

/-- **Restart at a random time** (on `{τ f < ⊤}`; junk `shift 0` elsewhere). -/
theorem supReflectedFrom_restart_shiftAt (x : ℝ≥0) (τ : DLoc → ℝ≥0∞) {f : DLoc} (hτ : τ f < ⊤)
    (u : ℝ≥0) :
    supReflectedFrom x f ((τ f).toNNReal + u) =
      supReflectedFrom (supReflectedFrom x f (τ f).toNNReal).toNNReal (DLoc.shiftAt τ f) u := by
  -- `hτ` is kept in the statement for the strong Markov interface; the identity holds for
  -- every path because `DLoc.shiftAt` reads `τ f` through `toNNReal`.
  have _hτ := hτ
  exact supReflectedFrom_restart x f (τ f).toNNReal u

/-- **Joint measurability** of `(x, f, t) ↦ R^x_t(f)`. -/
theorem measurable_supReflectedFrom_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc × ℝ≥0 => supReflectedFrom p.1 p.2.1 p.2.2) := by
  apply Measurable.sub
  · have hx : Measurable (fun p : ℝ≥0 × DLoc × ℝ≥0 => (p.1 : ℝ)) := by fun_prop
    apply hx.max
    exact measurable_supRunning_uncurry.comp
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  · exact DLoc.measurable_eval₂.comp measurable_snd

/-- Joint measurability of the `DLoc`-valued reflection in `(x, f)`. -/
theorem measurable_supReflectedFromLoc :
    Measurable (fun p : ℝ≥0 × DLoc => supReflectedFromLoc p.1 p.2) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun p : ℝ≥0 × DLoc => supReflectedFromLoc p.1 p.2)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance) ≤ _
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, iSup_le_iff,
    Function.comp_def]
  intro t
  exact (measurable_supReflectedFrom_uncurry.comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).comap_le

/-- **No positive jumps** (under spectral positivity of `X`): `R t ≤ leftLim R t`, every `x ≥ 0`. -/
theorem supReflectedFrom_le_leftLim {f : DLoc} (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s)
    (x : ℝ≥0) (t : ℝ≥0) :
    supReflectedFrom x f t ≤ Function.leftLim (supReflectedFrom x f) t := by
  let q : ℝ≥0 → ℝ := fun u => max (x : ℝ) (supRunning f u)
  have hq : IsCadlag q := by
    simpa only [q, Function.comp_def, id_eq] using
      (isCadlag_supRunning f).continuous_comp (continuous_const.max continuous_id)
  have hmono : Monotone q := fun _ _ h => max_le_max_left _ (monotone_supRunning f h)
  by_cases ht : t = 0
  · subst t
    rw [leftLim_eq_of_isBot isBot_zero]
  have ht0 : 0 < t := pos_iff_ne_zero.mpr ht
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  have heq : Function.leftLim (supReflectedFrom x f) t =
      Function.leftLim q t - Function.leftLim f.1 t := by
    apply leftLim_eq_of_tendsto
    exact (hq.tendsto_nhdsLT_leftLim t).sub (f.2.tendsto_nhdsLT_leftLim t)
  have hqt : q t ≤ max (Function.leftLim q t) (f.1 t) := by
    apply max_le
    · have hx0 : (x : ℝ) ≤ q 0 := le_max_left _ _
      exact hx0.trans ((hmono.le_leftLim ht0).trans (le_max_left _ _))
    · apply supRunning_le
      intro u
      by_cases hut : (u : ℝ≥0) = t
      · exact le_of_eq_of_le (congrArg f.1 hut) (le_max_right _ _)
      · exact ((eval_le_supRunning f le_rfl).trans
          (le_max_right (x : ℝ) (supRunning f (u : ℝ≥0)))).trans
          ((hmono.le_leftLim (lt_of_le_of_ne u.2 hut)).trans (le_max_left _ _))
  rw [heq]
  have hleftf := hf t
  rcases max_cases (Function.leftLim q t) (f.1 t) with hm | hm
  · rw [hm.1] at hqt
    change q t - f.1 t ≤ _
    linarith
  · rw [hm.1] at hqt
    have hleftfq : Function.leftLim f.1 t ≤ Function.leftLim q t :=
      le_of_tendsto_of_tendsto (f.2.tendsto_nhdsLT_leftLim t)
        (hq.tendsto_nhdsLT_leftLim t) (Filter.Eventually.of_forall fun u =>
          (eval_le_supRunning f le_rfl).trans (le_max_right (x : ℝ) (supRunning f u)))
    change q t - f.1 t ≤ _
    have hqtf : q t - f.1 t ≤ 0 := sub_nonpos.mpr hqt
    have hqleft : 0 ≤ Function.leftLim q t - Function.leftLim f.1 t := sub_nonneg.mpr hleftfq
    exact hqtf.trans hqleft

/-- Almost-sure form for the stable law, simultaneously in `x` and `t`. -/
theorem ae_supReflectedFrom_le_leftLim {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc), ∀ (x t : ℝ≥0),
      supReflectedFrom x f t ≤ Function.leftLim (supReflectedFrom x f) t := by
  filter_upwards [ae_leftLim_le_stableLocalLaw hθ] with f hf
  exact supReflectedFrom_le_leftLim hf

/-- Time set occupied below a cutoff before a fixed horizon. -/
private def occupationSet (ε : ℝ) (f : DLoc) (t : ℝ≥0) : Set ℝ :=
  {u | 0 ≤ u ∧ u ≤ (t : ℝ) ∧ supReflected f u.toNNReal < ε}

private theorem measurableSet_occupationSet (ε : ℝ) (f : DLoc) (t : ℝ≥0) :
    MeasurableSet (occupationSet ε f t) := by
  apply MeasurableSet.inter (measurableSet_le measurable_const measurable_id)
  apply MeasurableSet.inter (measurableSet_le measurable_id measurable_const)
  exact measurableSet_lt (measurable_supReflected_uncurry.comp
    (continuous_real_toNNReal.measurable.prodMk measurable_const)) measurable_const

private theorem occupationSet_mono (ε : ℝ) (f : DLoc) {s t : ℝ≥0} (hst : s ≤ t) :
    occupationSet ε f s ⊆ occupationSet ε f t := by
  intro u hu
  exact ⟨hu.1, hu.2.1.trans (by exact_mod_cast hst), hu.2.2⟩

private theorem occupationSet_ne_top (ε : ℝ) (f : DLoc) (t : ℝ≥0) :
    volume (occupationSet ε f t) ≠ ⊤ := supOccupation_volume_ne_top ε f t

/-- Increment bounds: monotone and `ε⁻¹`-Lipschitz increments. -/
theorem supOccupation_sub_mem {ε : ℝ} (hε : 0 < ε) (f : DLoc) {s t : ℝ≥0} (hst : s ≤ t) :
    0 ≤ supOccupation ε f t - supOccupation ε f s ∧
      supOccupation ε f t - supOccupation ε f s ≤ ε⁻¹ * ((t : ℝ) - s) := by
  have hnonneg := sub_nonneg.mpr (monotone_supOccupation hε.le f hst)
  refine ⟨hnonneg, ?_⟩
  rw [supOccupation, supOccupation, ← mul_sub]
  change ε⁻¹ * (volume.real (occupationSet ε f t) - volume.real (occupationSet ε f s)) ≤ _
  rw [← measureReal_sdiff (occupationSet_mono ε f hst) (measurableSet_occupationSet ε f s)
    (occupationSet_ne_top ε f t)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hε.le)
  calc
    volume.real (occupationSet ε f t \ occupationSet ε f s) ≤ volume.real (Set.Icc (s : ℝ) t) := by
      apply measureReal_mono
      · intro u hu
        have hut : ¬u ≤ (s : ℝ) := by
          intro hus
          exact hu.2 ⟨hu.1.1, hus, hu.1.2.2⟩
        exact ⟨le_of_not_ge hut, hu.1.2.1⟩
      · exact measure_Icc_lt_top.ne
    _ = (t : ℝ) - s := Real.volume_real_Icc_of_le (by exact_mod_cast hst)

/-- `t ↦ supOccupation ε f t` is `ε⁻¹`-Lipschitz. -/
theorem lipschitzWith_supOccupation {ε : ℝ} (hε : 0 < ε) (f : DLoc) :
    LipschitzWith (Real.toNNReal ε⁻¹) (fun t : ℝ≥0 => supOccupation ε f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  wlog hst : s ≤ t generalizing s t with H
  · have h := H t s (le_of_not_ge hst)
    simpa only [dist_comm] using h
  have hmono := monotone_supOccupation hε.le f hst
  have hdist : dist (supOccupation ε f s) (supOccupation ε f t) =
      supOccupation ε f t - supOccupation ε f s := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
  rw [hdist, NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hst)), neg_sub]
  simpa only [Real.coe_toNNReal _ (inv_nonneg.mpr hε.le)] using
    (supOccupation_sub_mem hε f hst).2

/-- Continuity (hence continuity and monotonicity together with `monotone_supOccupation`). -/
theorem continuous_supOccupation {ε : ℝ} (hε : 0 < ε) (f : DLoc) :
    Continuous (fun t : ℝ≥0 => supOccupation ε f t) :=
  (lipschitzWith_supOccupation hε f).continuous

/-- Reflection at the running supremum is càdlàg. -/
theorem isCadlag_supReflected (f : DLoc) : IsCadlag (supReflected f) :=
  (isCadlag_supRunning f).sub f.2

/-- Spectral positivity prevents positive jumps of the ordinary reflected path. -/
theorem supReflected_le_leftLim {f : DLoc} (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s)
    (t : ℝ≥0) : supReflected f t ≤ Function.leftLim (supReflected f) t := by
  by_cases ht : t = 0
  · subst t
    rw [leftLim_eq_of_isBot isBot_zero]
  have ht0 : 0 < t := pos_iff_ne_zero.mpr ht
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  have hmono := monotone_supRunning f
  have heq : Function.leftLim (supReflected f) t =
      Function.leftLim (supRunning f) t - Function.leftLim f.1 t := by
    apply leftLim_eq_of_tendsto
    exact ((isCadlag_supRunning f).tendsto_nhdsLT_leftLim t).sub
      (f.2.tendsto_nhdsLT_leftLim t)
  have hqt : supRunning f t ≤ max (Function.leftLim (supRunning f) t) (f.1 t) := by
    apply supRunning_le
    intro u
    by_cases hut : (u : ℝ≥0) = t
    · exact le_of_eq_of_le (congrArg f.1 hut) (le_max_right _ _)
    · exact (eval_le_supRunning f le_rfl).trans
        ((hmono.le_leftLim (lt_of_le_of_ne u.2 hut)).trans (le_max_left _ _))
  rw [heq]
  have hleftf := hf t
  rcases max_cases (Function.leftLim (supRunning f) t) (f.1 t) with hm | hm
  · rw [hm.1] at hqt
    dsimp [supReflected]
    linarith
  · rw [hm.1] at hqt
    have hleftfq : Function.leftLim f.1 t ≤ Function.leftLim (supRunning f) t :=
      le_of_tendsto_of_tendsto (f.2.tendsto_nhdsLT_leftLim t)
        ((isCadlag_supRunning f).tendsto_nhdsLT_leftLim t)
        (Filter.Eventually.of_forall fun u => eval_le_supRunning f le_rfl)
    change supRunning f t - f.1 t ≤ _
    have hqtf : supRunning f t - f.1 t ≤ 0 := sub_nonpos.mpr hqt
    have hqleft : 0 ≤ Function.leftLim (supRunning f) t - Function.leftLim f.1 t :=
      sub_nonneg.mpr hleftfq
    exact hqtf.trans hqleft

/-- Right-accumulation points of the contact set are contact times. -/
theorem supContact_rightClosed (f : DLoc) {t : ℝ≥0}
    (h : ∀ δ : ℝ≥0, 0 < δ → ∃ u ∈ supContact f, t < u ∧ u < t + δ) : t ∈ supContact f := by
  have hfreq : ∃ᶠ u in 𝓝[>] t, u ∈ supContact f := by
    rw [frequently_iff]
    intro U hU
    obtain ⟨v, htv, hv⟩ := (nhdsGT_basis t).mem_iff.mp hU
    obtain ⟨u, hu, htu, htuv⟩ := h (v - t) (tsub_pos_of_lt htv)
    have huv : u < v := htuv.trans_eq (add_tsub_cancel_of_le htv.le)
    exact ⟨u, hv ⟨htu, huv⟩, hu⟩
  have hlim : Tendsto (supReflected f) (𝓝[>] t) (𝓝 (supReflected f t)) :=
    (isCadlag_supReflected f).isRightContinuous t
  have hc : supReflected f t ∈ closure ({0} : Set ℝ) :=
    mem_closure_of_frequently_of_tendsto hfreq hlim
  change supReflected f t = 0
  simpa only [closure_singleton, mem_singleton_iff] using hc

/-- With no negative jumps of the path, its supremum-contact set is closed. -/
theorem isClosed_supContact {f : DLoc} (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s) :
    IsClosed (supContact f) := by
  apply isClosed_iff_frequently.mpr
  intro t ht
  rw [← nhdsWithin_univ] at ht
  rw [← Iic_union_Ioi, nhdsWithin_union, frequently_sup] at ht
  rcases ht with ht | ht
  · rw [← Iio_union_right, nhdsWithin_union, frequently_sup] at ht
    rcases ht with ht | ht
    · have hlim : Tendsto (supReflected f) (𝓝[<] t)
          (𝓝 (Function.leftLim (supReflected f) t)) :=
        (isCadlag_supReflected f).tendsto_nhdsLT_leftLim t
      have hc : Function.leftLim (supReflected f) t ∈ closure ({0} : Set ℝ) :=
        mem_closure_of_frequently_of_tendsto ht hlim
      have hzero : Function.leftLim (supReflected f) t = 0 := by simpa using hc
      apply le_antisymm _ (supReflected_nonneg f t)
      rw [← hzero]
      exact supReflected_le_leftLim hf t
    · simpa only [nhdsWithin_singleton, frequently_pure] using ht
  · apply supContact_rightClosed
    intro δ hδ
    have hmem : Set.Ioo t (t + δ) ∈ 𝓝[>] t := Ioo_mem_nhdsGT (lt_add_of_pos_right t hδ)
    obtain ⟨u, hu, hcontact⟩ := (ht.and_eventually hmem).exists
    exact ⟨u, hu, hcontact.1, hcontact.2⟩

/-- Contact occurs exactly when the path attains its running supremum. -/
theorem mem_supContact_iff {f : DLoc} {t : ℝ≥0} : t ∈ supContact f ↔ f.1 t = supRunning f t := by
  change supRunning f t - f.1 t = 0 ↔ _
  exact sub_eq_zero.trans eq_comm

/-- Every positive reflected value lies between consecutive contact times, with an infinite right
endpoint when there is no later contact. -/
theorem exists_excursionInterval_of_supReflected_pos {f : DLoc} (h0 : f.1 0 = 0)
    (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s) {t : ℝ≥0} (ht : 0 < supReflected f t) :
    ∃ (g : ℝ≥0) (d : ℝ≥0∞), g < t ∧ (t : ℝ≥0∞) < d ∧ supReflected f g = 0 ∧
      (∀ u : ℝ≥0, g < u → (u : ℝ≥0∞) < d → 0 < supReflected f u) ∧
      ∀ d' : ℝ≥0, d = d' → supReflected f d' = 0 := by
  -- `h0` is part of the stated interface (paths started at `0`); the argument below only uses
  -- closedness of the contact set.
  have _h0 := h0
  let C := supContact f
  have hC : IsClosed C := isClosed_supContact hf
  let A : Set ℝ≥0 := {u ∈ C | u ≤ t}
  let B : Set ℝ≥0 := {u ∈ C | t < u}
  have hA0 : A.Nonempty := by
    refine ⟨0, ?_, bot_le⟩
    exact supReflected_zero f
  have hCA : IsClosed A := hC.inter isClosed_Iic
  have hCB : IsClosed (C ∩ Set.Ici t) := hC.inter isClosed_Ici
  have hAbd : BddAbove A := bddAbove_Iic.mono (fun _ hu => hu.2)
  let g : ℝ≥0 := sSup A
  have hgA : g ∈ A := hCA.csSup_mem hA0 hAbd
  have htC : t ∉ C := ne_of_gt ht
  have hgt : g < t := lt_of_le_of_ne hgA.2 (fun h => htC (h ▸ hgA.1))
  by_cases hB0 : B.Nonempty
  · let d0 : ℝ≥0 := sInf B
    have hdcl : d0 ∈ closure B := csInf_mem_closure hB0 (⟨0, fun _ _ => bot_le⟩ : BddBelow B)
    have hdcl' : d0 ∈ C ∩ Set.Ici t := closure_minimal
      (fun u (hu : u ∈ B) => (⟨hu.1, hu.2.le⟩ : u ∈ C ∩ Set.Ici t)) hCB hdcl
    have htd0 : t < d0 := lt_of_le_of_ne hdcl'.2 (fun h => htC (h ▸ hdcl'.1))
    have hdB : d0 ∈ B := ⟨hdcl'.1, htd0⟩
    refine ⟨g, (d0 : ℝ≥0∞), hgt, by exact_mod_cast htd0, hgA.1, ?_, ?_⟩
    · intro u hgu hud
      apply lt_of_le_of_ne (supReflected_nonneg f u)
      intro hu
      have huC : u ∈ C := hu.symm
      by_cases hut : u ≤ t
      · exact (not_le_of_gt hgu) (le_csSup hAbd ⟨huC, hut⟩)
      · have huB : u ∈ B := ⟨huC, lt_of_not_ge hut⟩
        have hdu : d0 ≤ u := csInf_le (⟨0, fun _ _ => bot_le⟩ : BddBelow B) huB
        have : (d0 : ℝ≥0∞) ≤ (u : ℝ≥0∞) := by exact_mod_cast hdu
        exact (not_le_of_gt hud) this
    · intro d' hd'
      have heq : d' = d0 := by exact_mod_cast hd'.symm
      rw [heq]
      exact hdB.1
  · simp only [Set.not_nonempty_iff_eq_empty] at hB0
    refine ⟨g, ⊤, hgt, ENNReal.coe_lt_top, hgA.1, ?_, ?_⟩
    · intro u hgu _
      apply lt_of_le_of_ne (supReflected_nonneg f u)
      intro hu
      have huC : u ∈ C := hu.symm
      by_cases hut : u ≤ t
      · exact (not_le_of_gt hgu) (le_csSup hAbd ⟨huC, hut⟩)
      · have : u ∈ B := ⟨huC, lt_of_not_ge hut⟩
        rw [hB0] at this
        exact this
    · intro d' hd'
      exact (ENNReal.top_ne_coe hd').elim

/-- The running supremum depends only on the prefix of the path. -/
theorem supRunning_congr_prefix {f g : DLoc} {t : ℝ≥0} (h : ∀ u ≤ t, f.1 u = g.1 u) :
    supRunning f t = supRunning g t := by
  apply le_antisymm
  · apply supRunning_le
    intro u
    rw [h u.1 u.2]
    exact eval_le_supRunning g u.2
  · apply supRunning_le
    intro u
    rw [← h u.1 u.2]
    exact eval_le_supRunning f u.2

/-- Reflection at the supremum depends only on the prefix of the path. -/
theorem supReflectedFrom_congr_prefix (x : ℝ≥0) {f g : DLoc} {t : ℝ≥0}
    (h : ∀ u ≤ t, f.1 u = g.1 u) : supReflectedFrom x f t = supReflectedFrom x g t := by
  rw [supReflectedFrom, supReflectedFrom, supRunning_congr_prefix h, h t le_rfl]

/-- Occupation up to a fixed horizon depends only on the path on that horizon. -/
theorem supOccupation_congr_prefix (ε : ℝ) {f g : DLoc} {t : ℝ≥0}
    (h : ∀ u ≤ t, f.1 u = g.1 u) : supOccupation ε f t = supOccupation ε g t := by
  have heq : occupationSet ε f t = occupationSet ε g t := by
    ext u
    simp only [occupationSet, Set.mem_ofPred_eq]
    apply and_congr_right
    intro hu0
    apply and_congr_right
    intro hut
    have hut' : u.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]
      exact_mod_cast hut
    have huR : supReflected f u.toNNReal = supReflected g u.toNNReal := by
      rw [supReflected, supReflected, supRunning_congr_prefix (fun v hv => h v (hv.trans hut')),
        h u.toNNReal hut']
    rw [huR]
  change ε⁻¹ * (volume (occupationSet ε f t)).toReal = ε⁻¹ * (volume (occupationSet ε g t)).toReal
  rw [heq]

private theorem rawFiltration_eq_comap_restrict (s : ℝ≥0) :
    DLoc.rawFiltration s =
      MeasurableSpace.comap (DLoc.restrict s) (inferInstance : MeasurableSpace (D (s : ℝ) ℝ)) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro hts
    let t' : Set.Icc (0 : ℝ) (s : ℝ) := ⟨t, t.2, by exact_mod_cast hts⟩
    have heq : DLoc.eval t = (fun g : D (s : ℝ) ℝ => g t') ∘ DLoc.restrict s := by
      rfl
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (BGW.Skorokhod.measurable_eval t').comap_le
  · change _ ≤ ⨆ t ≤ s, MeasurableSpace.comap (DLoc.eval t) inferInstance
    rw [BGW.Skorokhod.measurableSpace_eq_iSup_comap_eval
      (T := (s : ℝ)) (E := ℝ) (S := Set.univ) dense_univ s.2 (by simp)]
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, Set.mem_univ, iSup_true, iSup_le_iff]
    intro t
    let u : ℝ≥0 := ⟨t, t.2.1⟩
    have hus : u ≤ s := by exact_mod_cast t.2.2
    exact le_iSup_of_le u (le_iSup_of_le hus le_rfl)

private noncomputable def compactSupTest (T : ℝ≥0) (f : D (T : ℝ) ℝ) : ℝ :=
  ⨆ u : Set.Icc (0 : ℝ) (T : ℝ), f u

private theorem supRunning_eq_compactSupTest (f : DLoc) (t : ℝ≥0) :
    supRunning f t = compactSupTest t (DLoc.restrict t f) := by
  let _ : Nonempty (Set.Icc (0 : ℝ) (t : ℝ)) := ⟨⟨0, le_rfl, t.2⟩⟩
  have hb : BddAbove (Set.range (fun u : Set.Icc (0 : ℝ) (t : ℝ) =>
      DLoc.restrict t f u)) := (isBounded_range _).bddAbove
  apply le_antisymm
  · apply supRunning_le
    intro u
    have hut : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast u.2
    exact le_ciSup hb ⟨(u : ℝ), u.1.2, hut⟩
  · apply ciSup_le
    intro u
    exact eval_le_supRunning f (by exact_mod_cast u.2.2)

private theorem measurable_compactSupTest (t : ℝ≥0) : Measurable (compactSupTest t) := by
  have hm := BGW.Skorokhod.measurable_iSup_eval (T := (t : ℝ))
    (J := Set.univ) ordConnected_univ
  have he : (fun f : D (t : ℝ) ℝ =>
      ⨆ u : (Set.univ : Set (Set.Icc (0 : ℝ) (t : ℝ))), f u) = compactSupTest t := by
    funext f
    apply congrArg sSup
    ext y
    simp
  rw [he] at hm
  exact hm

private theorem measurable_rawFiltration_supRunning (t : ℝ≥0) :
    Measurable[DLoc.rawFiltration t] (fun f => supRunning f t) := by
  rw [rawFiltration_eq_comap_restrict]
  simp_rw [supRunning_eq_compactSupTest]
  exact (measurable_compactSupTest t).comp (Measurable.of_comap_le le_rfl)

/-- Raw adaptedness: `R^x_t` is measurable for the raw filtration `σ(X_u, u ≤ t)`. -/
theorem measurable_rawFiltration_supReflectedFrom (x t : ℝ≥0) :
    Measurable[DLoc.rawFiltration t] (fun f => supReflectedFrom x f t) := by
  rw [rawFiltration_eq_comap_restrict]
  let e : Set.Icc (0 : ℝ) (t : ℝ) := ⟨t, t.2, le_rfl⟩
  have he : Measurable (fun p : D (t : ℝ) ℝ => p e) := BGW.Skorokhod.measurable_eval e
  have hmeas : Measurable (fun p : D (t : ℝ) ℝ => max (x : ℝ) (compactSupTest t p) - p e) :=
    (measurable_const.max (measurable_compactSupTest t)).sub he
  have heq : (fun f : DLoc => supReflectedFrom x f t) =
      (fun p : D (t : ℝ) ℝ => max (x : ℝ) (compactSupTest t p) - p e) ∘
        DLoc.restrict t := by
    funext f
    unfold supReflectedFrom
    rw [supRunning_eq_compactSupTest]
    rfl
  rw [heq]
  exact hmeas.comp (Measurable.of_comap_le le_rfl)


private theorem measurable_eval_rawFiltration {s T : ℝ≥0} (hs : s ≤ T) :
    Measurable[DLoc.rawFiltration T] (DLoc.eval s) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le s (le_iSup_of_le hs le_rfl)

private theorem measurable_eval_rawFiltration_uncurry (T : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (DLoc.rawFiltration T)]
      (fun p : Set.Iic T × DLoc => p.2.1 p.1) := by
  let τ : Set.Iic T → Set.Icc (0 : ℝ) (T : ℝ) := fun t =>
    ⟨(t.1 : ℝ), t.1.2, by exact_mod_cast t.2⟩
  have hτ : Measurable τ := Measurable.subtype_mk (by fun_prop)
  have hrestrict : Measurable[DLoc.rawFiltration T] (DLoc.restrict T) := by
    rw [rawFiltration_eq_comap_restrict]
    exact Measurable.of_comap_le le_rfl
  exact BGW.Skorokhod.measurable_eval₂.comp
    ((hrestrict.comp measurable_snd).prodMk (hτ.comp measurable_fst))

private theorem measurable_supRunning_rawFiltration_uncurry (T : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (DLoc.rawFiltration T)]
      (fun p : Set.Iic T × DLoc => supRunning p.2 p.1) := by
  apply measurable_of_Ioi
  intro a
  have heq : (fun p : Set.Iic T × DLoc => supRunning p.2 p.1) ⁻¹' Ioi a =
      (⋃ q : {q : ℚ // 0 ≤ q ∧ (q : ℝ) < T},
        {p | (q.1 : ℝ) < (p.1 : ℝ) ∧ a < p.2.1 (Real.toNNReal q.1)}) ∪
        {p | a < p.2.1 p.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_union, Set.mem_iUnion,
      Set.mem_ofPred_eq]
    rw [lt_supRunning_iff]
    constructor
    · rintro (h | h)
      · obtain ⟨q, hq0, hqT, hqval⟩ := (DLoc.strictPassageAbove_lt_iff a p.2 p.1).mp h
        exact Or.inl ⟨⟨q, hq0, hqT.trans_le (by exact_mod_cast p.1.2)⟩, hqT, hqval⟩
      · exact Or.inr h
    · rintro (⟨⟨q, hqu, hqval⟩⟩ | h)
      · apply Or.inl
        apply (DLoc.strictPassageAbove_lt_iff a p.2 p.1).mpr
        exact ⟨q.1, q.2.1, hqu, hqval⟩
      · exact Or.inr h
  rw [heq]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro q
    have hqT : Real.toNNReal q.1 ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by exact_mod_cast q.2.1)]
      exact q.2.2.le
    exact (measurableSet_lt measurable_const
        (measurable_coe_nnreal_real.comp (measurable_subtype_coe.comp measurable_fst))).inter
      (measurableSet_lt measurable_const
        ((measurable_eval_rawFiltration hqT).comp measurable_snd))
  · exact measurableSet_lt measurable_const (measurable_eval_rawFiltration_uncurry T)

private theorem measurable_supReflected_rawFiltration_uncurry (T : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (DLoc.rawFiltration T)]
      (fun p : Set.Iic T × DLoc => supReflected p.2 p.1) :=
  (measurable_supRunning_rawFiltration_uncurry T).sub (measurable_eval_rawFiltration_uncurry T)

/-- Raw adaptedness of the occupation functional, every `ε`. -/
theorem measurable_rawFiltration_supOccupation (ε : ℝ) (t : ℝ≥0) :
    Measurable[DLoc.rawFiltration t] (fun f => supOccupation ε f t) := by
  let : MeasurableSpace DLoc := DLoc.rawFiltration t
  let clip : ℝ → Set.Iic t := fun u => ⟨min u.toNNReal t, min_le_right _ _⟩
  have hclip : Measurable clip := by
    apply Measurable.subtype_mk
    exact continuous_real_toNNReal.measurable.min measurable_const
  have hpair : @Measurable (DLoc × ℝ) (Set.Iic t × DLoc)
      (MeasurableSpace.prod (DLoc.rawFiltration t) inferInstance)
      (Subtype.instMeasurableSpace.prod (DLoc.rawFiltration t))
      (fun p => (clip p.2, p.1)) :=
    (hclip.comp measurable_snd).prodMk measurable_fst
  let A : Set (DLoc × ℝ) :=
    {p | 0 ≤ p.2 ∧ p.2 ≤ (t : ℝ) ∧ supReflected p.1 p.2.toNNReal < ε}
  have hR := (measurable_supReflected_rawFiltration_uncurry t).comp hpair
  dsimp only [Function.comp_def] at hR
  have hAaux : MeasurableSet {p : DLoc × ℝ | supReflected p.1 (clip p.2).1 < ε} :=
    measurableSet_lt hR (measurable_const (a := ε))
  have heq : A = {p : DLoc × ℝ | 0 ≤ p.2 ∧ p.2 ≤ (t : ℝ) ∧
      supReflected p.1 (clip p.2).1 < ε} := by
    ext p
    simp only [A, Set.mem_ofPred_eq]
    by_cases hu : 0 ≤ p.2 ∧ p.2 ≤ (t : ℝ)
    · have hle : p.2.toNNReal ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1]
        exact hu.2
      simp only [hu, true_and, clip, min_eq_left hle]
    · exact iff_of_false (fun hp => hu ⟨hp.1, hp.2.1⟩)
        (fun hp => hu ⟨hp.1, hp.2.1⟩)
  have hA : MeasurableSet[MeasurableSpace.prod (DLoc.rawFiltration t) inferInstance] A := by
    rw [heq]
    exact (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_const).inter hAaux)
  change Measurable[DLoc.rawFiltration t]
    (fun f => ε⁻¹ * (volume (occupationSet ε f t)).toReal)
  apply Measurable.mul measurable_const.inv
  have hm := (measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hA).ennreal_toReal
  simpa only [A, occupationSet, Set.preimage_ofPred_eq] using hm

/-- The reflected process is progressively measurable for the natural filtration. -/
theorem isStronglyProgressive_supReflectedFrom (x : ℝ≥0) :
    IsStronglyProgressive DLoc.filtration (fun t f => supReflectedFrom x f t) := by
  apply IsProgressive.isStronglyProgressive
  intro T
  have hm : Measurable[Subtype.instMeasurableSpace.prod (DLoc.rawFiltration T)]
      (fun p : Set.Iic T × DLoc => supReflectedFrom x p.2 p.1) :=
    (measurable_const.max (measurable_supRunning_rawFiltration_uncurry T)).sub
      (measurable_eval_rawFiltration_uncurry T)
  apply hm.mono _ le_rfl
  simp only [MeasurableSpace.prod]
  exact sup_le le_sup_left
    ((MeasurableSpace.comap_mono (DLoc.rawFiltration.le_rightCont T)).trans le_sup_right)

end BGW.StableTrees
