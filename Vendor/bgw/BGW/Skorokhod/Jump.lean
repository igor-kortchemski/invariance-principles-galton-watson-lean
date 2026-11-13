/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Largest jumps of real càdlàg paths

The largest positive and absolute jumps are invariant under time changes and are 2-Lipschitz for
the Skorokhod J1 metric.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- The largest positive jump `sup_t (f t - f (t-)) ∨ 0` of a real càdlàg path (C36). -/
noncomputable def maxJump (f : D T ℝ) : ℝ := ⨆ t, max (f t - Function.leftLim f t) 0

/-- The largest absolute jump `sup_t |f t - f (t-)|` of a real càdlàg path (C36). -/
noncomputable def maxAbsJump (f : D T ℝ) : ℝ := ⨆ t, |f t - Function.leftLim f t|

private theorem tendsto_timeChange_nhdsLT (σ : TimeChange T) (t : Set.Icc (0 : ℝ) T) :
    Tendsto σ (𝓝[<] t) (𝓝[<] σ t) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact σ.continuous.continuousAt.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact σ.lt_iff_lt.mpr hs

private theorem leftLim_comp_timeChange (f : D T ℝ) (σ : TimeChange T)
    (t : Set.Icc (0 : ℝ) T) :
    Function.leftLim (f ∘ σ) t = Function.leftLim f (σ t) := by
  have hσ := tendsto_timeChange_nhdsLT σ t
  rcases eq_or_neBot (𝓝[<] t) with ht | ht
  · have hinv : Tendsto σ.symm (𝓝[<] σ t) (𝓝[<] t) := by
      simpa using tendsto_timeChange_nhdsLT σ.symm (σ t)
    have hσt : 𝓝[<] σ t = ⊥ := by
      by_contra hne
      have : (𝓝[<] σ t).NeBot := neBot_iff.mpr hne
      have hneBot : (𝓝[<] t).NeBot := hinv.neBot
      exact hneBot.ne ht
    rw [leftLim_eq_of_eq_bot _ ht, leftLim_eq_of_eq_bot _ hσt]
    rfl
  · have : (𝓝[<] t).NeBot := ht
    have : (𝓝[<] σ t).NeBot := hσ.neBot
    exact leftLim_eq_of_tendsto (((isCadlag f).tendsto_nhdsLT_leftLim (σ t)).comp hσ)

private theorem isCadlag_comp_timeChange [TopologicalSpace E] (f : D T E)
    (σ : TimeChange T) : IsCadlag (f ∘ σ) := by
  refine ⟨fun t => ?_, fun t => ⟨Function.leftLim f (σ t), ?_⟩⟩
  · exact ((isCadlag f).isRightContinuous (σ t)).comp σ.continuous.continuousWithinAt
      (fun _ hs => σ.lt_iff_lt.mpr hs)
  · exact ((isCadlag f).tendsto_nhdsLT_leftLim (σ t)).comp
      (tendsto_timeChange_nhdsLT σ t)

private def reparam [TopologicalSpace E] (f : D T E) (σ : TimeChange T) : D T E where
  toFun := f ∘ σ
  isCadlag' := isCadlag_comp_timeChange f σ

private theorem maxJump_reparam (f : D T ℝ) (σ : TimeChange T) :
    maxJump (reparam f σ) = maxJump f := by
  unfold maxJump
  simp only [reparam, coe_mk, Function.comp_apply]
  calc
    (⨆ t, max (f (σ t) - Function.leftLim (f ∘ σ) t) 0) =
        ⨆ t, max (f (σ t) - Function.leftLim f (σ t)) 0 := by
      apply iSup_congr
      intro t
      rw [leftLim_comp_timeChange]
    _ = ⨆ t, max (f t - Function.leftLim f t) 0 :=
      Equiv.iSup_comp (g := fun t : Set.Icc (0 : ℝ) T =>
        max (f t - Function.leftLim f t) 0) σ.toEquiv

private theorem maxAbsJump_reparam (f : D T ℝ) (σ : TimeChange T) :
    maxAbsJump (reparam f σ) = maxAbsJump f := by
  unfold maxAbsJump
  simp only [reparam, coe_mk, Function.comp_apply]
  calc
    (⨆ t, |f (σ t) - Function.leftLim (f ∘ σ) t|) =
        ⨆ t, |f (σ t) - Function.leftLim f (σ t)| := by
      apply iSup_congr
      intro t
      rw [leftLim_comp_timeChange]
    _ = ⨆ t, |f t - Function.leftLim f t| :=
      Equiv.iSup_comp (g := fun t : Set.Icc (0 : ℝ) T =>
        |f t - Function.leftLim f t|) σ.toEquiv

private theorem dist_leftLim_le_iSup_dist (f g : D T ℝ) (t : Set.Icc (0 : ℝ) T) :
    dist (Function.leftLim f t) (Function.leftLim g t) ≤ ⨆ s, dist (f s) (g s) := by
  have hb : BddAbove (Set.range fun s : Set.Icc (0 : ℝ) T => dist (f s) (g s)) := by
    simpa using bddAbove_range_dist f g (OrderIso.refl _)
  rcases eq_or_neBot (𝓝[<] t) with ht | ht
  · rw [leftLim_eq_of_eq_bot _ ht, leftLim_eq_of_eq_bot _ ht]
    exact le_ciSup hb t
  · have : (𝓝[<] t).NeBot := ht
    exact isClosed_Iic.mem_of_tendsto
      (((isCadlag f).tendsto_nhdsLT_leftLim t).dist
        ((isCadlag g).tendsto_nhdsLT_leftLim t))
      (Eventually.of_forall fun s => le_ciSup hb s)

/-- Absolute jump sizes of a bounded-horizon càdlàg path are bounded above. -/
theorem bddAbove_absJump (f : D T ℝ) :
    BddAbove (Set.range fun t => |f t - Function.leftLim f t|) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp (isBounded_range f)
  refine ⟨C, ?_⟩
  rintro x ⟨t, rfl⟩
  change |f t - Function.leftLim f t| ≤ C
  rw [← Real.dist_eq]
  rcases eq_or_neBot (𝓝[<] t) with ht | ht
  · rw [leftLim_eq_of_eq_bot _ ht]
    exact hC t t
  · have : (𝓝[<] t).NeBot := ht
    have hm := Metric.isClosed_closedBall.mem_of_tendsto
      ((isCadlag f).tendsto_nhdsLT_leftLim t)
      (Eventually.of_forall fun s => show f s ∈ Metric.closedBall (f t) C from
        hC s t)
    simpa [Metric.mem_closedBall, dist_comm] using hm

/-- Positive jump sizes of a bounded-horizon càdlàg path are bounded above. -/
theorem bddAbove_maxJump (f : D T ℝ) :
    BddAbove (Set.range fun t => max (f t - Function.leftLim f t) 0) := by
  obtain ⟨C, hC⟩ := bddAbove_absJump f
  refine ⟨C, ?_⟩
  rintro x ⟨t, rfl⟩
  exact (max_le (le_abs_self _) (abs_nonneg _)).trans (hC (Set.mem_range_self t))

private theorem maxJump_le_add_two_iSup_dist (hT : 0 ≤ T) (f g : D T ℝ) :
    maxJump f ≤ maxJump g + 2 * (⨆ t, dist (f t) (g t)) := by
  have hd : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => dist (f t) (g t)) := by
    simpa using bddAbove_range_dist f g (OrderIso.refl _)
  have ht0 : Set.Icc (0 : ℝ) T := ⟨0, by simp [hT]⟩
  have _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨ht0⟩
  unfold maxJump
  apply ciSup_le
  intro t
  have hsub : f t - Function.leftLim f t ≤
      max (g t - Function.leftLim g t) 0 + |f t - g t| +
        |Function.leftLim f t - Function.leftLim g t| := by
    calc
      f t - Function.leftLim f t = (g t - Function.leftLim g t) +
          ((f t - g t) - (Function.leftLim f t - Function.leftLim g t)) := by ring
      _ ≤ max (g t - Function.leftLim g t) 0 +
          |(f t - g t) - (Function.leftLim f t - Function.leftLim g t)| :=
        add_le_add (le_max_left _ _) (le_abs_self _)
      _ ≤ max (g t - Function.leftLim g t) 0 +
          (|f t - g t| + |Function.leftLim f t - Function.leftLim g t|) :=
        add_le_add le_rfl (abs_sub _ _)
      _ = _ := by ring
  have hpoint : max (f t - Function.leftLim f t) 0 ≤
      max (g t - Function.leftLim g t) 0 + dist (f t) (g t) +
        dist (Function.leftLim f t) (Function.leftLim g t) := by
    simp only [Real.dist_eq]
    exact max_le hsub (by positivity)
  have hmaxg : max (g t - Function.leftLim g t) 0 ≤
      ⨆ s, max (g s - Function.leftLim g s) 0 := le_ciSup (bddAbove_maxJump g) t
  have hval : dist (f t) (g t) ≤ ⨆ s, dist (f s) (g s) := le_ciSup hd t
  have hlim := dist_leftLim_le_iSup_dist f g t
  linarith

private theorem maxAbsJump_le_add_two_iSup_dist (hT : 0 ≤ T) (f g : D T ℝ) :
    maxAbsJump f ≤ maxAbsJump g + 2 * (⨆ t, dist (f t) (g t)) := by
  have hd : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => dist (f t) (g t)) := by
    simpa using bddAbove_range_dist f g (OrderIso.refl _)
  have ht0 : Set.Icc (0 : ℝ) T := ⟨0, by simp [hT]⟩
  have _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨ht0⟩
  unfold maxAbsJump
  apply ciSup_le
  intro t
  have hsub : |f t - Function.leftLim f t| ≤
      |g t - Function.leftLim g t| + |f t - g t| +
        |Function.leftLim f t - Function.leftLim g t| := by
    calc
      |f t - Function.leftLim f t| = |(g t - Function.leftLim g t) +
          ((f t - g t) - (Function.leftLim f t - Function.leftLim g t))| := by congr 1; ring
      _ ≤ |g t - Function.leftLim g t| +
          |(f t - g t) - (Function.leftLim f t - Function.leftLim g t)| :=
        abs_add_le _ _
      _ ≤ |g t - Function.leftLim g t| +
          (|f t - g t| + |Function.leftLim f t - Function.leftLim g t|) :=
        add_le_add le_rfl (abs_sub _ _)
      _ = _ := by ring
  have hpoint : |f t - Function.leftLim f t| ≤
      |g t - Function.leftLim g t| + dist (f t) (g t) +
        dist (Function.leftLim f t) (Function.leftLim g t) := by
    simpa only [Real.dist_eq] using hsub
  have hmaxg : |g t - Function.leftLim g t| ≤
      ⨆ s, |g s - Function.leftLim g s| := le_ciSup (bddAbove_absJump g) t
  have hval : dist (f t) (g t) ≤ ⨆ s, dist (f s) (g s) := le_ciSup hd t
  have hlim := dist_leftLim_le_iSup_dist f g t
  linarith

private theorem maxJump_le_timeChange_cost (hT : 0 ≤ T) (f h : D T ℝ)
    (σ : TimeChange T) :
    maxJump f ≤ maxJump h + 2 *
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (h (σ t))) := by
  let g := reparam h σ
  have hest := maxJump_le_add_two_iSup_dist hT f g
  change maxJump f ≤ maxJump g + 2 * (⨆ t, dist (f t) (h (σ t))) at hest
  have hinv : maxJump g = maxJump h := maxJump_reparam h σ
  have hmax : (⨆ t, dist (f t) (h (σ t))) ≤
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (h (σ t))) :=
    le_max_right _ _
  rw [← hinv]
  linarith

private theorem maxAbsJump_le_timeChange_cost (hT : 0 ≤ T) (f h : D T ℝ)
    (σ : TimeChange T) :
    maxAbsJump f ≤ maxAbsJump h + 2 *
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (h (σ t))) := by
  let g := reparam h σ
  have hest := maxAbsJump_le_add_two_iSup_dist hT f g
  change maxAbsJump f ≤ maxAbsJump g + 2 * (⨆ t, dist (f t) (h (σ t))) at hest
  have hinv : maxAbsJump g = maxAbsJump h := maxAbsJump_reparam h σ
  have hmax : (⨆ t, dist (f t) (h (σ t))) ≤
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (h (σ t))) :=
    le_max_right _ _
  rw [← hinv]
  linarith

/-- The largest positive jump is 2-Lipschitz for J1 (C36). -/
theorem lipschitzWith_two_maxJump : LipschitzWith 2 (maxJump (T := T)) := by
  refine LipschitzWith.of_le_add_mul 2 fun f h => ?_
  by_cases hT : 0 ≤ T
  · rw [dist_eq_j1Dist, ← sub_le_iff_le_add', j1Dist]
    simp only [NNReal.coe_ofNat]
    rw [Real.mul_iInf_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    refine le_ciInf fun σ => ?_
    have hest := maxJump_le_timeChange_cost hT f h σ
    linarith
  · have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
      ⟨fun t => (not_le_of_gt (lt_of_not_ge hT)) (le_trans t.property.1 t.property.2)⟩
    have hzero (k : D T ℝ) : maxJump k = 0 := by
      unfold maxJump
      rw [@iSup_of_empty' ℝ _ _ hempty]
      simp
    rw [hzero f, hzero h]
    positivity

/-- The largest absolute jump is 2-Lipschitz for J1 (C36). -/
theorem lipschitzWith_two_maxAbsJump : LipschitzWith 2 (maxAbsJump (T := T)) := by
  refine LipschitzWith.of_le_add_mul 2 fun f h => ?_
  by_cases hT : 0 ≤ T
  · rw [dist_eq_j1Dist, ← sub_le_iff_le_add', j1Dist]
    simp only [NNReal.coe_ofNat]
    rw [Real.mul_iInf_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    refine le_ciInf fun σ => ?_
    have hest := maxAbsJump_le_timeChange_cost hT f h σ
    linarith
  · have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
      ⟨fun t => (not_le_of_gt (lt_of_not_ge hT)) (le_trans t.property.1 t.property.2)⟩
    have hzero (k : D T ℝ) : maxAbsJump k = 0 := by
      unfold maxAbsJump
      rw [@iSup_of_empty' ℝ _ _ hempty]
      simp
    rw [hzero f, hzero h]
    positivity

/-- **C36, continuous paths.**  A continuous path has zero largest upward jump. -/
theorem maxJump_eq_zero_of_continuous {f : D T ℝ} (hf : Continuous f) : maxJump f = 0 := by
  unfold maxJump
  apply le_antisymm
  · apply Real.iSup_nonpos
    intro t
    simp [(hf.continuousAt (x := t)).continuousWithinAt.leftLim_eq]
  · exact Real.iSup_nonneg fun t => le_max_right _ _

private theorem maxJump_eq_zero_iff_aux (f : D T ℝ) :
    maxJump f = 0 ↔ ∀ t, f t ≤ Function.leftLim f t := by
  constructor
  · intro h t
    let _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨t⟩
    have ht : max (f t - Function.leftLim f t) 0 ≤ maxJump f :=
      le_ciSup (bddAbove_maxJump f) t
    rw [h, max_le_iff] at ht
    exact sub_nonpos.mp ht.1
  · intro h
    apply le_antisymm
    · unfold maxJump
      apply Real.iSup_nonpos
      intro t
      exact max_le (sub_nonpos.mpr (h t)) le_rfl
    · unfold maxJump
      exact Real.iSup_nonneg fun t => le_max_right _ _

/-- **C36 with nonnegative jumps.**  If every jump is nonnegative, vanishing of `maxJump` is
equivalent to continuity. -/
theorem maxJump_eq_zero_iff_continuous_of_leftLim_le (f : D T ℝ)
    (hf : ∀ t, Function.leftLim f t ≤ f t) : maxJump f = 0 ↔ Continuous f := by
  constructor
  · intro h
    have hle := (maxJump_eq_zero_iff_aux f).mp h
    rw [continuous_iff_continuousAt]
    intro t
    have heq : Function.leftLim f t = f t := le_antisymm (hf t) (hle t)
    apply continuousAt_iff_continuous_left'_right'.mpr
    constructor
    · change Tendsto f (𝓝[<] t) (𝓝 (f t))
      rw [← heq]
      exact (isCadlag f).tendsto_nhdsLT_leftLim t
    · exact (isCadlag f).isRightContinuous t
  · exact maxJump_eq_zero_of_continuous

end BGW.Skorokhod
