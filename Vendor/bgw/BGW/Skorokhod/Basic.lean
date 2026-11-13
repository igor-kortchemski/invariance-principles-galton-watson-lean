/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.TimeChange

/-!
# Càdlàg paths with Billingsley's J1 metric

This file defines the space of càdlàg paths on a compact real interval and proves that
Billingsley's J1 distance is a metric when the state space is metric.

Horizon conventions: no sign condition on `T` is imposed. For `T < 0` the time domain is empty,
`D T E` is a singleton and every displayed supremum and distance is `0` (Mathlib's convention for
empty real suprema). For `T = 0`, evaluation at `0` identifies `D 0 E` isometrically with `E`.
The ordinary J1 metric is not complete; Polishness needs Billingsley's equivalent metric `d°`
and is not provided here.

References: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., 1999, §12;
S. N. Ethier and T. G. Kurtz, *Markov Processes*, 1986, ch. 3 (general metric state spaces).
-/

@[expose] public section

open Set Filter Topology
open scoped Classical

namespace BGW.Skorokhod

/-- The Skorokhod space `D([0,T], E)` of càdlàg paths on `[0,T]`. On the subtype
`Set.Icc 0 T`, `IsCadlag` is Billingsley's condition: right-continuity at every
`t < T` and a left limit at every `t > 0`. -/
structure D (T : ℝ) (E : Type*) [TopologicalSpace E] where
  /-- The underlying path. -/
  toFun : Set.Icc (0 : ℝ) T → E
  /-- The path is càdlàg. -/
  isCadlag' : IsCadlag toFun

variable {T : ℝ} {E : Type*}

instance [TopologicalSpace E] : FunLike (D T E) (Set.Icc (0 : ℝ) T) E where
  coe := D.toFun
  coe_injective f g h := by cases f; cases g; congr

/-- Coercing a path constructor to a function recovers its underlying path. -/
@[simp] theorem coe_mk [TopologicalSpace E] (p : Set.Icc (0 : ℝ) T → E)
    (hp : IsCadlag p) : ((⟨p, hp⟩ : D T E) : Set.Icc (0 : ℝ) T → E) = p := rfl

/-- The underlying function of a path is càdlàg. -/
theorem isCadlag [TopologicalSpace E] (f : D T E) : IsCadlag f := f.isCadlag'

@[ext] theorem ext [TopologicalSpace E] {f g : D T E} (h : ∀ t, f t = g t) : f = g :=
  DFunLike.ext f g h

/-- The range of a càdlàg path on `[0,T]` is bounded. -/
theorem isBounded_range [PseudoMetricSpace E] (f : D T E) :
    Bornology.IsBounded (Set.range f) := by
  by_cases hT : 0 ≤ T
  · have hcompactSpace : CompactSpace (Set.Icc (0 : ℝ) T) := inferInstance
    have hcompact : IsCompact (Set.univ : Set (Set.Icc (0 : ℝ) T)) :=
      @isCompact_univ (Set.Icc (0 : ℝ) T) _ hcompactSpace
    have himageBounded : Bornology.IsBounded (f '' Set.univ) :=
      isBounded_image_of_isCadlag_of_isCompact (isCadlag f) hcompact
    obtain ⟨C, hC⟩ := Metric.isBounded_image_iff.mp himageBounded
    rw [Metric.isBounded_range_iff]
    exact ⟨C, fun x y => hC x (Set.mem_univ _) y (Set.mem_univ _)⟩
  · rw [Metric.isBounded_range_iff]
    refine ⟨0, ?_⟩
    intro x
    exact (hT (le_trans x.property.1 x.property.2)).elim

/-- Billingsley's Skorokhod J1 distance:
`d(f,g) = inf_σ max (sup_t |σ t - t|) (sup_t dist (f t) (g (σ t)))`. -/
noncomputable def j1Dist [PseudoMetricSpace E] (f g : D T E) : ℝ :=
  ⨅ σ : TimeChange T, max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t)))

private noncomputable def j1Cost [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) : ℝ :=
  max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t)))

private instance : Nonempty (TimeChange T) := ⟨OrderIso.refl _⟩

private theorem iSup_eq_zero_of_neg (hT : T < 0) (u : Set.Icc (0 : ℝ) T → ℝ) :
    (⨆ t, u t) = 0 := by
  have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
    ⟨fun t => (not_le_of_gt hT) (le_trans t.property.1 t.property.2)⟩
  rw [@iSup_of_empty' ℝ _ _ hempty]
  simp

private theorem bddAbove_displacement (hT : 0 ≤ T) (σ : TimeChange T) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => |((σ t : ℝ)) - t|) := by
  refine ⟨T, ?_⟩
  rintro x ⟨t, rfl⟩
  exact TimeChange.abs_sub_le σ hT t

/-- Paths are bounded, so the suprema in `j1Dist` are genuine. -/
theorem bddAbove_range_dist [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    BddAbove (Set.range fun t => dist (f t) (g (σ t))) := by
  by_cases hT : 0 ≤ T
  · have hcompactSpace : CompactSpace (Set.Icc (0 : ℝ) T) := inferInstance
    have hcompact : IsCompact (Set.univ : Set (Set.Icc (0 : ℝ) T)) :=
      @isCompact_univ (Set.Icc (0 : ℝ) T) _ hcompactSpace
    have hfBound : Bornology.IsBounded (f '' Set.univ) :=
      isBounded_image_of_isCadlag_of_isCompact (isCadlag f) hcompact
    have hgBound : Bornology.IsBounded (g '' Set.univ) :=
      isBounded_image_of_isCadlag_of_isCompact (isCadlag g) hcompact
    obtain ⟨Cf, hCf⟩ := Metric.isBounded_image_iff.mp hfBound
    obtain ⟨Cg, hCg⟩ := Metric.isBounded_image_iff.mp hgBound
    let t₀ : Set.Icc (0 : ℝ) T := ⟨0, by simp [hT]⟩
    refine ⟨Cf + dist (f t₀) (g t₀) + Cg, ?_⟩
    rintro x ⟨t, rfl⟩
    have hleft := hCf t (Set.mem_univ _) t₀ (Set.mem_univ _)
    have hright := hCg t₀ (Set.mem_univ _) (σ t) (Set.mem_univ _)
    calc
      dist (f t) (g (σ t)) ≤ dist (f t) (f t₀) + dist (f t₀) (g t₀) +
          dist (g t₀) (g (σ t)) := dist_triangle4 _ _ _ _
      _ ≤ Cf + dist (f t₀) (g t₀) + Cg := by linarith
  · refine ⟨0, ?_⟩
    rintro x ⟨t, rfl⟩
    exact (hT (le_trans t.property.1 t.property.2)).elim

private theorem j1Cost_nonneg [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    0 ≤ j1Cost f g σ := by
  by_cases hT : 0 ≤ T
  · have htime : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, |((σ t : ℝ)) - t| :=
      le_ciSup_of_le (bddAbove_displacement hT σ) ⟨0, by simp [hT]⟩ (abs_nonneg _)
    have hpath : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t)) :=
      le_ciSup_of_le (bddAbove_range_dist f g σ) ⟨0, by simp [hT]⟩ (dist_nonneg)
    exact le_max_of_le_left htime
  · have hneg : T < 0 := lt_of_not_ge hT
    simp [j1Cost, iSup_eq_zero_of_neg hneg]

private theorem j1Dist_nonneg [PseudoMetricSpace E] (f g : D T E) : 0 ≤ j1Dist f g := by
  change 0 ≤ ⨅ σ : TimeChange T, j1Cost f g σ
  exact le_ciInf fun σ => j1Cost_nonneg f g σ

private theorem j1Dist_le_cost [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    j1Dist f g ≤ j1Cost f g σ := by
  have hbelow : BddBelow (Set.range fun τ : TimeChange T => j1Cost f g τ) := by
    refine ⟨0, ?_⟩
    rintro x ⟨τ, rfl⟩
    exact j1Cost_nonneg f g τ
  change (⨅ τ : TimeChange T, j1Cost f g τ) ≤ j1Cost f g σ
  exact ciInf_le hbelow σ

private theorem j1Cost_refl [PseudoMetricSpace E] (f : D T E) :
    j1Cost f f (OrderIso.refl _) = 0 := by
  by_cases hT : 0 ≤ T
  · simp [j1Cost]
  · have hneg : T < 0 := lt_of_not_ge hT
    simp [j1Cost, iSup_eq_zero_of_neg hneg]

private theorem j1Cost_symm [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    j1Cost g f σ.symm = j1Cost f g σ := by
  unfold j1Cost
  rw [TimeChange.iSup_abs_sub_symm]
  congr 1
  calc
    (⨆ t : Set.Icc (0 : ℝ) T, dist (g t) (f (σ.symm t))) =
        ⨆ t : Set.Icc (0 : ℝ) T, dist (g (σ t)) (f (σ.symm (σ t))) :=
          (Equiv.iSup_comp
            (g := fun t : Set.Icc (0 : ℝ) T => dist (g t) (f (σ.symm t))) σ.toEquiv).symm
    _ = ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t)) := by
          apply iSup_congr
          intro t
          rw [σ.symm_apply_apply, dist_comm]

private theorem j1Cost_trans_le [MetricSpace E] (hT : 0 ≤ T) (f g h : D T E)
    (σ τ : TimeChange T) :
    j1Cost f h (σ.trans τ) ≤ j1Cost f g σ + j1Cost g h τ := by
  have hσdisp := bddAbove_displacement hT σ
  have hτdisp := bddAbove_displacement hT τ
  have hσpath := bddAbove_range_dist f g σ
  have hτpath := bddAbove_range_dist g h τ
  have hrangeTime :
      (Set.range fun t : Set.Icc (0 : ℝ) T => |((σ.trans τ t : ℝ)) - t|).Nonempty :=
    ⟨_, ⟨⟨0, by simp [hT]⟩, rfl⟩⟩
  have htime :
      (⨆ t : Set.Icc (0 : ℝ) T, |((σ.trans τ t : ℝ)) - t|) ≤
        (⨆ t : Set.Icc (0 : ℝ) T, |((σ t : ℝ)) - t|) +
          (⨆ t : Set.Icc (0 : ℝ) T, |((τ t : ℝ)) - t|) := by
    refine csSup_le hrangeTime ?_
    rintro x ⟨t, rfl⟩
    have h₁ : |((σ t : ℝ)) - t| ≤ ⨆ s : Set.Icc (0 : ℝ) T, |((σ s : ℝ)) - s| :=
      le_ciSup_of_le hσdisp t le_rfl
    have h₂ : |((τ (σ t) : ℝ)) - σ t| ≤ ⨆ s : Set.Icc (0 : ℝ) T, |((τ s : ℝ)) - s| :=
      le_ciSup_of_le hτdisp (σ t) le_rfl
    have htri : |((τ (σ t) : ℝ) - (t : ℝ))| ≤
        |((τ (σ t) : ℝ) - (σ t : ℝ))| + |((σ t : ℝ) - (t : ℝ))| := by
      calc
        |((τ (σ t) : ℝ) - (t : ℝ))| =
            |(((τ (σ t) : ℝ) - (σ t : ℝ)) + ((σ t : ℝ) - (t : ℝ)))| := by congr 1; ring
        _ ≤ |((τ (σ t) : ℝ) - (σ t : ℝ))| + |((σ t : ℝ) - (t : ℝ))| := abs_add_le _ _
    calc
      |((σ.trans τ t : ℝ)) - t| = |((τ (σ t) : ℝ)) - t| := rfl
      _ ≤ |((τ (σ t) : ℝ)) - σ t| + |((σ t : ℝ)) - t| := htri
      _ ≤ (⨆ s : Set.Icc (0 : ℝ) T, |((τ s : ℝ)) - s|) +
          (⨆ s : Set.Icc (0 : ℝ) T, |((σ s : ℝ)) - s|) := add_le_add h₂ h₁
      _ = _ := by ring
  have hpath :
      (⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (h (σ.trans τ t))) ≤
        (⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t))) +
          (⨆ t : Set.Icc (0 : ℝ) T, dist (g t) (h (τ t))) := by
    have hrangePath :
        (Set.range fun t : Set.Icc (0 : ℝ) T => dist (f t) (h (σ.trans τ t))).Nonempty :=
      ⟨_, ⟨⟨0, by simp [hT]⟩, rfl⟩⟩
    refine csSup_le hrangePath ?_
    rintro x ⟨t, rfl⟩
    have h₁ : dist (f t) (g (σ t)) ≤ ⨆ s : Set.Icc (0 : ℝ) T, dist (f s) (g (σ s)) :=
      le_ciSup_of_le hσpath t le_rfl
    have h₂ : dist (g (σ t)) (h (τ (σ t))) ≤
        ⨆ s : Set.Icc (0 : ℝ) T, dist (g s) (h (τ s)) :=
      le_ciSup_of_le hτpath (σ t) le_rfl
    calc
      dist (f t) (h (σ.trans τ t)) = dist (f t) (h (τ (σ t))) := rfl
      _ ≤ dist (f t) (g (σ t)) + dist (g (σ t)) (h (τ (σ t))) := dist_triangle _ _ _
      _ ≤ _ := add_le_add h₁ h₂
  unfold j1Cost
  calc
    max (⨆ t, |((σ.trans τ t : ℝ)) - t|) (⨆ t, dist (f t) (h (σ.trans τ t))) ≤
        max ((⨆ t, |((σ t : ℝ)) - t|) + (⨆ t, |((τ t : ℝ)) - t|))
          ((⨆ t, dist (f t) (g (σ t))) + (⨆ t, dist (g t) (h (τ t)))) :=
            max_le_max htime hpath
    _ ≤ max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t))) +
          max (⨆ t, |((τ t : ℝ)) - t|) (⨆ t, dist (g t) (h (τ t))) := by
          refine max_le ?_ ?_
          · exact add_le_add (le_max_left _ _) (le_max_left _ _)
          · exact add_le_add (le_max_right _ _) (le_max_right _ _)

/-! The following helper extracts a time change from a vanishing infimum. -/
private theorem exists_j1Cost_lt_of_j1Dist_eq_zero [PseudoMetricSpace E]
    (f g : D T E) (_hT : 0 ≤ T) (hzero : j1Dist f g = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : TimeChange T, j1Cost f g σ < ε := by
  have hlt : (⨅ σ : TimeChange T, j1Cost f g σ) < ε := by
    change j1Dist f g < ε
    rw [hzero]
    exact hε
  exact exists_lt_of_ciInf_lt hlt

private theorem exists_j1Cost_lt_two [PseudoMetricSpace E]
    (f g : D T E) (hpos : 0 < j1Dist f g) :
    ∃ σ : TimeChange T, j1Cost f g σ < 2 * j1Dist f g := by
  have hlt : (⨅ σ : TimeChange T, j1Cost f g σ) < 2 * j1Dist f g := by
    change j1Dist f g < 2 * j1Dist f g
    nlinarith
  exact exists_lt_of_ciInf_lt hlt

/-- The J1 cost with the path comparison written in inverse-time orientation. -/
private noncomputable def j1AltCost [PseudoMetricSpace E]
    (f g : D T E) (σ : TimeChange T) : ℝ :=
  max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f (σ t)) (g t))

private theorem j1AltCost_eq_j1Cost_symm [PseudoMetricSpace E]
    (f g : D T E) (σ : TimeChange T) : j1AltCost f g σ = j1Cost f g σ.symm := by
  unfold j1AltCost j1Cost
  rw [TimeChange.iSup_abs_sub_symm]
  congr 1
  calc
    (⨆ t : Set.Icc (0 : ℝ) T, dist (f (σ t)) (g t)) =
        ⨆ t : Set.Icc (0 : ℝ) T, dist (f (σ t)) (g (σ.symm (σ t))) := by
          apply iSup_congr
          intro t
          rw [σ.symm_apply_apply]
    _ = ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ.symm t)) :=
      Equiv.iSup_comp
        (g := fun t : Set.Icc (0 : ℝ) T => dist (f t) (g (σ.symm t))) σ.toEquiv

private theorem displacement_iSup_nonneg (σ : TimeChange T) :
    0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, |((σ t : ℝ)) - t| := by
  by_cases hT : 0 ≤ T
  · exact le_ciSup_of_le (bddAbove_displacement hT σ) ⟨0, by simp [hT]⟩ (abs_nonneg _)
  · simp [iSup_eq_zero_of_neg (lt_of_not_ge hT)]

private theorem path_iSup_nonneg [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t)) := by
  by_cases hT : 0 ≤ T
  · exact le_ciSup_of_le (bddAbove_range_dist f g σ) ⟨0, by simp [hT]⟩ dist_nonneg
  · simp [iSup_eq_zero_of_neg (lt_of_not_ge hT)]

private theorem altPath_iSup_nonneg [PseudoMetricSpace E] (f g : D T E)
    (σ : TimeChange T) :
    0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (f (σ t)) (g t) := by
  by_cases hT : 0 ≤ T
  · have hEq : (⨆ t : Set.Icc (0 : ℝ) T, dist (f (σ t)) (g t)) =
        ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ.symm t)) := by
      calc
        (⨆ t : Set.Icc (0 : ℝ) T, dist (f (σ t)) (g t)) =
            ⨆ t : Set.Icc (0 : ℝ) T, dist (f (σ t)) (g (σ.symm (σ t))) := by
              apply iSup_congr
              intro t
              rw [σ.symm_apply_apply]
        _ = ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ.symm t)) :=
          Equiv.iSup_comp
            (g := fun t : Set.Icc (0 : ℝ) T => dist (f t) (g (σ.symm t))) σ.toEquiv
    rw [hEq]
    exact path_iSup_nonneg f g σ.symm
  · simp [iSup_eq_zero_of_neg (lt_of_not_ge hT)]

/-- The J1 metric space structure, with distance `j1Dist`. -/
noncomputable instance instMetricSpace [MetricSpace E] : MetricSpace (D T E) where
  dist := j1Dist
  dist_self f := by
    have hnonneg := j1Dist_nonneg f f
    have hle : j1Dist f f ≤ 0 := by
      have := j1Dist_le_cost f f (OrderIso.refl _)
      simpa [j1Cost_refl] using this
    exact le_antisymm hle hnonneg
  dist_comm f g := by
    apply le_antisymm
    · apply le_ciInf
      intro σ
      calc
        j1Dist f g ≤ j1Cost f g σ.symm := j1Dist_le_cost _ _ _
        _ = j1Cost g f σ := j1Cost_symm g f σ
    · apply le_ciInf
      intro σ
      calc
        j1Dist g f ≤ j1Cost g f σ.symm := j1Dist_le_cost _ _ _
        _ = j1Cost f g σ := j1Cost_symm f g σ
  dist_triangle f g h := by
    by_cases hT : 0 ≤ T
    · have hε : ∀ ε > 0, j1Dist f h ≤ j1Dist f g + j1Dist g h + ε := by
        intro ε hε
        have hex₁ : j1Dist f g < j1Dist f g + ε / 2 := by linarith
        have hex₂ : j1Dist g h < j1Dist g h + ε / 2 := by linarith
        obtain ⟨σ, hσ⟩ := exists_lt_of_ciInf_lt (f := fun σ : TimeChange T => j1Cost f g σ) <| by
          change (⨅ σ : TimeChange T, j1Cost f g σ) < j1Dist f g + ε / 2
          simpa [j1Dist, j1Cost] using hex₁
        obtain ⟨τ, hτ⟩ := exists_lt_of_ciInf_lt (f := fun τ : TimeChange T => j1Cost g h τ) <| by
          change (⨅ τ : TimeChange T, j1Cost g h τ) < j1Dist g h + ε / 2
          simpa [j1Dist, j1Cost] using hex₂
        exact (calc
          j1Dist f h ≤ j1Cost f h (σ.trans τ) := j1Dist_le_cost _ _ _
          _ ≤ j1Cost f g σ + j1Cost g h τ := j1Cost_trans_le hT f g h σ τ
          _ < j1Dist f g + j1Dist g h + ε := by linarith).le
      exact le_of_forall_pos_le_add hε
    · have hneg : T < 0 := lt_of_not_ge hT
      simp [j1Dist, hneg]
  eq_of_dist_eq_zero := by
    intro f g hzero
    by_cases hT : 0 ≤ T
    · apply ext
      intro t
      by_cases htT : (t : ℝ) = T
      · have htop : t = (⟨T, by simp [hT]⟩ : Set.Icc (0 : ℝ) T) := Subtype.ext htT
        subst t
        apply eq_of_forall_dist_le
        intro ε hε
        obtain ⟨σ, hσ⟩ := exists_j1Cost_lt_of_j1Dist_eq_zero f g hT hzero (ε := ε) hε
        have hpath := le_ciSup_of_le (bddAbove_range_dist f g σ)
          ⟨T, by simp [hT]⟩ le_rfl
        have htopfix := TimeChange.apply_top σ hT
        calc
          dist (f ⟨T, by simp [hT]⟩) (g ⟨T, by simp [hT]⟩) =
              dist (f ⟨T, by simp [hT]⟩) (g (σ ⟨T, by simp [hT]⟩)) := by rw [htopfix]
          _ ≤ ⨆ s : Set.Icc (0 : ℝ) T, dist (f s) (g (σ s)) := hpath
          _ ≤ j1Cost f g σ := le_max_of_le_right le_rfl
          _ ≤ ε := hσ.le
      · have htlt : (t : ℝ) < T := lt_of_le_of_ne t.property.2 htT
        apply eq_of_forall_dist_le
        intro ε hε
        let ε₀ := ε / 3
        have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
        obtain ⟨δf, hδf, hfclose⟩ :=
          Metric.continuousWithinAt_iff.mp ((isCadlag f).isRightContinuous t) ε₀ hε₀
        obtain ⟨δg, hδg, hgclose⟩ :=
          Metric.continuousWithinAt_iff.mp ((isCadlag g).isRightContinuous t) ε₀ hε₀
        let η := min ((T - (t : ℝ)) / 4) (min ε₀ (min δf δg / 4))
        have hη : 0 < η := by
          dsimp [η]
          refine lt_min (by linarith) ?_
          refine lt_min hε₀ ?_
          exact div_pos (lt_min hδf hδg) (by norm_num)
        have hηT : η ≤ (T - (t : ℝ)) / 4 := (min_le_left _ _).trans le_rfl
        have hηε : η ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
        have hηδ : η ≤ min δf δg / 4 := (min_le_right _ _).trans (min_le_right _ _)
        obtain ⟨σ, hσ⟩ := exists_j1Cost_lt_of_j1Dist_eq_zero f g hT hzero (ε := η) hη
        let u : Set.Icc (0 : ℝ) T := ⟨(t : ℝ) + 2 * η, by
          constructor
          · have ht0 : 0 ≤ (t : ℝ) := t.property.1
            positivity
          · have : 2 * η ≤ (T - (t : ℝ)) / 2 := by linarith
            linarith⟩
        let s := σ.symm u
        have hmove : |(s : ℝ) - u| < η := by
          have hbdd := bddAbove_displacement hT σ.symm
          have hle : |(σ.symm u : ℝ) - u| ≤
              ⨆ r : Set.Icc (0 : ℝ) T, |(σ.symm r : ℝ) - r| := le_ciSup_of_le hbdd u le_rfl
          have hinv := TimeChange.iSup_abs_sub_symm σ
          dsimp [s]
          calc
            |(σ.symm u : ℝ) - u| ≤ ⨆ r : Set.Icc (0 : ℝ) T, |(σ.symm r : ℝ) - r| := hle
            _ = ⨆ r : Set.Icc (0 : ℝ) T, |(σ r : ℝ) - r| := hinv
            _ ≤ j1Cost f g σ := le_max_left _ _
            _ < η := hσ
        have hs_gt : (t : ℝ) < (s : ℝ) := by
          have := (abs_lt.mp hmove).1
          dsimp [s, u] at this ⊢
          linarith
        have hs_dist : dist s t < δf := by
          rw [Subtype.dist_eq, Real.dist_eq]
          have hsmall : |(s : ℝ) - t| < δf := by
            have hηδ' : η ≤ δf / 4 := by
              linarith [hηδ, min_le_left δf δg]
            have hsu : (s : ℝ) - t < 3 * η := by
              have := (abs_lt.mp hmove).2
              dsimp [s, u] at this ⊢
              linarith
            have hsleft : 0 < (s : ℝ) - t := sub_pos.mpr hs_gt
            rw [abs_of_nonneg hsleft.le]
            linarith
          exact hsmall
        have hu_gt : (t : ℝ) < (u : ℝ) := by
          dsimp [u]
          linarith
        have hu_dist : dist u t < δg := by
          rw [Subtype.dist_eq, Real.dist_eq]
          have hηδ' : η ≤ δg / 4 := by
            linarith [hηδ, min_le_right δf δg]
          have : |(u : ℝ) - t| = 2 * η := by
            dsimp [u]
            rw [abs_of_nonneg (by positivity)]
            ring
          rw [this]
          linarith
        have hsIoi : s ∈ Set.Ioi t := by
          change (t : ℝ) < (s : ℝ)
          exact hs_gt
        have huIoi : u ∈ Set.Ioi t := by
          change (t : ℝ) < (u : ℝ)
          exact hu_gt
        have hfε := hfclose hsIoi hs_dist
        have hgε := hgclose huIoi hu_dist
        have hpath := le_ciSup_of_le (bddAbove_range_dist f g σ) s le_rfl
        have hpathε : dist (f s) (g u) < ε₀ := by
          have hbound : dist (f s) (g (σ s)) ≤
              ⨆ r : Set.Icc (0 : ℝ) T, dist (f r) (g (σ r)) := hpath
          have hσs : σ s = u := σ.apply_symm_apply u
          rw [hσs] at hbound
          have hmax : (⨆ r : Set.Icc (0 : ℝ) T, dist (f r) (g (σ r))) ≤ j1Cost f g σ :=
            le_max_of_le_right le_rfl
          exact lt_of_le_of_lt (hbound.trans hmax) (lt_of_lt_of_le hσ hηε)
        have htriangle := dist_triangle4 (f t) (f s) (g u) (g t)
        have hdist₁ : dist (f t) (f s) < ε₀ := by
          simpa only [dist_comm] using hfε
        calc
          dist (f t) (g t) ≤ dist (f t) (f s) + dist (f s) (g u) + dist (g u) (g t) := htriangle
          _ ≤ ε₀ + ε₀ + ε₀ := by
            have hdist₃ : dist (g u) (g t) = dist (g t) (g u) := dist_comm _ _
            rw [hdist₃]
            linarith [hdist₁.le, hpathε.le, hgε.le]
          _ = ε := by dsimp [ε₀]; ring
    · have hneg : T < 0 := lt_of_not_ge hT
      apply ext
      intro t
      exact (hT (le_trans t.property.1 t.property.2)).elim

/-- The J1 metric has distance exactly `j1Dist`. -/
theorem dist_eq_j1Dist [MetricSpace E] (f g : D T E) : dist f g = j1Dist f g := rfl

/-- Billingsley's characterization of J1 convergence by time changes. -/
theorem tendsto_iff_exists_timeChange [MetricSpace E] {ι : Type*} {l : Filter ι}
    {u : ι → D T E} {f : D T E} :
    Tendsto u l (𝓝 f) ↔ ∃ σ : ι → TimeChange T,
      Tendsto (fun i => ⨆ t, |((σ i t : ℝ)) - t|) l (𝓝 0) ∧
      Tendsto (fun i => ⨆ t, dist (u i (σ i t)) (f t)) l (𝓝 0) := by
  constructor
  · intro hu
    classical
    let d : ι → ℝ := fun i => j1Dist (u i) f
    have hd_nonneg : ∀ i, 0 ≤ d i := fun i => j1Dist_nonneg (u i) f
    have hd : Tendsto d l (𝓝 0) := by
      have hdist := (tendsto_iff_dist_tendsto_zero).1 hu
      simpa only [d, dist_eq_j1Dist] using hdist
    have htwo : Tendsto (fun i => 2 * d i) l (𝓝 0) := by
      have hadd := hd.add hd
      simpa [two_mul] using hadd
    let σ : ι → TimeChange T := fun i =>
      if hz : d i = 0 then OrderIso.refl _ else
        (Classical.choose (exists_j1Cost_lt_two (u i) f
          (lt_of_le_of_ne (hd_nonneg i) (Ne.symm hz)))).symm
    have hcost (i) : j1AltCost (u i) f (σ i) ≤ 2 * d i := by
      by_cases hz : d i = 0
      · have heq : u i = f := by
          apply eq_of_dist_eq_zero
          simpa only [dist_eq_j1Dist, d] using hz
        have hσ : σ i = OrderIso.refl _ := by simp [σ, hz]
        rw [hσ, heq]
        have hcost0 : j1AltCost f f (OrderIso.refl _) = 0 := by
          rw [j1AltCost_eq_j1Cost_symm]
          simpa using j1Cost_refl f
        rw [hcost0]
        simp [d, hz]
      · have hpos : 0 < d i := lt_of_le_of_ne (hd_nonneg i) (Ne.symm hz)
        let he := exists_j1Cost_lt_two (u i) f hpos
        have hspec : j1Cost (u i) f (Classical.choose he) < 2 * d i := by
          simpa [d] using Classical.choose_spec he
        have hσ : σ i = (Classical.choose he).symm := by simp [σ, hz]
        rw [hσ, j1AltCost_eq_j1Cost_symm]
        simpa [OrderIso.symm_symm] using hspec.le
    have hdisp_bound (i) :
        (⨆ t : Set.Icc (0 : ℝ) T, |((σ i t : ℝ)) - t|) ≤ 2 * d i := by
      exact (le_max_left _ _).trans (hcost i)
    have hpath_bound (i) :
        (⨆ t : Set.Icc (0 : ℝ) T, dist (u i (σ i t)) (f t)) ≤ 2 * d i := by
      exact (le_max_right _ _).trans (hcost i)
    exact ⟨σ,
      squeeze_zero (fun i => displacement_iSup_nonneg (σ i)) hdisp_bound htwo,
      squeeze_zero (fun i => altPath_iSup_nonneg (u i) f (σ i)) hpath_bound htwo⟩
  · rintro ⟨σ, hdisp, hpath⟩
    have hmax : Tendsto (fun i => max
        (⨆ t : Set.Icc (0 : ℝ) T, |((σ i t : ℝ)) - t|)
        (⨆ t : Set.Icc (0 : ℝ) T, dist (u i (σ i t)) (f t))) l (𝓝 0) := by
      simpa using hdisp.max hpath
    have hupper (i) : j1Dist (u i) f ≤ max
        (⨆ t : Set.Icc (0 : ℝ) T, |((σ i t : ℝ)) - t|)
        (⨆ t : Set.Icc (0 : ℝ) T, dist (u i (σ i t)) (f t)) := by
      calc
        j1Dist (u i) f ≤ j1Cost (u i) f (σ i).symm := j1Dist_le_cost _ _ _
        _ = j1AltCost (u i) f (σ i) := (j1AltCost_eq_j1Cost_symm _ _ _).symm
    have hj1 : Tendsto (fun i => j1Dist (u i) f) l (𝓝 0) :=
      squeeze_zero (fun i => j1Dist_nonneg (u i) f) hupper hmax
    apply (tendsto_iff_dist_tendsto_zero).2
    simpa only [dist_eq_j1Dist] using hj1

/-- The J1 distance is at most the uniform distance (take the identity time change). -/
theorem dist_le_iSup_dist [MetricSpace E] (f g : D T E) :
    dist f g ≤ ⨆ t, dist (f t) (g t) := by
  rw [dist_eq_j1Dist]
  by_cases hT : 0 ≤ T
  · have hsup : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g t) :=
      le_ciSup_of_le (bddAbove_range_dist f g (OrderIso.refl _)) ⟨0, by simp [hT]⟩ dist_nonneg
    calc
      j1Dist f g ≤ j1Cost f g (OrderIso.refl _) := j1Dist_le_cost _ _ _
      _ = max 0 (⨆ t, dist (f t) (g t)) := by simp [j1Cost]
      _ = ⨆ t, dist (f t) (g t) := max_eq_right hsup
  · have hneg : T < 0 := lt_of_not_ge hT
    simp [j1Dist, hneg]

end BGW.Skorokhod
