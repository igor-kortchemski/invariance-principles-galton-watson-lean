/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessBasic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Compact sets of anchored paths with prescribed moduli

A common modulus at one positive scale bounds paths anchored at zero. A sequence
of vanishing modulus tolerances gives equicontinuity. Arzelà-Ascoli then yields
a compact subset of the continuous path space containing every such path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical BoundedContinuousFunction
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

private theorem anchored_path_bound (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (f : Set.Icc (0 : ℝ) (T : ℝ) → ℝ)
    (hf0 : f ⟨0, le_rfl, T.coe_nonneg⟩ = 0)
    (hmod : ∀ s t : Set.Icc (0 : ℝ) (T : ℝ), |(s : ℝ) - t| ≤ δ → |f s - f t| ≤ 1)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) : |f t| ≤ (⌈(T : ℝ) / δ⌉₊ : ℝ) := by
  let u (k : ℕ) : Set.Icc (0 : ℝ) (T : ℝ) :=
    ⟨min ((k : ℝ) * δ) (t : ℝ), le_min (by positivity) t.property.1,
      (min_le_right _ _).trans t.property.2⟩
  have hu0 : u 0 = ⟨0, le_rfl, T.coe_nonneg⟩ := by
    apply Subtype.ext
    simp only [u, Nat.cast_zero, zero_mul, min_eq_left t.property.1]
  have hb (k : ℕ) : |f (u k)| ≤ (k : ℝ) := by
    induction k with
    | zero => rw [hu0, hf0]; simp
    | succ k ih =>
      have hh := abs_min_sub_min_le_max (((k + 1 : ℕ) : ℝ) * δ) (t : ℝ)
        ((k : ℝ) * δ) (t : ℝ)
      rw [show (((k + 1 : ℕ) : ℝ) * δ) - (k : ℝ) * δ = δ by push_cast; ring,
        sub_self, abs_zero, abs_of_pos hδ, max_eq_left hδ.le] at hh
      have hm := hmod (u (k + 1)) (u k) hh
      have ht := abs_sub_le (f (u (k + 1))) (f (u k)) 0
      simp only [sub_zero] at ht
      push_cast
      linarith
  have hceil : (T : ℝ) ≤ (⌈(T : ℝ) / δ⌉₊ : ℝ) * δ :=
    (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  have he : u ⌈(T : ℝ) / δ⌉₊ = t := by
    apply Subtype.ext
    exact min_eq_right (t.property.2.trans hceil)
  simpa only [he] using hb ⌈(T : ℝ) / δ⌉₊

/-- Anchored paths with a common vanishing modulus envelope lie in one compact set. -/
theorem exists_isCompact_of_height_moduli (T : ℝ≥0) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) :
    ∃ K : Set C(Set.Icc (0 : ℝ) (T : ℝ), ℝ), IsCompact K ∧
      ∀ f : C(Set.Icc (0 : ℝ) (T : ℝ), ℝ), f ⟨0, le_rfl, T.coe_nonneg⟩ = 0 →
        (∀ j, ∀ s t : Set.Icc (0 : ℝ) (T : ℝ), |(s : ℝ) - t| ≤ δ j →
          |f s - f t| ≤ 1 / (j + 1 : ℝ)) → f ∈ K := by
  let X : Type := Set.Icc (0 : ℝ) (T : ℝ)
  let z : X := ⟨0, le_rfl, T.coe_nonneg⟩
  let A : Set (X →ᵇ ℝ) := {f | f z = 0 ∧ ∀ j : ℕ, ∀ s t : X,
    |(s : ℝ) - t| ≤ δ j → |f s - f t| ≤ 1 / (j + 1 : ℝ)}
  have heval (t : X) : Continuous (fun f : X →ᵇ ℝ => f t) :=
    (continuous_apply t).comp BoundedContinuousFunction.continuous_coe
  have hcond : IsClosed {f : X →ᵇ ℝ | ∀ j : ℕ, ∀ s t : X,
      |(s : ℝ) - t| ≤ δ j → |f s - f t| ≤ 1 / (j + 1 : ℝ)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_iInter fun _ => isClosed_le ((heval s).sub (heval t)).abs continuous_const
  have hclosed : IsClosed A := (isClosed_eq (heval z) continuous_const).inter hcond
  let M : ℝ := ⌈(T : ℝ) / δ 0⌉₊
  have hbound (f : X →ᵇ ℝ) (t : X) (hf : f ∈ A) : f t ∈ Icc (-M) M := by
    have hh := anchored_path_bound T (δ 0) (hδ 0) f hf.1
      (by simpa only [Nat.cast_zero, zero_add, div_one] using hf.2 0) t
    exact abs_le.mp hh
  have heq : Equicontinuous ((↑) : A → X → ℝ) := by
    intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    refine ⟨δ j, hδ j, ?_⟩
    intro y hy f
    change |f.1 x - f.1 y| < ε
    have hd : |(x : ℝ) - y| ≤ δ j := by
      change |(y : ℝ) - x| < δ j at hy
      rw [abs_sub_comm]
      exact hy.le
    exact (f.property.2 j x y hd).trans_lt hj
  have hA : IsCompact A := BoundedContinuousFunction.arzela_ascoli₂
    (Icc (-M) M) isCompact_Icc A hclosed hbound heq
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  refine ⟨e.symm '' A, hA.image e.symm.continuous, ?_⟩
  intro f hf0 hf
  refine ⟨e f, ⟨hf0, hf⟩, e.symm_apply_apply f⟩

end BGW.StableTrees.HeightTightness
