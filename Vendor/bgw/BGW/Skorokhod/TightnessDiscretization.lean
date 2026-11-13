/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.TightnessMatching
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Finite discretization of uniformly controlled càdlàg paths

Partition lengths are bounded by the minimum spacing. Each partition node is labeled by
a finite net in the compact product of the time interval and the state-value set. Equal
labels imply small complete Skorokhod distance.
-/

@[expose] public section

open Set
open scoped Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*} [MetricSpace E]

private structure Sample (f : D T E) (δ a κ : ℝ) (C : Set (ℝ × E)) where
  n : ℕ
  x : Fin (n + 1) → Icc (0 : ℝ) T
  zero : (x 0 : ℝ) = 0
  last : (x (Fin.last n) : ℝ) = T
  mono : StrictMono x
  gap : ∀ i : Fin n, δ < (x i.succ : ℝ) - x i.castSucc
  osc : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
    x i.castSucc ≤ s → s < x i.succ → x i.castSucc ≤ t → t < x i.succ →
      dist (f s) (f t) ≤ a
  label : Fin (n + 1) → C
  approx : ∀ i, dist ((x i : ℝ), f (x i)) (label i).1 < κ

private noncomputable def sampleCode {f : D T E} {δ a κ : ℝ} {C : Set (ℝ × E)}
    (s : Sample f δ a κ C) (N : ℕ) : Fin (N + 1) → Option C :=
  fun i => if hi : i.val < s.n + 1 then some (s.label ⟨i.val, hi⟩) else none

private theorem close_of_sampleCode_eq {f g : D T E} {δ ε κ : ℝ} {C : Set (ℝ × E)}
    (s : Sample f δ (ε / 8) κ C) (t : Sample g δ (ε / 8) κ C)
    (N : ℕ) (hsN : s.n ≤ N) (hst : s.n = t.n)
    (hcode : sampleCode s N = sampleCode t N)
    (hε : 0 < ε) (hκ : κ ≤ ε / 16)
    (hκlow : 8 * κ ≤ (1 - Real.exp (-(ε / 2))) * δ)
    (hκupp : 8 * κ ≤ (Real.exp (ε / 2) - 1) * δ) : j1CompleteDist f g < ε := by
  rcases s with ⟨n, x, hx0, hxT, hx, hgap, hf, c, hc⟩
  rcases t with ⟨m, y, hy0, hyT, hy, _, hg, d, hd⟩
  dsimp only at hst hsN
  subst m
  apply j1CompleteDist_lt_of_close_partition_nodes f g x y hx0 hxT hy0 hyT hx hy
    hε hκ hκlow hκupp hgap hf hg
  intro i
  have hiN : i.val < N + 1 := lt_of_lt_of_le i.isLt (Nat.add_le_add_right hsN 1)
  have hlabel := congrFun hcode ⟨i.val, hiN⟩
  simp only [sampleCode, dite_eq_left i.isLt, Option.some.injEq] at hlabel
  have hi : (⟨i.val, i.isLt⟩ : Fin (n + 1)) = i := rfl
  simp only [hi] at hlabel
  calc
    dist ((x i : ℝ), f (x i)) ((y i : ℝ), g (y i)) ≤
        dist ((x i : ℝ), f (x i)) (c i).1 +
          dist ((y i : ℝ), g (y i)) (d i).1 := by
      rw [hlabel]
      exact dist_triangle_right _ _ _
    _ < 2 * κ := by linarith [hc i, hd i]

/-- A compact value set and uniformly small oscillations on partitions with uniformly
positive spacing imply total boundedness in Billingsley's complete metric. -/
theorem totallyBounded_toDComplete_of_partitions {A : Set (D T E)} {K : Set E}
    (hK : IsCompact K) (hA : ∀ f ∈ A, ∀ t, f t ∈ K)
    (hpart : ∀ a > 0, ∃ δ > 0, ∀ f ∈ A,
      ∃ (n : ℕ) (p : Fin (n + 1) → ℝ),
        p 0 = 0 ∧ p (Fin.last n) = T ∧ StrictMono p ∧
        (∀ i : Fin n, δ < p i.succ - p i.castSucc) ∧
        ∀ (i : Fin n) (s u : Icc (0 : ℝ) T),
          p i.castSucc ≤ s → (s : ℝ) < p i.succ →
          p i.castSucc ≤ u → (u : ℝ) < p i.succ → dist (f s) (f u) ≤ a) :
    TotallyBounded (toDComplete '' A) := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  obtain ⟨δ, hδ, hpart⟩ := hpart (ε / 8) (by positivity)
  let κ := min (ε / 16) (min ((1 - Real.exp (-(ε / 2))) * δ / 8)
    ((Real.exp (ε / 2) - 1) * δ / 8))
  have hlow : 0 < 1 - Real.exp (-(ε / 2)) := by
    have := Real.exp_lt_one_iff.mpr (show -(ε / 2) < 0 by linarith)
    linarith
  have hupp : 0 < Real.exp (ε / 2) - 1 := by
    have := Real.one_lt_exp_iff.mpr (show 0 < ε / 2 by linarith)
    linarith
  have hκpos : 0 < κ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hκ : κ ≤ ε / 16 := min_le_left _ _
  have hκlow : 8 * κ ≤ (1 - Real.exp (-(ε / 2))) * δ := by
    have : κ ≤ (1 - Real.exp (-(ε / 2))) * δ / 8 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hκupp : 8 * κ ≤ (Real.exp (ε / 2) - 1) * δ := by
    have : κ ≤ (Real.exp (ε / 2) - 1) * δ / 8 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hprod : IsCompact (Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp hprod.totallyBounded κ hκpos
  let : Fintype C := hC.fintype
  have hcover' (z : ℝ × E) (hz : z ∈ Icc (0 : ℝ) T ×ˢ K) :
      ∃ c : C, dist z c.1 < κ := by
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hcover hz)
    exact ⟨⟨c, hc⟩, hzc⟩
  let B := toDComplete '' A
  let original (u : B) : D T E := toDComplete.symm u.1
  have horiginal (u : B) : original u ∈ A := by
    obtain ⟨f, hf, heq⟩ := u.2
    change toDComplete.symm u.1 ∈ A
    rw [← heq, toDComplete.symm_apply_apply]
    exact hf
  have hsamples (u : B) : Nonempty (Sample (original u) δ (ε / 8) κ C) := by
    obtain ⟨n, p, hp0, hpT, hp, hgap, hosc⟩ := hpart _ (horiginal u)
    let x : Fin (n + 1) → Icc (0 : ℝ) T := fun i => ⟨p i, by
      constructor
      · rw [← hp0]; exact hp.monotone (Fin.zero_le i)
      · rw [← hpT]; exact hp.monotone (Fin.le_last i)⟩
    choose c hc using fun i => hcover' ((x i : ℝ), original u (x i))
      ⟨(x i).2, hA _ (horiginal u) (x i)⟩
    exact ⟨⟨n, x, hp0, hpT, hp, hgap, hosc, c, hc⟩⟩
  let samples (u : B) := Classical.choice (hsamples u)
  let N := ⌈T / δ⌉₊
  have hN (u : B) : (samples u).n ≤ N :=
    partition_length_le (fun i => ((samples u).x i : ℝ))
      (samples u).zero (samples u).last hδ (samples u).gap
  let code (u : B) : Fin (N + 1) × (Fin (N + 1) → Option C) :=
    (⟨(samples u).n, Nat.lt_succ_of_le (hN u)⟩, sampleCode (samples u) N)
  refine ⟨Fin (N + 1) × (Fin (N + 1) → Option C), inferInstance, code, ?_⟩
  intro u v huv
  have hn : (samples u).n = (samples v).n := congrArg (fun z => z.1.val) huv
  have hc : sampleCode (samples u) N = sampleCode (samples v) N := congrArg Prod.snd huv
  change j1CompleteDist (original u) (original v) < ε
  exact close_of_sampleCode_eq (samples u) (samples v) N (hN u) hn hc hε hκ hκlow hκupp

end BGW.Skorokhod
