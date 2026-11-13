/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
import BGW.Skorokhod.TightnessMatching
import BGW.Skorokhod.TightnessPartitions
import Mathlib.Topology.MetricSpace.Basic

/-!
# Separability of the Skorokhod space

Finite small-oscillation partitions are encoded by countably many time-value labels.
The partition matching estimate controls the diameter of each code class.
-/

@[expose] public section

namespace BGW.Skorokhod

open Set Filter Topology

variable {T : ℝ} {E : Type*}

private noncomputable def labelRadius (ε : ℝ) (k : ℕ) : ℝ :=
  min (ε / 16) (min ((1 - Real.exp (-(ε / 2))) / (k + 1) / 8)
    ((Real.exp (ε / 2) - 1) / (k + 1) / 8))

private theorem labelRadius_pos {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    0 < labelRadius ε k := by
  have hl : 0 < 1 - Real.exp (-(ε / 2)) := by
    have := Real.exp_lt_one_iff.mpr (show -(ε / 2) < 0 by linarith)
    linarith
  have hu : 0 < Real.exp (ε / 2) - 1 := by
    have := Real.one_lt_exp_iff.mpr (show 0 < ε / 2 by linarith)
    linarith
  exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

private structure SepSample [MetricSpace E] (f : D T E) (ε : ℝ) (C : Set (ℝ × E)) where
  n : ℕ
  k : ℕ
  x : Fin (n + 1) → Icc (0 : ℝ) T
  zero : (x 0 : ℝ) = 0
  last : (x (Fin.last n) : ℝ) = T
  mono : StrictMono x
  gap : ∀ i : Fin n, 1 / (k + 1 : ℝ) < (x i.succ : ℝ) - x i.castSucc
  osc : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
    x i.castSucc ≤ s → s < x i.succ → x i.castSucc ≤ t → t < x i.succ →
      dist (f s) (f t) ≤ ε / 8
  label : Fin (n + 1) → C
  approx : ∀ i, dist ((x i : ℝ), f (x i)) (label i).val < labelRadius ε k

private def sepCode [MetricSpace E] {f : D T E} {ε : ℝ} {C : Set (ℝ × E)}
    (s : SepSample f ε C) : ℕ × (Σ n : ℕ, Fin (n + 1) → C) :=
  (s.k, ⟨s.n, s.label⟩)

private theorem close_of_sepCode_eq [MetricSpace E] {f g : D T E} {ε : ℝ} {C : Set (ℝ × E)}
    (s : SepSample f ε C) (t : SepSample g ε C)
    (hε : 0 < ε) (hcode : sepCode s = sepCode t) : j1CompleteDist f g < ε := by
  rcases s with ⟨n, k, x, hx0, hxT, hx, hgap, hf, c, hc⟩
  rcases t with ⟨m, l, y, hy0, hyT, hy, _, hg, d, hd⟩
  have hkl : k = l := congrArg Prod.fst hcode
  have hnm : n = m := congrArg (fun z => z.2.1) hcode
  subst l
  subst m
  have hcd : c = d := by
    simpa only [sepCode, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hcode
  let κ := labelRadius ε k
  have hκ : κ ≤ ε / 16 := min_le_left _ _
  have hκlow : 8 * κ ≤ (1 - Real.exp (-(ε / 2))) * (1 / (k + 1 : ℝ)) := by
    have := (min_le_right (ε / 16) _).trans
      (min_le_left ((1 - Real.exp (-(ε / 2))) / (k + 1) / 8)
        ((Real.exp (ε / 2) - 1) / (k + 1) / 8))
    change labelRadius ε k ≤ _ at this
    dsimp [labelRadius] at this
    dsimp [κ, labelRadius]
    rw [mul_one_div]
    linarith
  have hκupp : 8 * κ ≤ (Real.exp (ε / 2) - 1) * (1 / (k + 1 : ℝ)) := by
    have := (min_le_right (ε / 16) _).trans
      (min_le_right ((1 - Real.exp (-(ε / 2))) / (k + 1) / 8)
        ((Real.exp (ε / 2) - 1) / (k + 1) / 8))
    change labelRadius ε k ≤ _ at this
    dsimp [labelRadius] at this
    dsimp [κ, labelRadius]
    rw [mul_one_div]
    linarith
  apply j1CompleteDist_lt_of_close_partition_nodes f g x y hx0 hxT hy0 hyT hx hy
    hε hκ hκlow hκupp hgap hf hg
  intro i
  calc
    dist ((x i : ℝ), f (x i)) ((y i : ℝ), g (y i)) ≤
        dist ((x i : ℝ), f (x i)) (c i).val +
          dist ((y i : ℝ), g (y i)) (d i).val := by
      rw [hcd]
      exact dist_triangle_right _ _ _
    _ < 2 * κ := by linarith [hc i, hd i]

/-- `D` is separable for J1 when `E` is (Billingsley 1999, Theorem 12.2; C2). -/
instance instSeparableSpace [MetricSpace E] [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (D T E) := by
  classical
  by_cases hT : 0 ≤ T
  · have hsecond : SecondCountableTopology (DComplete T E) := by
      apply Metric.secondCountable_of_countable_discretization
      intro ε hε
      obtain ⟨C, hCc, hCd⟩ := TopologicalSpace.exists_countable_dense (ℝ × E)
      let : Countable C := hCc
      have hsamples (f : D T E) : Nonempty (SepSample f ε C) := by
        obtain ⟨n, p, hp0, hpT, hp, hosc⟩ :=
          exists_partition_dist_le f hT (show 0 < ε / 8 by positivity)
        let x : Fin (n + 1) → Icc (0 : ℝ) T := fun i => ⟨p i, by
          constructor
          · rw [← hp0]; exact hp.monotone (Fin.zero_le i)
          · rw [← hpT]; exact hp.monotone (Fin.le_last i)⟩
        have hr : Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) atTop (𝓝 0) := by
          simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
            (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
        have hevent : ∀ᶠ k : ℕ in atTop, ∀ i : Fin n,
            1 / (k + 1 : ℝ) < p i.succ - p i.castSucc := by
          apply eventually_all.mpr
          intro i
          exact hr.eventually (gt_mem_nhds (sub_pos.mpr (hp (Fin.castSucc_lt_succ (i := i)))))
        obtain ⟨k, hk⟩ := hevent.exists
        have hlabel (i : Fin (n + 1)) :
            ∃ c : C, dist ((x i : ℝ), f (x i)) c.val < labelRadius ε k := by
          obtain ⟨c, hcC, hc⟩ := hCd.exists_dist_lt ((x i : ℝ), f (x i))
            (labelRadius_pos hε k)
          exact ⟨⟨c, hcC⟩, by simpa only [dist_comm] using hc⟩
        choose c hc using hlabel
        exact ⟨⟨n, k, x, hp0, hpT, hp, hk, hosc, c, hc⟩⟩
      let sample (f : D T E) := Classical.choice (hsamples f)
      let code (f : DComplete T E) := sepCode (sample (toDComplete.symm f))
      let β := ℕ × (Σ n : ℕ, Fin (n + 1) → C)
      let : Encodable β := Encodable.ofCountable β
      refine ⟨β, inferInstance, code, ?_⟩
      intro f g hfg
      exact (close_of_sepCode_eq (sample (toDComplete.symm f))
        (sample (toDComplete.symm g)) hε hfg).le
    let : SecondCountableTopology (DComplete T E) := hsecond
    let : SecondCountableTopology (D T E) := toDComplete.secondCountableTopology
    infer_instance
  · let : IsEmpty (Icc (0 : ℝ) T) := ⟨fun t => hT (t.2.1.trans t.2.2)⟩
    let : Subsingleton (D T E) := ⟨fun f g => by ext t; exact isEmptyElim t⟩
    infer_instance

end BGW.Skorokhod
