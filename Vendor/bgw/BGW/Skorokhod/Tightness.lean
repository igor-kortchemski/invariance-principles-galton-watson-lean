/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import Mathlib.MeasureTheory.Measure.Tight

import BGW.Skorokhod.TightnessPartitions
import BGW.Skorokhod.TightnessDiscretization
import BGW.Skorokhod.CompleteMetricLimits
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compactness and tightness in Skorokhod space

The oscillation uses half-open partition blocks, excluding the terminal value. The modulus
tends to zero for every càdlàg path, by the finite small-oscillation partition lemma.

Uniform modulus bounds and bounded values give compact closure. The proof uses finite
discretization in Billingsley's complete metric, then transfers through the identity
homeomorphism. Countable error budgets give uniform tightness; the eventual form uses
uniform modulus and value bounds on compact sets to include finitely many initial laws.

References: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., 1999, §12 (the
modulus `w'`, (12.6)–(12.7), Theorem 12.3) and Theorem 13.2.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Billingsley's càdlàg modulus `w'_f(δ)`: the infimum, over partitions
`0 = t₀ < t₁ < ⋯ < t_r = T` whose steps all exceed `δ`, of the largest oscillation of `f` on the
half-open blocks `[t_{i-1}, t_i)`. (It is `0` by convention when no such partition exists,
e.g. for `δ ≥ T`; only small `δ` matter.) -/
noncomputable def cadlagModulus [PseudoMetricSpace E] (f : D T E) (δ : ℝ) : ℝ :=
  ⨅ (p : Σ r : ℕ, {t : Fin (r + 1) → ℝ // t 0 = 0 ∧ t (Fin.last r) = T ∧ StrictMono t ∧
      ∀ i : Fin r, δ < t i.succ - t i.castSucc}),
    ⨆ (i : Fin p.1) (s : Set.Icc (0 : ℝ) T) (u : Set.Icc (0 : ℝ) T)
      (_ : p.2.1 i.castSucc ≤ s ∧ (s : ℝ) < p.2.1 i.succ ∧
        p.2.1 i.castSucc ≤ u ∧ (u : ℝ) < p.2.1 i.succ),
      dist (f s) (f u)

/-- The modulus is nonnegative, including when the partition type is empty. -/
theorem cadlagModulus_nonneg [PseudoMetricSpace E] (f : D T E) (δ : ℝ) :
    0 ≤ cadlagModulus f δ := by
  apply Real.iInf_nonneg
  intro p
  exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => dist_nonneg

/-- A partition with blocks of oscillation at most `ε` bounds the modulus at every smaller
mesh threshold. -/
theorem cadlagModulus_le_of_partition [PseudoMetricSpace E] (f : D T E) {δ ε : ℝ}
    (hε : 0 ≤ ε) {r : ℕ} (t : Fin (r + 1) → ℝ) (ht0 : t 0 = 0)
    (htr : t (Fin.last r) = T) (hmono : StrictMono t)
    (hstep : ∀ i : Fin r, δ < t i.succ - t i.castSucc)
    (hosc : ∀ (i : Fin r) (s u : Icc (0 : ℝ) T),
      t i.castSucc ≤ s → (s : ℝ) < t i.succ →
      t i.castSucc ≤ u → (u : ℝ) < t i.succ → dist (f s) (f u) ≤ ε) :
    cadlagModulus f δ ≤ ε := by
  unfold cadlagModulus
  refine (ciInf_le ?_ ⟨r, t, ht0, htr, hmono, hstep⟩).trans ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => dist_nonneg
  · apply Real.iSup_le _ hε
    intro i
    apply Real.iSup_le _ hε
    intro s
    apply Real.iSup_le _ hε
    intro u
    apply Real.iSup_le _ hε
    exact fun h => hosc i s u h.1 h.2.1 h.2.2.1 h.2.2.2

private noncomputable def partitionOscillation [PseudoMetricSpace E] (f : D T E)
    {r : ℕ} (t : Fin (r + 1) → ℝ) : ℝ :=
  ⨆ (i : Fin r) (s : Icc (0 : ℝ) T) (u : Icc (0 : ℝ) T)
    (_ : t i.castSucc ≤ s ∧ (s : ℝ) < t i.succ ∧
      t i.castSucc ≤ u ∧ (u : ℝ) < t i.succ), dist (f s) (f u)

private theorem dist_le_partitionOscillation [PseudoMetricSpace E] (f : D T E)
    {r : ℕ} (t : Fin (r + 1) → ℝ) (i : Fin r) (s u : Icc (0 : ℝ) T)
    (hs : t i.castSucc ≤ s) (hs' : (s : ℝ) < t i.succ)
    (hu : t i.castSucc ≤ u) (hu' : (u : ℝ) < t i.succ) :
    dist (f s) (f u) ≤ partitionOscillation f t := by
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp (isBounded_range f)
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hdist : ∀ s u, dist (f s) (f u) ≤ B := fun s u =>
    (hC s u).trans (le_max_left _ _)
  let v := fun (j : Fin r) (s u : Icc (0 : ℝ) T) =>
    ⨆ (_ : t j.castSucc ≤ s ∧ (s : ℝ) < t j.succ ∧
      t j.castSucc ≤ u ∧ (u : ℝ) < t j.succ), dist (f s) (f u)
  have hv : ∀ j s u, v j s u ≤ B := fun j s u => Real.iSup_le (fun _ => hdist s u) hB
  have hvu : ∀ j s, (⨆ u, v j s u) ≤ B := fun j s => Real.iSup_le (hv j s) hB
  have hvs : ∀ j, (⨆ s, ⨆ u, v j s u) ≤ B := fun j => Real.iSup_le (hvu j) hB
  change dist (f s) (f u) ≤ ⨆ j, ⨆ s, ⨆ u, v j s u
  refine le_ciSup_of_le ⟨B, forall_mem_range.mpr hvs⟩ i ?_
  refine le_ciSup_of_le ⟨B, forall_mem_range.mpr (hvu i)⟩ s ?_
  refine le_ciSup_of_le ⟨B, forall_mem_range.mpr (hv i s)⟩ u ?_
  change dist (f s) (f u) ≤ ⨆ (_ : t i.castSucc ≤ s ∧ (s : ℝ) < t i.succ ∧
    t i.castSucc ≤ u ∧ (u : ℝ) < t i.succ), dist (f s) (f u)
  have hbound : BddAbove (Set.range fun (_ : t i.castSucc ≤ s ∧ (s : ℝ) < t i.succ ∧
      t i.castSucc ≤ u ∧ (u : ℝ) < t i.succ) => dist (f s) (f u)) :=
    ⟨B, by rintro _ ⟨_, rfl⟩; exact hdist s u⟩
  exact le_ciSup hbound ⟨hs, hs', hu, hu'⟩

/-- A strict modulus bound yields an actual admissible partition with the same strict
oscillation bound. The infimum need not be attained. -/
theorem exists_partition_of_cadlagModulus_lt [PseudoMetricSpace E] (f : D T E)
    {δ ε : ℝ} (hδ : 0 < δ) (hδT : δ < T) (hmod : cadlagModulus f δ < ε) :
    ∃ (r : ℕ) (t : Fin (r + 1) → ℝ), t 0 = 0 ∧ t (Fin.last r) = T ∧ StrictMono t ∧
      (∀ i : Fin r, δ < t i.succ - t i.castSucc) ∧
      ∀ (i : Fin r) (s u : Icc (0 : ℝ) T),
        t i.castSucc ≤ s → (s : ℝ) < t i.succ →
        t i.castSucc ≤ u → (u : ℝ) < t i.succ → dist (f s) (f u) < ε := by
  have hT : 0 < T := hδ.trans hδT
  let t : Fin 2 → ℝ := fun i => if i = 0 then 0 else T
  have hmono : StrictMono t := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hi : i = 0 := by ext; omega
    subst i
    simpa [t] using hT
  have hstep : ∀ i : Fin 1, δ < t i.succ - t i.castSucc := by
    intro i
    have hi : i = 0 := by ext; omega
    subst i
    simpa [t] using hδT
  have hnonempty : Nonempty (Σ r : ℕ, {t : Fin (r + 1) → ℝ // t 0 = 0 ∧
      t (Fin.last r) = T ∧ StrictMono t ∧
      ∀ i : Fin r, δ < t i.succ - t i.castSucc}) :=
    ⟨⟨1, t, by simp [t], by simp [t], hmono, hstep⟩⟩
  obtain ⟨⟨r, t, ht0, htr, hmono, hstep⟩, hosc⟩ := exists_lt_of_ciInf_lt hmod
  refine ⟨r, t, ht0, htr, hmono, hstep, ?_⟩
  intro i s u hs hs' hu hu'
  exact (dist_le_partitionOscillation f t i s u hs hs' hu hu').trans_lt hosc

/-- At a nonpositive time horizon the modulus is identically zero. -/
theorem cadlagModulus_eq_zero_of_nonpos [PseudoMetricSpace E] (f : D T E)
    (hT : T ≤ 0) (δ : ℝ) : cadlagModulus f δ = 0 := by
  unfold cadlagModulus
  have hp : ∀ (p : Σ r : ℕ, {t : Fin (r + 1) → ℝ // t 0 = 0 ∧
      t (Fin.last r) = T ∧ StrictMono t ∧
      ∀ i : Fin r, δ < t i.succ - t i.castSucc}), p.1 = 0 := by
    rintro ⟨r, t, ht0, htr, hmono, _⟩
    by_contra hr
    change r ≠ 0 at hr
    have hlt : (0 : Fin (r + 1)) < Fin.last r := by
      change 0 < r
      omega
    have := hmono hlt
    rw [ht0, htr] at this
    exact (not_lt_of_ge hT) this
  have heq : ∀ (p : Σ r : ℕ, {t : Fin (r + 1) → ℝ // t 0 = 0 ∧
      t (Fin.last r) = T ∧ StrictMono t ∧
      ∀ i : Fin r, δ < t i.succ - t i.castSucc}),
      (⨆ (i : Fin p.1) (s : Icc (0 : ℝ) T) (u : Icc (0 : ℝ) T)
      (_ : p.2.1 i.castSucc ≤ s ∧ (s : ℝ) < p.2.1 i.succ ∧
        p.2.1 i.castSucc ≤ u ∧ (u : ℝ) < p.2.1 i.succ), dist (f s) (f u)) = 0 := by
    intro p
    have hempty : IsEmpty (Fin p.1) := ⟨fun i => by
      have hi := i.isLt
      have hp0 := hp p
      omega⟩
    rw [@iSup_of_empty' ℝ _ _ hempty]
    simp
  simp_rw [heq]
  simp

/-- Every càdlàg path has `w'_f(δ) → 0` as `δ ↓ 0` (Billingsley 1999, (12.7)). -/
theorem tendsto_cadlagModulus [MetricSpace E] (f : D T E) :
    Tendsto (fun δ => cadlagModulus f δ) (𝓝[>] 0) (𝓝 0) := by
  by_cases hT : 0 ≤ T
  · refine tendsto_order.mpr ⟨?_, ?_⟩
    · intro a ha
      exact Filter.Eventually.of_forall fun δ => ha.trans_le (cadlagModulus_nonneg f δ)
    · intro ε hε
      obtain ⟨r, t, ht0, htr, hmono, hosc⟩ := exists_partition_dist_le f hT
        (half_pos hε)
      have hstep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i : Fin r,
          δ < t i.succ - t i.castSucc := by
        apply Filter.eventually_all.mpr
        intro i
        exact (eventually_lt_nhds (sub_pos.mpr (hmono i.castSucc_lt_succ))).filter_mono
          nhdsWithin_le_nhds
      filter_upwards [hstep] with δ hδ
      exact (cadlagModulus_le_of_partition f (half_pos hε).le t ht0 htr hmono hδ hosc).trans_lt
        (half_lt_self hε)
  · have hnonpos : T ≤ 0 := (lt_of_not_ge hT).le
    simpa only [cadlagModulus_eq_zero_of_nonpos f hnonpos] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))

/-- Arzelà–Ascoli criterion in `D` (sufficiency, Billingsley 1999, Theorem 12.3): a set of paths
with values in a fixed bounded set of a proper space and with uniformly vanishing modulus `w'`
has compact closure. -/
theorem isCompact_closure_of_cadlagModulus [MetricSpace E] [ProperSpace E] {A : Set (D T E)}
    {K : Set E} (hK : Bornology.IsBounded K) (hA : ∀ f ∈ A, ∀ t, f t ∈ K)
    (hmod : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∀ f ∈ A, cadlagModulus f δ ≤ ε) :
    IsCompact (closure A) := by
  have ht : TotallyBounded (toDComplete '' A) :=
    totallyBounded_toDComplete_of_partitions hK.isCompact_closure
      (fun f hf t => subset_closure (hA f hf t)) (by
        intro a ha
        obtain ⟨δ, hδ, hδT, hsmall⟩ := hmod (a / 2) (half_pos ha)
        refine ⟨δ, hδ, fun f hf => ?_⟩
        obtain ⟨n, p, hp0, hpT, hp, hgap, hosc⟩ :=
          exists_partition_of_cadlagModulus_lt f hδ hδT
            ((hsmall f hf).trans_lt (half_lt_self ha))
        exact ⟨n, p, hp0, hpT, hp, hgap,
          fun i s u hs hs' hu hu' => (hosc i s u hs hs' hu hu').le⟩)
  have hc := ht.closure.isCompact_of_isClosed isClosed_closure
  rw [← toDComplete.image_closure] at hc
  exact toDComplete.isEmbedding.isCompact_iff.mpr hc

/-- Tightness criterion in `D` (sufficiency, uniform form of Billingsley 1999, Theorem 13.2):
if, uniformly in `n`, the paths stay in a bounded set with high probability and the modulus
`w'` is small with high probability, then the laws are tight. Measures of possibly
non-measurable sets are outer measures, so no measurability of `w'` is assumed. -/
theorem isTightMeasureSet_of_cadlagModulus [MetricSpace E] [ProperSpace E]
    [MeasurableSpace (D T E)] {ι : Type*}
    (P : ι → Measure (D T E))
    (hbdd : ∀ η > 0, ∃ K : Set E, Bornology.IsBounded K ∧
      ∀ i, P i {f | ∃ t, f t ∉ K} ≤ ENNReal.ofReal η)
    (hmod : ∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∀ i, P i {f | ε < cadlagModulus f δ} ≤ ENNReal.ofReal η) :
    IsTightMeasureSet (Set.range P) := by
  classical
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro η hη
  obtain ⟨err, herr, hsum⟩ := ENNReal.exists_pos_sum_of_countable hη.ne' (Option ℕ)
  obtain ⟨K, hK, hbound⟩ := hbdd (err none) (NNReal.coe_pos.mpr (herr none))
  let e (n : ℕ) : ℝ := 1 / (n + 1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  choose δ hδ hδT hprob using fun n => hmod (e n) (he n) (err (some n))
    (NNReal.coe_pos.mpr (herr (some n)))
  let bad : Option ℕ → Set (D T E)
    | none => {f | ∃ t, f t ∉ K}
    | some n => {f | e n < cadlagModulus f (δ n)}
  let A := (⋃ j, bad j)ᶜ
  have hvalues : ∀ f ∈ A, ∀ t, f t ∈ K := by
    intro f hf t
    by_contra ht
    exact hf (mem_iUnion.mpr ⟨none, t, ht⟩)
  have hsmall : ∀ ε > 0, ∃ d, 0 < d ∧ d < T ∧ ∀ f ∈ A, cadlagModulus f d ≤ ε := by
    intro ε hε
    have hlim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    refine ⟨δ n, hδ n, hδT n, fun f hf => ?_⟩
    have hnot : ¬ e n < cadlagModulus f (δ n) := fun h =>
      hf (mem_iUnion.mpr ⟨some n, h⟩)
    exact (le_of_not_gt hnot).trans hn.le
  refine ⟨closure A, isCompact_closure_of_cadlagModulus hK hvalues hsmall, ?_⟩
  rintro μ ⟨i, rfl⟩
  have hbad (j) : P i (bad j) ≤ (err j : ℝ≥0∞) := by
    cases j with
    | none => simpa only [bad, ENNReal.ofReal_coe_nnreal] using hbound i
    | some n => simpa only [bad, ENNReal.ofReal_coe_nnreal] using hprob n i
  calc
    P i (closure A)ᶜ ≤ P i (⋃ j, bad j) := measure_mono (by
      intro f hf
      by_contra hnot
      exact hf (subset_closure hnot))
    _ ≤ ∑' j, P i (bad j) := measure_iUnion_le bad
    _ ≤ ∑' j, (err j : ℝ≥0∞) := ENNReal.tsum_le_tsum hbad
    _ ≤ η := hsum.le

/-- The modulus increases with its threshold as long as the larger threshold admits
partitions. This restriction excludes the empty-infimum convention. -/
theorem cadlagModulus_mono [PseudoMetricSpace E] (f : D T E) {δ d : ℝ}
    (hδd : δ ≤ d) (hd : 0 < d) (hdT : d < T) : cadlagModulus f δ ≤ cadlagModulus f d := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, p, hp0, hpT, hp, hgap, hosc⟩ :=
    exists_partition_of_cadlagModulus_lt f hd hdT (lt_add_of_pos_right _ hε)
  exact cadlagModulus_le_of_partition f (by linarith [cadlagModulus_nonneg f d]) p
    hp0 hpT hp (fun i => hδd.trans_lt (hgap i))
    (fun i s u hs hs' hu hu' => (hosc i s u hs hs' hu hu').le)

private theorem modulus_le_of_partition_timeChange [MetricSpace E] (f g : D T E)
    {n : ℕ} (x : Fin (n + 1) → Icc (0 : ℝ) T)
    (hx0 : (x 0 : ℝ) = 0) (hxT : (x (Fin.last n) : ℝ) = T) (hx : StrictMono x)
    {d a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hgap : ∀ i : Fin n, d < (x i.succ : ℝ) - x i.castSucc)
    (hf : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
      x i.castSucc ≤ s → s < x i.succ → x i.castSucc ≤ t → t < x i.succ →
        dist (f s) (f t) ≤ a)
    (σ : TimeChange T) (hlog : σ.logSlope ≤ ENNReal.ofReal r)
    (hpath : ∀ t, dist (f t) (g (σ t)) ≤ b) :
    cadlagModulus g (Real.exp (-r) * d) ≤ a + 2 * b := by
  have hT : 0 ≤ T := (x 0).2.1.trans (x 0).2.2
  have hx0' : x 0 = ⟨0, le_rfl, hT⟩ := Subtype.ext hx0
  have hxT' : x (Fin.last n) = ⟨T, hT, le_rfl⟩ := Subtype.ext hxT
  apply cadlagModulus_le_of_partition g (by positivity) (fun i => (σ (x i) : ℝ))
    (by rw [hx0', TimeChange.apply_zero σ hT])
    (by rw [hxT', TimeChange.apply_top σ hT]) (σ.strictMono.comp hx)
  · intro i
    exact (mul_lt_mul_of_pos_left (hgap i) (Real.exp_pos _)).trans_le
      (σ.secant_bounds_of_logSlope_le hr hlog (hx i.castSucc_lt_succ)).1
  · intro i s t hs hs' ht ht'
    let v := σ.symm s
    let w := σ.symm t
    have hv : x i.castSucc ≤ v := by simpa [v] using σ.symm.monotone hs
    have hv' : v < x i.succ := by simpa [v] using σ.symm.strictMono hs'
    have hw : x i.castSucc ≤ w := by simpa [w] using σ.symm.monotone ht
    have hw' : w < x i.succ := by simpa [w] using σ.symm.strictMono ht'
    have hsv : dist (g s) (f v) ≤ b := by simpa [v, dist_comm] using hpath v
    have hwt : dist (f w) (g t) ≤ b := by simpa [w] using hpath w
    have hfw := hf i v w hv hv' hw hw'
    calc
      dist (g s) (g t) ≤ dist (g s) (f v) + dist (f v) (f w) +
          dist (f w) (g t) := dist_triangle4 _ _ _ _
      _ ≤ a + 2 * b := by linarith

private theorem exists_modulus_bound_nhds [MetricSpace E] (f : D T E)
    (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ d, 0 < d ∧ d < T ∧ ∃ U, IsOpen U ∧ f ∈ U ∧
      ∀ g ∈ U, cadlagModulus g d ≤ ε := by
  have hlim := (tendsto_cadlagModulus f).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))
  have hpos : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
  have hlt : ∀ᶠ d in 𝓝[>] (0 : ℝ), d < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  obtain ⟨d, hd, hdT, hsmall⟩ := (hpos.and (hlt.and hlim)).exists
  obtain ⟨n, p, hp0, hpT, hp, hgap, hosc⟩ :=
    exists_partition_of_cadlagModulus_lt f hd hdT hsmall
  let x : Fin (n + 1) → Icc (0 : ℝ) T := fun i => ⟨p i, by
    constructor
    · rw [← hp0]; exact hp.monotone (Fin.zero_le i)
    · rw [← hpT]; exact hp.monotone (Fin.le_last i)⟩
  let r := ε / 8
  have hr : 0 < r := by dsimp [r]; positivity
  let d' := Real.exp (-r) * d
  have hd' : 0 < d' := mul_pos (Real.exp_pos _) hd
  have hd'T : d' < T := by
    have hexp : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (mul_le_of_le_one_left hd.le hexp).trans_lt hdT
  let U := toDComplete ⁻¹' Metric.ball (toDComplete f) r
  refine ⟨d', hd', hd'T, U, Metric.isOpen_ball.preimage toDComplete.continuous, ?_, ?_⟩
  · change dist (toDComplete f) (toDComplete f) < r
    simpa using hr
  · intro g hg
    have hdist : j1CompleteDist f g < r := by
      change j1CompleteDist g f < r at hg
      rwa [j1CompleteDist_comm] at hg
    obtain ⟨σ, hcost⟩ := exists_completeCost_lt f g hdist
    have hlog : σ.logSlope ≤ ENNReal.ofReal r := (le_max_left _ _).trans hcost.le
    have hpath (t) : dist (f t) (g (σ t)) ≤ r := by
      apply (ENNReal.ofReal_le_ofReal_iff hr.le).mp
      rw [← edist_dist]
      exact (le_iSup (fun s => edist (f s) (g (σ s))) t).trans
        ((le_max_right _ _).trans hcost.le)
    have hm := modulus_le_of_partition_timeChange f g x hp0 hpT hp
      (show 0 ≤ ε / 4 by linarith) hr.le hr.le hgap
      (fun i s t hs hs' ht ht' => (hosc i s t hs hs' ht ht').le) σ hlog hpath
    exact hm.trans (by dsimp [r]; linarith)

/-- On a compact set of càdlàg paths, the moduli vanish uniformly at small positive
thresholds strictly below a positive horizon. -/
theorem exists_uniform_cadlagModulus_of_isCompact [MetricSpace E] {A : Set (D T E)}
    (hA : IsCompact A) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ d, 0 < d ∧ d < T ∧ ∀ f ∈ A, cadlagModulus f d ≤ ε := by
  classical
  obtain hzero | ⟨f₀, hf₀⟩ := A.eq_empty_or_nonempty
  · exact ⟨T / 2, half_pos hT, half_lt_self hT, by simp [hzero]⟩
  choose d hd hdT U hU hmem hbound using fun f : A => exists_modulus_bound_nhds f.1 hT hε
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover U hU (fun f hf =>
    mem_iUnion.mpr ⟨⟨f, hf⟩, hmem ⟨f, hf⟩⟩)
  obtain ⟨f, hfs, _⟩ := mem_iUnion₂.mp (hs hf₀)
  have hsne : s.Nonempty := ⟨f, hfs⟩
  let d₀ := s.inf' hsne d
  have hd₀ : 0 < d₀ := (Finset.lt_inf'_iff hsne).mpr (fun i _ => hd i)
  have hd₀T : d₀ < T := (Finset.inf'_le d hfs).trans_lt (hdT f)
  refine ⟨d₀, hd₀, hd₀T, fun g hg => ?_⟩
  obtain ⟨f, hfs, hgf⟩ := mem_iUnion₂.mp (hs hg)
  exact (cadlagModulus_mono g (Finset.inf'_le d hfs) (hd f) (hdT f)).trans
    (hbound f g hgf)

/-- The values of all paths in a compact set lie in a single bounded subset of the
state space. -/
theorem exists_isBounded_values_of_isCompact [MetricSpace E] {A : Set (D T E)}
    (hA : IsCompact A) : ∃ K : Set E, Bornology.IsBounded K ∧ ∀ f ∈ A, ∀ t, f t ∈ K := by
  have hc : IsCompact (toDComplete '' A) := hA.image toDComplete.continuous
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp hc.totallyBounded 1 zero_lt_one
  let K := ⋃ c ∈ C, Metric.thickening 1 (range (toDComplete.symm c : D T E))
  have hK : Bornology.IsBounded K := Bornology.isBounded_biUnion hC |>.mpr
    (fun c _ => (isBounded_range (toDComplete.symm c : D T E)).thickening)
  refine ⟨K, hK, fun f hf t => ?_⟩
  obtain ⟨c, hc, hfc⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem toDComplete hf))
  have hdist : j1CompleteDist f (toDComplete.symm c) < 1 := hfc
  obtain ⟨σ, hσ⟩ := exists_completeCost_lt f (toDComplete.symm c) hdist
  apply mem_iUnion₂.mpr
  refine ⟨c, hc, Metric.mem_thickening_iff_exists_edist_lt _ _ |>.mpr ?_⟩
  refine ⟨(toDComplete.symm c : D T E) (σ t), mem_range_self _, ?_⟩
  exact (le_iSup (fun s => edist (f s) ((toDComplete.symm c : D T E) (σ s))) t).trans_lt
    ((le_max_right _ _).trans_lt hσ)

private theorem exists_compact_initial_segment [MetricSpace E]
    [MeasurableSpace (D T E)] (P : ℕ → Measure (D T E))
    (htight : ∀ n, IsTightMeasureSet {P n}) (N : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ C : Set (D T E), IsCompact C ∧ ∀ n < N, P n Cᶜ ≤ η := by
  classical
  have h (n : Fin N) : ∃ C : Set (D T E), IsCompact C ∧ P n Cᶜ ≤ η := by
    obtain ⟨C, hC, hprob⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (htight n) η hη
    exact ⟨C, hC, hprob _ (mem_singleton _)⟩
  choose C hC hprob using h
  refine ⟨⋃ n, C n, isCompact_iUnion hC, fun n hn => ?_⟩
  exact (measure_mono (compl_subset_compl.mpr (subset_iUnion C ⟨n, hn⟩))).trans
    (hprob ⟨n, hn⟩)

/-- Tightness criterion in `D` in Billingsley's eventual form (Theorem 13.2, sufficiency): the
bounds are only required for large `n`, and each single law is assumed tight (for example the
law of a step path, a continuous image of a law on `ℝⁿ`). -/
theorem isTightMeasureSet_of_cadlagModulus_eventually [MetricSpace E] [ProperSpace E]
    [MeasurableSpace (D T E)] (P : ℕ → Measure (D T E))
    (htight : ∀ n, IsTightMeasureSet {P n})
    (hbdd : ∀ η > 0, ∃ K : Set E, Bornology.IsBounded K ∧
      ∃ N, ∀ n ≥ N, P n {f | ∃ t, f t ∉ K} ≤ ENNReal.ofReal η)
    (hmod : ∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∃ N, ∀ n ≥ N, P n {f | ε < cadlagModulus f δ} ≤ ENNReal.ofReal η) :
    IsTightMeasureSet (Set.range P) := by
  apply isTightMeasureSet_of_cadlagModulus P
  · intro η hη
    obtain ⟨K, hK, N, htail⟩ := hbdd η hη
    obtain ⟨C, hC, hprob⟩ := exists_compact_initial_segment P htight N
      (ENNReal.ofReal_pos.mpr hη)
    obtain ⟨L, hL, hvalues⟩ := exists_isBounded_values_of_isCompact hC
    refine ⟨K ∪ L, hK.union hL, fun n => ?_⟩
    by_cases hn : N ≤ n
    · exact (measure_mono (by
        rintro f ⟨t, ht⟩
        exact ⟨t, fun h => ht (Or.inl h)⟩)).trans (htail n hn)
    · apply le_trans (measure_mono ?_) (hprob n (lt_of_not_ge hn))
      rintro f ⟨t, ht⟩ hf
      exact ht (Or.inr (hvalues f hf t))
  · intro ε hε η hη
    obtain ⟨δ, hδ, hδT, N, htail⟩ := hmod ε hε η hη
    obtain ⟨C, hC, hprob⟩ := exists_compact_initial_segment P htight N
      (ENNReal.ofReal_pos.mpr hη)
    obtain ⟨d, hd, hdT, hsmall⟩ := exists_uniform_cadlagModulus_of_isCompact hC
      (hδ.trans hδT) hε
    refine ⟨min δ d, lt_min hδ hd, (min_le_left _ _).trans_lt hδT, fun n => ?_⟩
    by_cases hn : N ≤ n
    · apply le_trans (measure_mono ?_) (htail n hn)
      intro f hf
      exact hf.trans_le (cadlagModulus_mono f (min_le_left _ _) hδ hδT)
    · apply le_trans (measure_mono ?_) (hprob n (lt_of_not_ge hn))
      intro f hf hfC
      exact (not_lt_of_ge ((cadlagModulus_mono f (min_le_right _ _) hd hdT).trans
        (hsmall f hfC))) hf

end BGW.Skorokhod
