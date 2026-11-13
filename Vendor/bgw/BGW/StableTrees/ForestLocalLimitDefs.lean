/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.Defs
public import BGW.StableTrees.KendallAdapter

/-!
# Forest masses and prefix weights

Canonical forest mass, inclusive tail and exact-prefix weight definitions.
The probability identities retain extinction and admissibility hypotheses explicitly.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace BGW.StableTrees

open BGW.LocallyFinite (bienaymeLaw sizeEvent)

/-- Admissible size: the exact-size mass `P[ζ = n]` is nonzero. -/
def Admissible (μ : PMF ℕ) (n : ℕ) : Prop := bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0

/-- `f_j(r)`: probability that a `j`-forest of Bienaymé trees has `r` vertices. -/
noncomputable def forestMass (μ : PMF ℕ) (j r : ℕ) : ℝ := (BGW.forestWeight μ j r).toReal

/-- `G_j(r) = ∑_{k ≥ r} f_j(k)`: probability that a `j`-forest has at least `r` vertices. -/
noncomputable def forestTail (μ : PMF ℕ) (j r : ℕ) : ℝ :=
  ∑' k : ℕ, (Set.Ici r).indicator (fun k => forestMass μ j k) k

/-- Discrete RN weight `R_n(m,j) = f_j(n-m)/G_j(n-m) * G_1(n)/f_1(n)` from the tail-conditioned
law to the exact-size law, at prefix length `m < n` with `j = W_m + 1` (totalized division). -/
noncomputable def exactPrefixWeight (μ : PMF ℕ) (n m j : ℕ) : ℝ :=
  forestMass μ j (n - m) / forestTail μ j (n - m) *
    (forestTail μ 1 n / forestMass μ 1 n)

/-- `f_1(n) = P[ζ = n]`. -/
theorem forestMass_one_eq_sizeProb (μ : PMF ℕ) (n : ℕ) :
    forestMass μ 1 n = (bienaymeLaw μ.toMeasure).real (sizeEvent n) := by
  have heq := BGW.LocallyFinite.forestWeight_one_eq_bienaymeLaw_sizeEvent μ.toMeasure n
  simpa only [forestMass, measureReal_def,
    PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using
    congrArg ENNReal.toReal heq

/-- `G_1(n) = P[ζ ≥ n]` for a critical non-degenerate law. -/
theorem forestTail_one_eq_sizeGe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    forestTail μ 1 n = (bienaymeLaw μ.toMeasure).real (Attraction.sizeGeEvent n) := by
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure = 1 := by
    rw [lintegral_countable']
    simpa only [IsCritical,
      PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hc
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hae := BGW.LocallyFinite.ae_finiteVertices_bienaymeLaw μ.toMeasure hm.le hne'
  have heq : Attraction.sizeGeEvent n =ᵐ[bienaymeLaw μ.toMeasure]
      ⋃ k : ℕ, if n ≤ k then sizeEvent k else ∅ := by
    filter_upwards [hae] with T hT
    apply propext
    change (¬ BGW.LocallyFinite.FiniteVertices T ∨
      n ≤ {u | BGW.LocallyFinite.Present T u}.ncard) ↔ _
    constructor
    · intro h
      have hn := h.resolve_left (not_not_intro hT)
      exact mem_iUnion.2 ⟨_, by rw [ite_eq_left hn]; exact ⟨hT, rfl⟩⟩
    · intro h
      obtain ⟨k, hk⟩ := mem_iUnion.1 h
      by_cases hn : n ≤ k
      · rw [ite_eq_left hn] at hk
        exact Or.inr (hk.2.symm ▸ hn)
      · rw [ite_eq_right hn] at hk
        exact hk.elim
  have hdis : Pairwise (Function.onFun Disjoint
      (fun k : ℕ => if n ≤ k then sizeEvent k else ∅)) := by
    intro i j hij
    simp only [Function.onFun]
    split_ifs <;> try simp
    exact Set.disjoint_left.2 fun T hi hj => hij (hi.2.symm.trans hj.2)
  rw [measureReal_def, measure_congr heq, measure_iUnion hdis
    (fun k => by
      split_ifs
      · exact BGW.LocallyFinite.measurableSet_sizeEvent k
      · exact MeasurableSet.empty)]
  rw [ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  unfold forestTail
  apply tsum_congr
  intro k
  by_cases hk : n ≤ k
  · simp [hk, Set.indicator_of_mem, forestMass_one_eq_sizeProb, measureReal_def]
  · simp [hk]

/-- **Exact mass along an explicit unbounded admissible sequence:**
`q_k B_{q_k} f_1(q_k) → d p₁(0)` (false along all integers when `d > 1`). -/
theorem exactMass_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k : ℕ => (q k : ℝ) * B (q k) * forestMass μ 1 (q k)) atTop
      (𝓝 (Scalar.latticeSpan μ * Scalar.stableDensity θ 0)) := by
  obtain ⟨N₀, hN₀⟩ := Attraction.sizeProb_pos_iff h
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Attraction.sizeProb_lattice_asymp h (half_pos hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hqtop.eventually (eventually_ge_atTop (max N₀ N₁)))
  refine ⟨K, fun k hk => ?_⟩
  rw [Real.dist_eq, forestMass_one_eq_sizeProb]
  exact (hN₁ (q k) ((le_max_right _ _).trans (hK k hk))
    ((hN₀ (q k) ((le_max_left _ _).trans (hK k hk))).1 (hq k))).trans_lt
      (half_lt_self hε)

end BGW.StableTrees
