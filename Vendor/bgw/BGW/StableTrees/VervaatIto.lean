/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridge
public import BGW.StableTrees.ExactPrefix
public import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.StableBridgeMinimum
import BGW.StableTrees.StableLaw
import BGW.Skorokhod.MeasurableLaws
import BGW.Skorokhod.MeasurableJumps
import BGW.Skorokhod.RestrictContinuity
import BGW.Probability.WeakConvergence
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The Vervaat image of the stable bridge

A single discrete offspring witness identifies the Vervaat bridge limit with the normalized
Itô excursion law, by agreement of prefixes and the pinned terminal value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteBridge (offspringVec vecPath conditionedVecOrJunk walkBridgeLaw
  exactWalkLaw offspringVec_countBridges_ne_zero offspringVec_countExcursions_ne_zero restrictLaw)

namespace BGW.StableTrees.VervaatIto

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-! ## 1. Adapters to the sealed discrete bridge and prefix results -/

instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (offspringVec μ n) := by
  unfold offspringVec
  infer_instance

/-- (K06 statement) **Walk bridge invariance principle**. -/
theorem tendsto_walkBridgeLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => walkBridgeLaw μ B (q k) (hq k)) atTop (𝓝 (stableBridgeLaw θ)) := by
  exact DiscreteBridge.tendsto_walkBridgeLaw h hqtop hq

/-- (K06 statement) **Cyclic law**: the Vervaat image of the discrete walk bridge is the
exact-size Łukasiewicz path law. -/
theorem map_vervaatD_walkBridgeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : Admissible μ n)
    (hB : 0 < B n) :
    ((walkBridgeLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)).map vervaatD =
      ((exactWalkLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)) := by
  exact DiscreteBridge.map_vervaatD_walkBridgeLaw hn hB

-- Definitional ADAPTATION of contract CT8_K07_ExactSizePrefixes `tendsto_exactWalkLaw_prefix`
-- (not a literal copy): K07's `exactWalkPrefixLaw` is unfolded to `restrictLaw ... exactWalkLaw`.
/-- (K07 statement) **Exact-size walk prefixes**: the restriction of the exact-size path law to
`[0,a]` converges to the unit-excursion prefix. -/
theorem tendsto_exactWalkLaw_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => restrictLaw a ha.2.le (exactWalkLaw μ B (q k) (hq k))) atTop
      (𝓝 ((unitExcursionLaw θ).map (excursionRestrict a))) := by
  exact ExactPrefix.tendsto_exactWalkLaw_prefix h hqtop hq a ha

/-! ## 2. The single witness -/

/-- **One witness** for the whole identification: an offspring law, a norming, the stable
domain proof and an unbounded admissible sequence of sizes, all chosen once. -/
structure DiscreteWitness (θ : ℝ) where
  /-- The offspring law. -/
  μ : PMF ℕ
  /-- The norming sequence. -/
  B : ℕ → ℝ
  /-- Attraction to the spectrally positive `θ`-stable law. -/
  h : StableDomain μ θ B
  /-- The sample sizes. -/
  q : ℕ → ℕ
  /-- The sizes are unbounded. -/
  hqtop : Tendsto q atTop atTop
  /-- The sizes are admissible: `P(ζ = q k) ≠ 0`. -/
  hq : ∀ k, Admissible μ (q k)

/-- The witness exists for every `1 < θ ≤ 2` (`exists_stableDomain`, `sizeProb_pos_iff`:
choose `q k = 1 + d * (N + k + 1)`, `d = Scalar.latticeSpan μ`, beyond the lattice
threshold `N`; then `q k ≡ 1 mod d` and `N ≤ q k`). -/
theorem exists_discreteWitness {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Nonempty (DiscreteWitness θ) := by
  obtain ⟨μ, B, h⟩ := exists_stableDomain hθ
  obtain ⟨N, hN⟩ := Attraction.sizeProb_pos_iff h
  let d := Scalar.latticeSpan μ
  have hd : 1 ≤ d := Scalar.latticeSpan_pos h.critical h.nondegenerate
  let q : ℕ → ℕ := fun k => 1 + d * (N + k + 1)
  have hbound (k : ℕ) : N + k + 1 ≤ q k := by
    have := Nat.mul_le_mul_right (N + k + 1) hd
    dsimp [q]
    omega
  refine ⟨⟨μ, B, h, q, ?_, ?_⟩⟩
  · apply tendsto_atTop_mono (fun k => ?_) tendsto_id
    exact (by omega : k ≤ N + k + 1).trans (hbound k)
  · intro k
    apply (hN (q k) (by have := hbound k; omega)).2
    refine ⟨(N + k + 1 : ℕ), ?_⟩
    dsimp [q, d]
    ring

/-! ## 3. The Vervaat image and the full-path limit -/

/-- The Vervaat image `(stableBridgeLaw θ).map vervaatD` as a probability measure. -/
noncomputable def vervaatImage (θ : ℝ) : ProbabilityMeasure (D 1 ℝ) :=
  (stableBridgeLaw θ).map vervaatD

/-- **Full-path limit of the transformed walk bridge**: along the witness the exact-size walk
laws converge to the Vervaat image of the stable bridge.  K06 convergence, the a.s.
continuity of `vervaatD` at the bridge (`stableBridgeLaw_ae_continuousAt_vervaatD`), the
continuous mapping theorem, and the cyclic law `map_vervaatD_walkBridgeLaw`.  The terminal
value of the paths is `-1/B n`; nothing is assumed about the limit at time `1`. -/
theorem tendsto_exactWalkLaw_vervaatImage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (w : DiscreteWitness θ) :
    Tendsto (fun k => exactWalkLaw w.μ w.B (w.q k) (w.hq k)) atTop (𝓝 (vervaatImage θ)) := by
  have ht := BGW.Probability.tendsto_map_of_ae_continuousAt
    (tendsto_walkBridgeLaw w.h w.hqtop w.hq)
    (fun _ => measurable_vervaatD.aemeasurable)
    (stableBridgeLaw_ae_continuousAt_vervaatD hθ)
  have he (k : ℕ) : (walkBridgeLaw w.μ w.B (w.q k) (w.hq k)).map vervaatD =
      exactWalkLaw w.μ w.B (w.q k) (w.hq k) := by
    apply Subtype.ext
    apply map_vervaatD_walkBridgeLaw (w.hq k)
    apply w.h.pos
    have hn := w.hq k
    by_contra hn0
    have hz : w.q k = 0 := by omega
    exact hn (by simp [hz, LocallyFinite.sizeEvent_zero])
  simpa only [he, vervaatImage] using ht

/-! ## 4. Prefixes on a dense set of times and the terminal coordinate -/

/-- The time `a ∈ [0,1]` as a point of the domain of `D 1 ℝ`. -/
def timePoint (a : ℝ≥0) (ha : a ≤ 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(a : ℝ), a.coe_nonneg, by exact_mod_cast ha⟩

/-- `P` has no fixed discontinuity at `t`: almost every path is continuous at `t`. -/
def NoFixedDiscontinuity (P : ProbabilityMeasure (D 1 ℝ)) (t : Set.Icc (0 : ℝ) 1) : Prop :=
  (P : Measure (D 1 ℝ)) {f | ¬ ContinuousAt f t} = 0

/-- A probability law on `D[0,1]` has at most countably many fixed discontinuities. -/
theorem countable_fixedDiscontinuities (P : ProbabilityMeasure (D 1 ℝ)) :
    {t : Set.Icc (0 : ℝ) 1 | ¬ NoFixedDiscontinuity P t}.Countable := by
  apply (countable_setOf_measure_jump_ne_zero P).mono
  intro t ht hz
  apply ht
  change (P : Measure (D 1 ℝ)) {f | ¬ ContinuousAt f t} = 0
  apply measure_mono_null (fun f hf => ?_) hz
  exact fun he => hf (continuousAt_of_eq_leftLim f he.symm)

/-- A dense set of cutoff times outside the fixed discontinuities of the Vervaat image
(`countable_fixedDiscontinuities` and density of the complement of a countable set). -/
theorem exists_dense_noFixedDiscontinuity_times (θ : ℝ) :
    ∃ A : Set ℝ≥0, (∀ a ∈ A, a ∈ Ioo (0 : ℝ≥0) 1) ∧
      Ioo (0 : ℝ) 1 ⊆ closure (((↑) : ℝ≥0 → ℝ) '' A) ∧
      ∀ a ∈ A, ∀ ha : a ≤ 1, NoFixedDiscontinuity (vervaatImage θ) (timePoint a ha) := by
  let C := {t : Set.Icc (0 : ℝ) 1 | ¬ NoFixedDiscontinuity (vervaatImage θ) t}
  have hc : (((↑) : Set.Icc (0 : ℝ) 1 → ℝ) '' C).Countable :=
    (countable_fixedDiscontinuities (vervaatImage θ)).image _
  let A := {a : ℝ≥0 | a ∈ Ioo (0 : ℝ≥0) 1 ∧
    ∀ ha : a ≤ 1, NoFixedDiscontinuity (vervaatImage θ) (timePoint a ha)}
  refine ⟨A, fun a ha => ha.1, ?_, fun a ha => ha.2⟩
  intro x hx
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨y, ⟨hyU, hy⟩, hyC⟩ := (hc.dense_compl ℝ).inter_open_nonempty
    (U ∩ Ioo 0 1) (hU.inter isOpen_Ioo) ⟨x, hxU, hx⟩
  have hy0 : 0 ≤ y := hy.1.le
  refine ⟨y, hyU, ⟨⟨y, hy0⟩, ?_, rfl⟩⟩
  refine ⟨?_, ?_⟩
  · exact_mod_cast hy
  · intro ha
    by_contra hbad
    apply hyC
    exact ⟨timePoint ⟨y, hy0⟩ ha, hbad, rfl⟩

/-- **Equality of prefixes** (K06 + K07 on the same witness `w`, which is exposed here and passed
to `tendsto_exactWalkLaw_vervaatImage hθ w`): at every `a ∈ (0,1)` where the
Vervaat image has no fixed discontinuity, its restriction to `[0,a]` is the unit-excursion
prefix.  The same sequence `E_k = exactWalkLaw` converges to both (CMT for `restrict`
at continuity points and K07). -/
theorem restrictLaw_vervaatImage_eq_unitPrefix {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (w : DiscreteWitness θ) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    (hcont : NoFixedDiscontinuity (vervaatImage θ) (timePoint a ha.2.le)) :
    restrictLaw a ha.2.le (vervaatImage θ) =
      (unitExcursionLaw θ).map (excursionRestrict a) := by
  have hca : ∀ᵐ (f : D 1 ℝ) ∂(vervaatImage θ : Measure (D 1 ℝ)),
      ContinuousAt f (timePoint a ha.2.le) := ae_iff.mpr hcont
  have haR : (a : ℝ) ≤ 1 := by exact_mod_cast ha.2.le
  have ht := BGW.Probability.tendsto_map_of_ae_continuousAt
    (h := restrict haR) (tendsto_exactWalkLaw_vervaatImage hθ w)
    (fun _ => (measurable_restrict haR).aemeasurable)
    (hca.mono fun f hf => continuousAt_restrict a.coe_nonneg haR hf)
  exact tendsto_nhds_unique ht (tendsto_exactWalkLaw_prefix w.h w.hqtop w.hq a ha)

/-- Both laws vanish a.s. at the terminal time (`stableBridgeLaw_ae_vervaat_endpoints`). -/
theorem ae_vervaatImage_terminal_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(vervaatImage θ : Measure (D 1 ℝ)), f ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  rw [vervaatImage, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff measurable_vervaatD.aemeasurable
    (measurableSet_eq_fun (measurable_eval _) measurable_const)).mpr
  exact (stableBridgeLaw_ae_vervaat_endpoints hθ).mono fun _ hf => hf.2.1

/-- **Uniqueness with the terminal coordinate**: two laws on `D[0,1]` that agree on the prefixes
`[0,a]` for `a` in a set of times dense in `(0,1)`, and are both a.s. `0` at time `1`, are equal
using `ext_of_finiteDimensional`: every finite collection of nonterminal times fits below a
cutoff in `A`, and its joint law is obtained by adjoining the terminal constant `0`. -/
theorem eq_of_restrict_eq_of_terminal_zero (P Q : ProbabilityMeasure (D 1 ℝ))
    (A : Set ℝ≥0) (hA : ∀ a ∈ A, a ∈ Ioo (0 : ℝ≥0) 1)
    (hdense : Ioo (0 : ℝ) 1 ⊆ closure (((↑) : ℝ≥0 → ℝ) '' A))
    (h : ∀ (a : ℝ≥0) (ha : a ∈ A),
      restrictLaw a (hA a ha).2.le P = restrictLaw a (hA a ha).2.le Q)
    (hP : ∀ᵐ f ∂(P : Measure (D 1 ℝ)), f ⟨1, zero_le_one, le_rfl⟩ = 0)
    (hQ : ∀ᵐ f ∂(Q : Measure (D 1 ℝ)), f ⟨1, zero_le_one, le_rfl⟩ = 0) : P = Q := by
  classical
  have hcut (b : ℝ≥0) (hb : b < 1) : ∃ a ∈ A, b < a := by
    let x : ℝ := ((b : ℝ) + 1) / 2
    have hbR : (b : ℝ) < 1 := by exact_mod_cast hb
    have hx : x ∈ Ioo (0 : ℝ) 1 := by
      dsimp [x]
      constructor <;> linarith [b.coe_nonneg]
    obtain ⟨y, hy, a, ha, hya⟩ := mem_closure_iff.mp (hdense hx)
      (Ioi (b : ℝ)) isOpen_Ioi (by change (b : ℝ) < x; dsimp only [x]; linarith)
    refine ⟨a, ha, ?_⟩
    rw [← hya] at hy
    exact_mod_cast hy
  apply ext_of_finiteDimensional dense_univ (by norm_num) (mem_univ _)
  intro s _
  let v : Set.Icc (0 : ℝ) 1 → ℝ≥0 := fun t => if (t : ℝ) < 1 then ⟨t, t.2.1⟩ else 0
  let b : ℝ≥0 := s.sup v
  have hb : b < 1 := by
    apply (Finset.sup_lt_iff (show (0 : ℝ≥0) < 1 by norm_num)).mpr
    intro t _
    change v t < 1
    by_cases ht : (t : ℝ) < 1
    · simp only [v, ht, ↓reduceIte]
      exact_mod_cast ht
    · simp only [v, ht, ↓reduceIte]
      norm_num
  obtain ⟨a, ha, hba⟩ := hcut b hb
  have hat : (a : ℝ) ≤ 1 := by exact_mod_cast (hA a ha).2.le
  have hbound (t : s) (ht : (t.val : ℝ) < 1) : (t.val : ℝ) ≤ a := by
    have hh : v t.val ≤ b := Finset.le_sup (f := v) t.property
    simp only [v, ht, ↓reduceIte] at hh
    exact_mod_cast hh.trans hba.le
  let G : D (a : ℝ) ℝ → s → ℝ := fun x t =>
    if ht : (t.val : ℝ) < 1 then x ⟨t.val, t.val.2.1, hbound t ht⟩ else 0
  have hG : Measurable G := Measurable.of_eval fun t => by
    dsimp [G]
    split_ifs
    · exact measurable_eval _
    · exact measurable_const
  have he (f : D 1 ℝ) (hf : f ⟨1, zero_le_one, le_rfl⟩ = 0) :
      (fun t : s => f t) = G (restrict hat f) := by
    funext t
    dsimp [G]
    split_ifs with ht
    · rfl
    · have ht1 : t.val = (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) :=
        Subtype.ext (le_antisymm t.val.2.2 (not_lt.mp ht))
      exact ht1 ▸ hf
  have hm (R : ProbabilityMeasure (D 1 ℝ))
      (hR : ∀ᵐ f ∂(R : Measure (D 1 ℝ)), f ⟨1, zero_le_one, le_rfl⟩ = 0) :
      R.map (fun f : D 1 ℝ => fun t : s => f t) =
        (restrictLaw a (hA a ha).2.le R).map G := by
    apply ProbabilityMeasure.toMeasure_injective
    unfold restrictLaw
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map hG (measurable_restrict hat)]
    exact Measure.map_congr (hR.mono fun f hf => he f hf)
  rw [hm P hP, hm Q hQ, h a ha]

/-! ## 5. C35 -/

/-- **C35, probability-measure form**: the Vervaat image of the stable bridge is the unit
excursion law. -/
theorem vervaatImage_eq_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    vervaatImage θ = levyExcLaw θ := by
  obtain ⟨w⟩ := exists_discreteWitness hθ
  obtain ⟨A, hA, hdense, hcont⟩ := exists_dense_noFixedDiscontinuity_times θ
  have hr (a : ℝ≥0) (ha : a ∈ A) :
      restrictLaw a (hA a ha).2.le (levyExcLaw θ) =
        (unitExcursionLaw θ).map (excursionRestrict a) := by
    apply ProbabilityMeasure.toMeasure_injective
    have haR : (a : ℝ) ≤ 1 := by exact_mod_cast (hA a ha).2.le
    change ((unitExcursionLaw θ : Measure Excursion).map (excursionRestrict 1)).map
      (restrict haR) = (unitExcursionLaw θ : Measure Excursion).map (excursionRestrict a)
    exact Measure.map_map (measurable_restrict haR) (measurable_excursionRestrict 1)
  apply eq_of_restrict_eq_of_terminal_zero _ _ A hA hdense
  · intro a ha
    rw [hr a ha]
    exact restrictLaw_vervaatImage_eq_unitPrefix hθ w a (hA a ha) (hcont a ha _)
  · exact ae_vervaatImage_terminal_zero hθ
  · exact (levyExcLaw_endpoints_pos hθ).mono fun _ hf => hf.2.2.1

/-- **C35 (K08 main theorem)**: for `1 < θ ≤ 2`, the Vervaat transform of the stable bridge has
the law of the normalized Itô excursion (`levyExcLaw θ`).  Statement as in the blueprint. -/
theorem map_vervaatD_stableBridgeLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ((stableBridgeLaw θ : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)).map vervaatD =
      (levyExcLaw θ : Measure (D 1 ℝ)) := by
  exact congrArg (fun P : ProbabilityMeasure (D 1 ℝ) => (P : Measure (D 1 ℝ)))
    (vervaatImage_eq_levyExcLaw hθ)

end BGW.StableTrees.VervaatIto
