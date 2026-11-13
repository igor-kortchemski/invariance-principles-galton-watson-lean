/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimit
public import BGW.StableTrees.DiscreteForest
public import BGW.Skorokhod.VervaatStep
public import BGW.Skorokhod.VervaatMeasurable
public import BGW.Skorokhod.MeasurableMaps
public import BGW.LocallyFinite.ExcursionLaw

/-!
# Discrete walk bridges

Offspring vectors, their conditioned path laws and the finite cyclic identities.
The path retains its terminal value `-1 / B n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest (degreeWeight prefixWalk exactTreeLaw)

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-! ## 1. The offspring vector, its path, and the two conditioned laws -/

/-- The product law of an offspring vector `(ω_0, ..., ω_{n-1})`. -/
noncomputable def offspringVec (μ : PMF ℕ) (n : ℕ) : Measure (Fin n → ℕ) :=
  Measure.pi (fun _ : Fin n => μ.toMeasure)

instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (offspringVec μ n) := by
  unfold offspringVec
  infer_instance

/-- The rescaled Łukasiewicz path `t ↦ W_{⌊n t⌋} / B n` of an offspring vector. -/
noncomputable def vecPath (B : ℕ → ℝ) (n : ℕ) (ω : Fin n → ℕ) : D 1 ℝ :=
  stepPath (stepWord ω) (B n)

/-- The path map is measurable (countable discrete source). -/
theorem measurable_vecPath (B : ℕ → ℝ) (n : ℕ) : Measurable (vecPath B n) := by
  exact measurable_of_countable _

/-- Value at the terminal time of the path of a bridge vector: `-1 / B n`. -/
theorem vecPath_one_of_mem_countBridges {B : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    {ω : Fin n → ℕ} (hω : ω ∈ countBridges n) :
    vecPath B n ω ⟨1, zero_le_one, le_rfl⟩ = -1 / B n := by
  have _ := hn
  have hw := (stepWord_mem_bridgeWords_iff ω).mpr hω
  change (((stepWord ω).take ⌊((stepWord ω).length : ℝ) * 1⌋₊).sum : ℝ) / B n = _
  rw [mul_one, Nat.floor_natCast, List.take_length, hw.2.2]
  simp

/-- The offspring vector conditioned on `A`; the Dirac law at `0` when the conditioning event
has mass zero (so that no proof field uses an unproved positivity fact). -/
noncomputable def conditionedVecOrJunk (μ : PMF ℕ) (n : ℕ)
    (A : Set (Fin n → ℕ)) : ProbabilityMeasure (Fin n → ℕ) :=
  if hP : IsProbabilityMeasure ((offspringVec μ n)[|A]) then
    ⟨(offspringVec μ n)[|A], hP⟩
  else
    ⟨Measure.dirac (fun _ => 0), inferInstance⟩

/-- **The walk bridge law**: the offspring vector conditioned on `∑ ω_i = n - 1`, pushed through
`vecPath` (totalized; `hn` excludes the junk branch, see the positivity theorems below). -/
noncomputable def walkBridgeLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (_hn : Admissible μ n) : ProbabilityMeasure (D 1 ℝ) :=
  (conditionedVecOrJunk μ n (countBridges n)).map (vecPath B n)

/-- **The exact-size walk law**: the offspring vector conditioned on being a tree excursion
(Łukasiewicz path of a BGW tree of size `n`), pushed through `vecPath` (totalized). -/
noncomputable def exactWalkLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (_hn : Admissible μ n) : ProbabilityMeasure (D 1 ℝ) :=
  (conditionedVecOrJunk μ n (countExcursions n)).map (vecPath B n)

/-- Admissibility (K03: exact-size mass nonzero) is positivity of the bridge mass
(Kemperman: `P(bridge) = n P(ζ = n)`).  Not used by any definition. -/
theorem offspringVec_countBridges_ne_zero {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    offspringVec μ n (countBridges n) ≠ 0 := by
  apply (pi_countBridges_ne_zero_iff μ.toMeasure n).mpr
  refine ⟨?_, hn⟩
  intro hn0
  subst n
  exact hn (by simp [LocallyFinite.sizeEvent_zero])

/-- Admissibility is positivity of the excursion mass `P(excursion word) = P(ζ = n)`.
Not used by any definition. -/
theorem offspringVec_countExcursions_ne_zero {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    offspringVec μ n (countExcursions n) ≠ 0 := by
  exact (pi_countExcursions_ne_zero_iff μ.toMeasure n).mpr hn

/-- Off the junk branch the totalized law is the conditioned product law. -/
theorem coe_conditionedVecOrJunk (μ : PMF ℕ) (n : ℕ)
    (A : Set (Fin n → ℕ))
    (hA : offspringVec μ n A ≠ 0) :
    (conditionedVecOrJunk μ n A : Measure (Fin n → ℕ)) =
      (offspringVec μ n)[|A] := by
  classical
  have hP := cond_isProbabilityMeasure hA
  simp [conditionedVecOrJunk, hP]

/-- Law of the restriction of a path to `[0, a]`, `a ≤ 1`. -/
noncomputable def restrictLaw (a : ℝ≥0) (ha : a ≤ 1) (P : ProbabilityMeasure (D 1 ℝ)) :
    ProbabilityMeasure (D (a : ℝ) ℝ) :=
  P.map (BGW.Skorokhod.restrict (E := ℝ) (show (a : ℝ) ≤ 1 by exact_mod_cast ha))

/-- The value of a path on `[0, a]` at its last time `a`. -/
noncomputable def endValue (a : ℝ≥0) (x : D (a : ℝ) ℝ) : ℝ :=
  x ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩

/-- The rotation of an offspring vector at the Vervaat index of its step word. -/
noncomputable def rotateVec {n : ℕ} (ω : Fin n → ℕ) : Fin n → ℕ :=
  countsOfWord n ((stepWord ω).rotate (vervaatIndex (stepWord ω)))

/-- Rotation is a measurable map of the (countable, discrete) vector space. -/
theorem measurable_rotateVec (n : ℕ) : Measurable (rotateVec (n := n)) := by
  exact measurable_of_countable _

/-- Deterministic identity: on bridge vectors the càdlàg Vervaat map of the path is the path of
the rotated vector (`vervaatD_stepPath`, `stepWord_countsOfWord`), for positive norming. -/
theorem vervaatD_vecPath {B : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) (hB : 0 < B n)
    {ω : Fin n → ℕ} (hω : ω ∈ countBridges n) :
    vervaatD (vecPath B n ω) = vecPath B n (rotateVec ω) := by
  have _ := hn
  have hw := (stepWord_mem_bridgeWords_iff ω).mpr hω
  have hrot : stepWord (rotateVec ω) = (stepWord ω).rotate (vervaatIndex (stepWord ω)) :=
    stepWord_countsOfWord (by simp [stepWord])
      (fun j hj => hw.2.1 j (List.mem_rotate.mp hj))
  unfold vecPath
  rw [hrot]
  exact vervaatD_stepPath ⟨n, hn, hw.1.ge, by
    simpa only [← hw.1, List.take_length, hw.2.2] using (show (-1 : ℤ) < 0 by decide)⟩ hB

/-- A bridge vector rotated at the Vervaat index is a tree excursion (cycle lemma,
`exists_unique_rotate_isTreeExcursion`). -/
theorem rotateVec_mem_countExcursions {n : ℕ} (hn : 1 ≤ n) {ω : Fin n → ℕ}
    (hω : ω ∈ countBridges n) : rotateVec ω ∈ countExcursions n := by
  have _ := hn
  have hw := (stepWord_mem_bridgeWords_iff ω).mpr hω
  have hrot : stepWord (rotateVec ω) = (stepWord ω).rotate (vervaatIndex (stepWord ω)) :=
    stepWord_countsOfWord (by simp [stepWord])
      (fun j hj => hw.2.1 j (List.mem_rotate.mp hj))
  change IsTreeExcursion (stepWord (rotateVec ω))
  rw [hrot]
  exact isTreeExcursion_rotate_vervaatIndex hw


private theorem rotateVec_countsOfWord_rotate {n : ℕ} (t : PlaneTree) (ht : t.size = n)
    (i : Fin n) :
    rotateVec (countsOfWord n (t.increments.rotate i)) = countsOfWord n t.increments := by
  have hx : t.increments ∈ bridgeWords n := by
    simpa [ht] using PlaneTree.increments_mem_bridgeWords t
  have hy : t.increments.rotate i ∈ bridgeWords n :=
    ⟨by simp [hx.1], fun j hj => hx.2.1 j (List.mem_rotate.mp hj),
      (List.rotate_perm _ _).sum_eq.trans hx.2.2⟩
  have hw : stepWord (countsOfWord n (t.increments.rotate i)) = t.increments.rotate i :=
    stepWord_countsOfWord hy.1 hy.2.1
  have hg := isTreeExcursion_rotate_vervaatIndex hy
  rw [List.rotate_rotate] at hg
  have hmod : ((i : ℕ) + vervaatIndex (t.increments.rotate i)) % n = 0 := by
    apply (exists_unique_rotate_isTreeExcursion hx).unique
    · refine ⟨Nat.mod_lt _ (Fin.pos i), ?_⟩
      simpa only [← hx.1, List.rotate_mod] using hg
    · simpa using And.intro (Fin.pos i) (PlaneTree.isTreeExcursion_increments t)
  unfold rotateVec
  rw [hw, List.rotate_rotate, ← List.rotate_mod, hx.1, hmod, List.rotate_zero]

/-- **Cyclic law at the level of vectors**: the bridge-conditioned product law, rotated at the
Vervaat index, is the excursion-conditioned product law. -/
theorem map_rotateVec_cond_countBridges {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    ((offspringVec μ n)[|countBridges n]).map rotateVec =
      (offspringVec μ n)[|countExcursions n] := by
  have hn0 : n ≠ 0 := by
    intro h0
    subst n
    exact hn (by simp [LocallyFinite.sizeEvent_zero])
  unfold offspringVec
  ext A hA
  rw [Measure.map_apply (measurable_rotateVec n) hA]
  change (Measure.pi fun _ : Fin n => μ.toMeasure)[|countBridges n] (rotateVec ⁻¹' A) = _
  rw [cond_pi_countBridges_apply_eq_tsum, cond_pi_countExcursions_apply_eq_tsum,
    ENNReal.tsum_prod']
  apply tsum_congr
  intro t
  have he (i : Fin n) :
      (rotateVec ⁻¹' A).indicator (1 : (Fin n → ℕ) → ℝ≥0∞)
          (countsOfWord n (t.1.increments.rotate i)) =
        A.indicator 1 (countsOfWord n t.1.increments) := by
    change (if rotateVec (countsOfWord n (t.1.increments.rotate i)) ∈ A then 1 else 0) =
      (if countsOfWord n t.1.increments ∈ A then 1 else 0)
    rw [rotateVec_countsOfWord_rotate t.1 t.2 i]
  simp_rw [he]
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hn0)
    (ENNReal.natCast_ne_top n), one_mul]

/-- **Cyclic law at the level of paths (K06 second export)**: the Vervaat image of the discrete
walk bridge is the exact-size Łukasiewicz path law.  Positive norming is explicit. -/
theorem map_vervaatD_walkBridgeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : Admissible μ n)
    (hB : 0 < B n) :
    ((walkBridgeLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)).map vervaatD =
      ((exactWalkLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)) := by
  have hn1 : 1 ≤ n := by
    by_contra hn1
    have : n = 0 := by omega
    subst n
    exact hn (by simp [LocallyFinite.sizeEvent_zero])
  change ((conditionedVecOrJunk μ n (countBridges n) : Measure (Fin n → ℕ)).map
    (vecPath B n)).map vervaatD =
      (conditionedVecOrJunk μ n (countExcursions n) : Measure (Fin n → ℕ)).map (vecPath B n)
  rw [coe_conditionedVecOrJunk μ n _ (offspringVec_countBridges_ne_zero hn),
    coe_conditionedVecOrJunk μ n _ (offspringVec_countExcursions_ne_zero hn),
    Measure.map_map measurable_vervaatD (measurable_vecPath B n)]
  calc
    _ = ((offspringVec μ n)[|countBridges n]).map (vecPath B n ∘ rotateVec) := by
      apply Measure.map_congr
      exact ae_cond_of_forall_mem (Set.to_countable _).measurableSet
        (fun ω hω => vervaatD_vecPath hn1 hB hω)
    _ = (((offspringVec μ n)[|countBridges n]).map rotateVec).map (vecPath B n) := by
      rw [Measure.map_map (measurable_vecPath B n) (measurable_rotateVec n)]
    _ = _ := by rw [map_rotateVec_cond_countBridges hn]

/-- The Łukasiewicz step path `t ↦ W_{⌊n t⌋}/B n` of a finite tree (junk path `0` for
infinite trees), from its DFS increments. -/
noncomputable def treePath (B : ℕ → ℝ) (n : ℕ) (τ : BGW.LocallyFinite.Tree) : D 1 ℝ :=
  open scoped Classical in
  if h : BGW.LocallyFinite.FiniteVertices τ then
    stepPath (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).increments (B n)
  else stepPath [] (B n)

/-- The totalized tree path is measurable because finite trees form a countable set. -/
theorem measurable_treePath (B : ℕ → ℝ) (n : ℕ) : Measurable (treePath B n) := by
  apply (measurable_const (a := stepPath [] (B n))).measurable_of_countable_ne
  apply (Set.countable_range PlaneTree.toLocallyFinite).mono
  intro τ hτ
  by_contra hτfin
  have hi : ¬ LocallyFinite.FiniteVertices τ := by
    simpa only [LocallyFinite.range_toLocallyFinite, mem_ofPred_eq] using hτfin
  exact hτ (by simp [treePath, hi])

/-- The tree path evaluated on the finite-tree embedding is its increment step path. -/
theorem treePath_toLocallyFinite (B : ℕ → ℝ) (n : ℕ) (t : PlaneTree) :
    treePath B n t.toLocallyFinite = stepPath t.increments (B n) := by
  simp only [treePath, dite_eq_left t.finiteVertices_toLocallyFinite]
  change stepPath (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).increments
    (B n) = _
  rw [Equiv.symm_apply_apply]

private theorem exactTreeLaw_apply_eq_tsum {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n)
    (A : Set LocallyFinite.Tree) (hA : MeasurableSet A) :
    (exactTreeLaw μ n : Measure LocallyFinite.Tree) A =
      ∑' t : {t : PlaneTree // t.size = n},
        (LocallyFinite.bienaymeLaw μ.toMeasure)[|LocallyFinite.sizeEvent n]
          {t.1.toLocallyFinite} * A.indicator 1 t.1.toLocallyFinite := by
  have _ := hA
  rw [DiscreteForest.exactTreeLaw_toMeasure μ n hn]
  let P := (LocallyFinite.bienaymeLaw μ.toMeasure)[|LocallyFinite.sizeEvent n]
  have hs := ae_cond_mem (μ := LocallyFinite.bienaymeLaw μ.toMeasure)
    (LocallyFinite.measurableSet_sizeEvent n)
  have heq : P A = P (A ∩ LocallyFinite.sizeEvent n) := by
    apply measure_congr
    filter_upwards [hs] with τ hτ
    simp only [mem_inter_iff, hτ, and_true]
  rw [heq]
  have hset : A ∩ LocallyFinite.sizeEvent n =
      ⋃ t : {t : PlaneTree // t.size = n},
        if t.1.toLocallyFinite ∈ A then {t.1.toLocallyFinite} else ∅ := by
    ext τ
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨hτ, hsτ⟩
      obtain ⟨t, ht, rfl⟩ := (LocallyFinite.sizeEvent_eq_image n ▸ hsτ)
      exact ⟨⟨t, ht⟩, by simp [hτ]⟩
    · rintro ⟨t, hτ⟩
      split_ifs at hτ with htA
      · obtain rfl := hτ
        exact ⟨htA, (LocallyFinite.toLocallyFinite_mem_sizeEvent_iff _ _).mpr t.2⟩
      · exact hτ.elim
  rw [hset, measure_iUnion]
  · apply tsum_congr
    intro t
    by_cases htA : t.1.toLocallyFinite ∈ A <;> simp [htA, P]
  · intro t t' htt'
    have hd : Disjoint ({t.1.toLocallyFinite} : Set LocallyFinite.Tree)
        {t'.1.toLocallyFinite} :=
      Set.disjoint_singleton.mpr (fun h => htt'
        (Subtype.ext (PlaneTree.toLocallyFinite_injective h)))
    exact hd.mono (by dsimp only; split_ifs <;> simp) (by dsimp only; split_ifs <;> simp)
  · intro t
    split_ifs <;> measurability

/-- The exact-size walk law is the Łukasiewicz path of the exact-size BGW tree: one object. -/
theorem map_treePath_exactTreeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) :
    ((exactTreeLaw μ n : ProbabilityMeasure BGW.LocallyFinite.Tree) :
        Measure BGW.LocallyFinite.Tree).map (treePath B n) =
      ((exactWalkLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)) := by
  change _ = (conditionedVecOrJunk μ n (countExcursions n) : Measure (Fin n → ℕ)).map
    (vecPath B n)
  rw [coe_conditionedVecOrJunk μ n _ (offspringVec_countExcursions_ne_zero hn)]
  ext A hA
  rw [Measure.map_apply (measurable_treePath B n) hA,
    Measure.map_apply (measurable_vecPath B n) hA,
    exactTreeLaw_apply_eq_tsum hn _ ((measurable_treePath B n) hA)]
  change _ = (Measure.pi fun _ : Fin n => μ.toMeasure)[|countExcursions n]
    (vecPath B n ⁻¹' A)
  rw [cond_pi_countExcursions_apply_eq_tsum]
  apply tsum_congr
  intro t
  have hp : vecPath B n (countsOfWord n t.1.increments) = treePath B n t.1.toLocallyFinite := by
    rw [treePath_toLocallyFinite, vecPath, stepWord_countsOfWord_increments _ t.2]
  congr 1
  change (if treePath B n t.1.toLocallyFinite ∈ A then 1 else 0) =
    (if vecPath B n (countsOfWord n t.1.increments) ∈ A then 1 else 0)
  rw [hp]

end BGW.StableTrees.DiscreteBridge
