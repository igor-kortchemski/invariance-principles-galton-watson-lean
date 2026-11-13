/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.WalkCF
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The scalar walk on one product probability space

The product law of the increments is the coordinatewise image of independent
offspring counts. Its sum has the convolution law. Prefix and suffix events
are independent, with all split-time bounds explicit.

Adapted from `PoissonDeclumping/Cyclic/WalkBridge.lean`, `PoissonDeclumping/Bridge/WalkCalculus.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BGW.StableTrees.Scalar

/-- The product law of `n` independent increments with law `stepLaw μ`. -/
noncomputable def walkVecLaw (μ : PMF ℕ) (n : ℕ) : Measure (Fin n → ℤ) :=
  Measure.pi fun _ => stepLaw μ

instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (walkVecLaw μ n) := by
  unfold walkVecLaw
  infer_instance

theorem walkVecLaw_singleton (μ : PMF ℕ) (n : ℕ) (ω : Fin n → ℤ) :
    walkVecLaw μ n {ω} = ∏ i, stepLaw μ {ω i} := by
  rw [walkVecLaw, Measure.pi_singleton]

/-- Mapping each offspring count to `K - 1` gives the product increment law. -/
theorem map_offspring_pi (μ : PMF ℕ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ.toMeasure)).map
      (fun ω i => (ω i : ℤ) - 1) = walkVecLaw μ n := by
  rw [walkVecLaw, stepLaw]
  exact Measure.pi_map_pi (μ := fun _ : Fin n => μ.toMeasure)
    (f := fun _ : Fin n => fun k : ℕ => (k : ℤ) - 1)
    (fun _ => (measurable_of_countable (fun k : ℕ => (k : ℤ) - 1)).aemeasurable)

/-- **Bridge between the two walk laws.** The `m`-fold convolution `walkLaw μ m` is the law of
`S_m = X_1 + ⋯ + X_m` when `(X_1, …, X_m)` has the product law `walkVecLaw μ m`. -/
theorem walkLaw_eq_map_sum (μ : PMF ℕ) (m : ℕ) :
    walkLaw μ m = (walkVecLaw μ m).map (fun ω => ∑ i, ω i) := by
  induction m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [Measure.map_const, measure_univ, one_smul]
    rfl
  | succ m ih =>
    rw [walkLaw, Measure.conv, ih]
    set P := stepLaw μ
    have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => P) 0
    have hW : walkVecLaw μ (m + 1) =
        (P.prod (walkVecLaw μ m)).map (MeasurableEquiv.piFinSuccAbove (fun _ => ℤ) 0).symm := by
      rw [walkVecLaw, ← hpres.symm.map_eq]
      rfl
    have hprod : ((walkVecLaw μ m).map (fun ω => ∑ i, ω i)).prod P =
        ((walkVecLaw μ m).prod P).map (Prod.map (fun ω => ∑ i, ω i) id) := by
      rw [← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id, Measure.map_id]
    rw [hW, Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hprod,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      ← Measure.prod_swap, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext p
    simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Prod.map,
      Prod.fst_swap, Prod.snd_swap, id]
    rw [Fin.sum_univ_succAbove _ 0]
    simp [Fin.insertNthEquiv, add_comm]


theorem walkLaw_apply (μ : PMF ℕ) (m : ℕ) (s : Set ℤ) :
    walkLaw μ m s = walkVecLaw μ m {ω | ∑ i, ω i ∈ s} := by
  rw [walkLaw_eq_map_sum, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  rfl


/-- The convolution walk law is also the image of the original offspring-count product. -/
theorem walkLaw_eq_map_offspring_sum (μ : PMF ℕ) (n : ℕ) :
    walkLaw μ n = (Measure.pi (fun _ : Fin n => μ.toMeasure)).map
      (fun ω => ∑ i, ((ω i : ℤ) - 1)) := by
  rw [walkLaw_eq_map_sum, ← map_offspring_pi,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- **Independent blocks of increments.** Under the law of `(X_1, …, X_{m+k})`, the first `m`
increments and the last `k` increments are independent, with the laws of `(X_1, …, X_m)` and
`(X_1, …, X_k)`. -/
theorem walkVecLaw_map_split (μ : PMF ℕ) (m k : ℕ) :
    (walkVecLaw μ (m + k)).map
        (fun ω => ((fun i : Fin m => ω (Fin.castAdd k i)), (fun j : Fin k => ω (Fin.natAdd m j)))) =
      (walkVecLaw μ m).prod (walkVecLaw μ k) := by
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun ω : Fin (m + k) → ℤ =>
      ((fun i : Fin m => ω (Fin.castAdd k i)), (fun j : Fin k => ω (Fin.natAdd m j)))) ⁻¹'
        {(a, b)} = {Fin.append a b} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact Fin.append_castAdd_natAdd.symm
    · rintro rfl
      exact ⟨funext fun i => Fin.append_left a b i, funext fun j => Fin.append_right a b j⟩
  rw [hpre, ← Set.singleton_prod_singleton, Measure.prod_prod, walkVecLaw_singleton,
    walkVecLaw_singleton, walkVecLaw_singleton, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]


/-- Independence of a prefix block and the following increments:
`P(H(X_1..X_m), K(X_{m+1}..X_n)) = P(H(X_1..X_m)) P(K(X_1..X_{n-m}))`. -/
theorem walkVecLaw_take_inter_drop (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H K : List ℤ → Prop) :
    walkVecLaw μ n {ω | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m)} =
      walkVecLaw μ m {a | H (List.ofFn a)} * walkVecLaw μ (n - m) {b | K (List.ofFn b)} := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  have hset : {ω : Fin (m + k) → ℤ | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m)} =
      (fun ω : Fin (m + k) → ℤ => ((fun i : Fin m => ω (Fin.castAdd k i)),
        (fun j : Fin k => ω (Fin.natAdd m j)))) ⁻¹'
        ({a | H (List.ofFn a)} ×ˢ {b | K (List.ofFn b)}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod]
    rw [List.ofFn_add, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
    rfl
  rw [hset, ← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    walkVecLaw_map_split, Measure.prod_prod]


/-- A prefix has the product law of the corresponding length. -/
theorem walkVecLaw_take (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H : List ℤ → Prop) :
    walkVecLaw μ n {ω | H ((List.ofFn ω).take m)} =
      walkVecLaw μ m {a | H (List.ofFn a)} := by
  have h := walkVecLaw_take_inter_drop μ hmn H (fun _ => True)
  simpa only [and_true, Set.ofPred_true, measure_univ, mul_one] using h

end BGW.StableTrees.Scalar

