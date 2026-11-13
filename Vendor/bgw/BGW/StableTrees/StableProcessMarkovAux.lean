/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableProcess
public import BGW.Skorokhod.ShiftIncrement
public import Mathlib.Probability.Independence.Process.Basic

/-!
# Independence auxiliaries for the stable process

The increments of a stable Lévy law along strictly increasing times are independent with stable
marginals. From this, the restricted past and the future increment path are independent, and the
future increment path is again a stable Lévy law (J. Bertoin, *Lévy Processes*, Cambridge
University Press, 1996, Chapter I).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod

private noncomputable def initialSum {n : ℕ} (a : Fin (n + 1)) (x : Fin n → ℝ) : ℝ :=
  ∑ i, if i.succ ≤ a then x i else 0

private noncomputable def intervalSum {n : ℕ} (a b : Fin (n + 1)) (x : Fin n → ℝ) : ℝ :=
  ∑ i, if a ≤ i.castSucc ∧ i.succ ≤ b then x i else 0

private lemma initialSum_apply {n : ℕ} (a : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    initialSum a (fun i => f i.succ - f i.castSucc) = f a - f 0 := by
  classical
  induction a using Fin.cases with
  | zero => simp [initialSum]
  | succ a =>
      have hsum : initialSum a.succ (fun i => f i.succ - f i.castSucc) =
          ∑ i ≤ a, (f i.succ - f i.castSucc) := by
        simp [initialSum, Fin.succ_le_succ_iff, Finset.sum_ite, Finset.filter_ge_eq_Iic]
      rw [hsum, Fin.sum_Iic_sub]

private lemma intervalSum_eq {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) (x : Fin n → ℝ) :
    intervalSum a b x = initialSum b x - initialSum a x := by
  classical
  simp only [intervalSum, initialSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases Fin.succ_le_or_le_castSucc a i with hia | hai
  · have hib : i.succ ≤ b := hia.trans hab
    have hna : ¬a ≤ i.castSucc :=
      not_le_of_gt (lt_of_lt_of_le Fin.castSucc_lt_succ hia)
    simp [hia, hib, hna]
  · have hna : ¬i.succ ≤ a := by
      intro hia
      exact (not_lt_of_ge hia) (lt_of_le_of_lt hai Fin.castSucc_lt_succ)
    by_cases hib : i.succ ≤ b
    · simp [hai, hib, hna]
    · simp [hai, hib, hna]

/-- A single increment of a stable Lévy law has the corresponding stable law. -/
theorem IsStableLevyLaw.map_sub_eval {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) (r t : Set.Icc (0 : ℝ) T) (hrt : r < t) :
    Measure.map (fun f : D T ℝ => f t - f r) (P : Measure (D T ℝ)) =
      (stableLawAt θ ((t : ℝ) - r) : Measure ℝ) := by
  let v : Fin 2 → Set.Icc (0 : ℝ) T := ![r, t]
  have hv : StrictMono v := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hrt
  have hmap := congrArg (Measure.map (Function.eval (0 : Fin 1))) (hP.map_increments 1 v hv)
  change Measure.map (Function.eval (0 : Fin 1))
    (Measure.map (fun f : D T ℝ => fun i : Fin 1 => f (v i.succ) - f (v i.castSucc))
      (P : Measure (D T ℝ))) = _ at hmap
  have hmeas : Measurable (fun f : D T ℝ => fun i : Fin 1 =>
      f (v i.succ) - f (v i.castSucc)) := Measurable.of_eval fun i =>
    (measurable_eval _).sub (measurable_eval _)
  rw [Measure.map_map (measurable_pi_apply _) hmeas, Measure.pi_map_eval] at hmap
  simpa [v, Function.comp_def] using hmap

/-- The increments along strictly increasing times are independent. -/
theorem IsStableLevyLaw.iIndepFun_eval_sub_of_strictMono {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) (n : ℕ)
    (t : Fin (n + 1) → Set.Icc (0 : ℝ) T) (ht : StrictMono t) :
    iIndepFun (fun (i : Fin n) (f : D T ℝ) => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) := by
  have hmeas (i : Fin n) : Measurable (fun f : D T ℝ => f (t i.succ) - f (t i.castSucc)) :=
    (measurable_eval _).sub (measurable_eval _)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable),
    hP.map_increments n t ht]
  congr 1
  funext i
  exact (hP.map_sub_eval (t i.castSucc) (t i.succ) (ht Fin.castSucc_lt_succ)).symm

/-- Finite past evaluations are independent of finite future shifted evaluations. -/
private theorem IsStableLevyLaw.indepFun_finset_eval_shift {θ T s : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P)
    (hs : 0 ≤ s) (hsT : s ≤ T)
    (I : Finset {t : Set.Icc (0 : ℝ) T // (t : ℝ) ≤ s})
    (J : Finset (Set.Icc (0 : ℝ) (T - s))) :
    IndepFun (fun (f : D T ℝ) (i : I) => f i.1.1)
      (fun (f : D T ℝ) (j : J) => shiftIncrement hs hsT f j.1)
      (P : Measure (D T ℝ)) := by
  classical
  let U : Finset ℝ := ({0, s} ∪ I.image (fun i => (i.1 : ℝ))) ∪
    J.image (fun j : Set.Icc (0 : ℝ) (T - s) => s + (j : ℝ))
  have h0U : 0 ∈ U := by simp [U]
  have hsU : s ∈ U := by simp [U]
  have hIU (i : {t : Set.Icc (0 : ℝ) T // (t : ℝ) ≤ s}) (hi : i ∈ I) :
      (i.1 : ℝ) ∈ U := by
    simp only [U]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hJU (j : Set.Icc (0 : ℝ) (T - s)) (hj : j ∈ J) : s + (j : ℝ) ∈ U := by
    simp only [U]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hUb {x : ℝ} (hx : x ∈ U) : 0 ≤ x ∧ x ≤ T := by
    simp only [U, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at hx
    rcases hx with (((rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨j, hj, rfl⟩)
    · exact ⟨le_rfl, hs.trans hsT⟩
    · exact ⟨hs, hsT⟩
    · exact ⟨i.1.property.1, i.1.property.2⟩
    · exact ⟨add_nonneg hs j.property.1, by linarith [j.property.2]⟩
  have hUcard : 0 < U.card := Finset.card_pos.mpr ⟨0, h0U⟩
  let n := U.card - 1
  have hcard : U.card = n + 1 := by
    dsimp [n]
    omega
  let t : Fin (n + 1) → Set.Icc (0 : ℝ) T := fun i =>
    ⟨U.orderEmbOfFin hcard i, (hUb (U.orderEmbOfFin_mem hcard i)).1,
      (hUb (U.orderEmbOfFin_mem hcard i)).2⟩
  have ht : StrictMono t := by
    intro i j hij
    exact (U.orderEmbOfFin hcard).strictMono hij
  let index (x : ℝ) (hx : x ∈ U) : Fin (n + 1) := (U.orderIsoOfFin hcard).symm ⟨x, hx⟩
  let a : I → Fin (n + 1) := fun i => index i.1.1 (hIU i.1 i.2)
  let b : J → Fin (n + 1) := fun j => index (s + (j.1 : ℝ)) (hJU j.1 j.2)
  let as : Fin (n + 1) := index s hsU
  have ht_index (x : ℝ) (hx : x ∈ U) : (t (index x hx) : ℝ) = x := by
    simp [t, index, Finset.orderEmbOfFin]
  have ht_a (i : I) : t (a i) = i.1.1 := by
    apply Subtype.ext
    exact ht_index _ _
  have ht_b (j : J) : t (b j) =
      ⟨s + (j.1 : ℝ), add_nonneg hs j.1.property.1, by linarith [j.1.property.2]⟩ := by
    apply Subtype.ext
    exact ht_index _ _
  have ht_as : t as = ⟨s, hs, hsT⟩ := by
    apply Subtype.ext
    exact ht_index _ _
  have ht0 : t 0 = ⟨0, le_rfl, hs.trans hsT⟩ := by
    apply Subtype.ext
    apply le_antisymm
    · have hle : t 0 ≤ t (index 0 h0U) := ht.monotone (Fin.zero_le _)
      change (t 0 : ℝ) ≤ (t (index 0 h0U) : ℝ) at hle
      rw [ht_index] at hle
      exact hle
    · exact (t 0).property.1
  let A : Set (Fin n) := {i | i.succ ≤ as}
  let B : Set (Fin n) := {i | as ≤ i.castSucc}
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro i hiA hiB
    exact (not_lt_of_ge hiA) (lt_of_le_of_lt hiB Fin.castSucc_lt_succ)
  let inc : D T ℝ → Fin n → ℝ := fun f i => f (t i.succ) - f (t i.castSucc)
  have hinc (i : Fin n) : Measurable (fun f => inc f i) :=
    (measurable_eval _).sub (measurable_eval _)
  have hind : iIndepFun (fun i f => inc f i) (P : Measure (D T ℝ)) := by
    exact hP.iIndepFun_eval_sub_of_strictMono n t ht
  have hbase : IndepFun (fun f (i : A) => inc f i) (fun f (i : B) => inc f i)
      (P : Measure (D T ℝ)) := hind.indepFun_set A B hAB hinc
  let pa : (A → ℝ) → (I → ℝ) := fun x i =>
    initialSum (a i) (fun k => if hk : k ∈ A then x ⟨k, hk⟩ else 0)
  let fu : (B → ℝ) → (J → ℝ) := fun x j =>
    intervalSum as (b j) (fun k => if hk : k ∈ B then x ⟨k, hk⟩ else 0)
  have hpa : Measurable pa := by
    apply Measurable.of_eval
    intro i
    simp only [pa, initialSum]
    fun_prop
  have hfu : Measurable fu := by
    apply Measurable.of_eval
    intro j
    simp only [fu, intervalSum]
    fun_prop
  have hpast : (fun f => pa (fun i : A => inc f i)) =ᵐ[(P : Measure (D T ℝ))]
      (fun (f : D T ℝ) (i : I) => f i.1.1) := by
    filter_upwards [hP.start (hs.trans hsT)] with f hf
    funext i
    have hai : a i ≤ as := by
      apply ht.le_iff_le.mp
      rw [ht_a, ht_as]
      exact i.1.2
    have hsum : initialSum (a i)
        (fun k => if hk : k ∈ A then (fun q : A => inc f q) ⟨k, hk⟩ else 0) =
        initialSum (a i) (inc f) := by
      unfold initialSum
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hka : k.succ ≤ a i
      · have hkA : k ∈ A := hka.trans hai
        simp [hkA, hka]
      · simp [hka]
    change initialSum (a i)
      (fun k => if hk : k ∈ A then (fun q : A => inc f q) ⟨k, hk⟩ else 0) = _
    rw [hsum]
    change initialSum (a i) (fun k => f (t k.succ) - f (t k.castSucc)) = _
    rw [initialSum_apply (a i) (fun q => f (t q)), ht0, ht_a, hf, sub_zero]
  have hfuture : (fun f => fu (fun i : B => inc f i)) =ᵐ[(P : Measure (D T ℝ))]
      (fun (f : D T ℝ) (j : J) => shiftIncrement hs hsT f j.1) := by
    filter_upwards [] with f
    funext j
    have hab : as ≤ b j := by
      apply ht.le_iff_le.mp
      rw [ht_as, ht_b]
      exact le_add_of_nonneg_right j.1.property.1
    have hsum : intervalSum as (b j)
        (fun k => if hk : k ∈ B then (fun q : B => inc f q) ⟨k, hk⟩ else 0) =
        intervalSum as (b j) (inc f) := by
      unfold intervalSum
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkb : as ≤ k.castSucc ∧ k.succ ≤ b j
      · have hkB : k ∈ B := hkb.1
        simp [hkB, hkb]
      · simp [hkb]
    change intervalSum as (b j)
      (fun k => if hk : k ∈ B then (fun q : B => inc f q) ⟨k, hk⟩ else 0) = _
    rw [hsum, intervalSum_eq _ _ hab]
    change initialSum (b j) (fun k => f (t k.succ) - f (t k.castSucc)) -
      initialSum as (fun k => f (t k.succ) - f (t k.castSucc)) = _
    rw [initialSum_apply (b j) (fun q => f (t q)),
      initialSum_apply as (fun q => f (t q)), ht_b, ht_as]
    simp only [shiftIncrement, coe_mk]
    ring
  exact (hbase.comp hpa hfu).congr hpast hfuture

/-- The whole restricted past is independent of the whole future increment path. -/
theorem IsStableLevyLaw.indepFun_restrict_shiftIncrement {θ T s : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P)
    (hs : 0 ≤ s) (hsT : s ≤ T) :
    IndepFun (restrict (E := ℝ) hsT) (shiftIncrement hs hsT)
      (P : Measure (D T ℝ)) := by
  have hcoord : IndepFun
      (fun (f : D T ℝ) (i : {t : Set.Icc (0 : ℝ) T // (t : ℝ) ≤ s}) => f i.1)
      (fun (f : D T ℝ) (j : Set.Icc (0 : ℝ) (T - s)) => shiftIncrement hs hsT f j)
      (P : Measure (D T ℝ)) := by
    refine IndepFun.process_indepFun_process
      (X := fun (i : {t : Set.Icc (0 : ℝ) T // (t : ℝ) ≤ s})
        (f : D T ℝ) => f i.1)
      (Y := fun (j : Set.Icc (0 : ℝ) (T - s)) (f : D T ℝ) =>
        shiftIncrement hs hsT f j)
      (fun i => measurable_eval i.1)
      (fun j => (measurable_eval j).comp (measurable_shiftIncrement hs hsT)) ?_
    intro I J
    exact hP.indepFun_finset_eval_shift hs hsT I J
  have hpast : MeasurableSpace.comap
      (fun (f : D T ℝ) (i : {t : Set.Icc (0 : ℝ) T // (t : ℝ) ≤ s}) => f i.1)
      (inferInstance : MeasurableSpace
        ({t : Set.Icc (0 : ℝ) T // (t : ℝ) ≤ s} → ℝ)) =
      MeasurableSpace.comap (restrict (E := ℝ) hsT)
        (inferInstance : MeasurableSpace (D s ℝ)) := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def]
    exact (comap_restrict_eq_iSup_comap_eval hsT).symm
  have hfuture : MeasurableSpace.comap
      (fun (f : D T ℝ) (j : Set.Icc (0 : ℝ) (T - s)) => shiftIncrement hs hsT f j)
      (inferInstance : MeasurableSpace (Set.Icc (0 : ℝ) (T - s) → ℝ)) =
      MeasurableSpace.comap (shiftIncrement hs hsT)
        (inferInstance : MeasurableSpace (D (T - s) ℝ)) := by
    rw [measurableSpace_eq_iSup_comap_eval (T := T - s) (E := ℝ) (S := Set.univ)
      dense_univ (sub_nonneg.mpr hsT) (by simp)]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def, Set.mem_univ, iSup_true]
  change Indep
    (MeasurableSpace.comap (restrict (E := ℝ) hsT) inferInstance)
    (MeasurableSpace.comap (shiftIncrement hs hsT) inferInstance) (P : Measure (D T ℝ))
  rw [← hpast, ← hfuture]
  exact hcoord

/-- Shifting a stable Lévy law to a positive remaining horizon gives a stable Lévy law. -/
theorem IsStableLevyLaw.isStableLevyLaw_map_shiftIncrement {θ T s : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P)
    (hs : 0 ≤ s) (hsT : s ≤ T) :
    IsStableLevyLaw θ (T - s) (P.map (shiftIncrement hs hsT)) := by
  refine ⟨?_, ?_⟩
  · intro h
    let z : Set.Icc (0 : ℝ) (T - s) := ⟨0, le_rfl, h⟩
    have hset : MeasurableSet {g : D (T - s) ℝ | g z = 0} :=
      (measurable_eval z) (measurableSet_singleton 0)
    rw [ProbabilityMeasure.toMeasure_map,
      ae_map_iff (measurable_shiftIncrement hs hsT).aemeasurable hset]
    filter_upwards [] with f
    have hz : (⟨s + (0 : ℝ), add_nonneg hs (le_refl 0), by simpa using hsT⟩ :
        Set.Icc (0 : ℝ) T) = ⟨s, hs, hsT⟩ := by
      apply Subtype.ext
      simp
    simp only [shiftIncrement, coe_mk, z]
    rw [hz, sub_self]
  · intro k t ht ht0
    let u : Fin (k + 1) → Set.Icc (0 : ℝ) T := fun i =>
      ⟨s + t i, add_nonneg hs (t i).property.1, by linarith [(t i).property.2]⟩
    have hu : StrictMono u := by
      intro i j hij
      change s + (t i : ℝ) < s + (t j : ℝ)
      exact add_lt_add_right (by exact_mod_cast ht hij) s
    have hmeas : Measurable (fun g : D (T - s) ℝ =>
        fun i : Fin k => g (t i.succ) - g (t i.castSucc)) :=
      Measurable.of_eval fun i => (measurable_eval _).sub (measurable_eval _)
    rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_map hmeas (measurable_shiftIncrement hs hsT)]
    have hcomp : (fun g : D (T - s) ℝ =>
        fun i : Fin k => g (t i.succ) - g (t i.castSucc)) ∘ shiftIncrement hs hsT =
        (fun f : D T ℝ => fun i : Fin k => f (u i.succ) - f (u i.castSucc)) := by
      funext f i
      simp only [Function.comp_apply, shiftIncrement, coe_mk, u]
      ring
    rw [hcomp]
    simpa only [u, add_sub_add_left_eq_sub] using hP.map_increments k u hu

/-- The future increment path has the stable process law on the remaining horizon. -/
theorem map_shiftIncrement_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    (stableProcessLaw θ T).map (shiftIncrement hs hsT) = stableProcessLaw θ (T - s) := by
  by_cases hTs : 0 < T - s
  · apply (eq_stableProcessLaw_iff hθ hTs).mpr
    exact (isStableLevyLaw_stableProcessLaw hθ hT).isStableLevyLaw_map_shiftIncrement
      hs hsT
  · have hst : s = T := by linarith
    subst T
    let z : D (s - s) ℝ := Skorokhod.ofContinuous (ContinuousMap.const _ 0)
    have hzero : shiftIncrement hs (le_refl s) = fun _ => z := by
      funext f
      apply BGW.Skorokhod.ext
      intro t
      have ht : (t : ℝ) = 0 := by linarith [t.property.1, t.property.2]
      have ht' : (⟨s + (t : ℝ), add_nonneg hs t.property.1, by linarith [t.property.2]⟩ :
          Set.Icc (0 : ℝ) s) = ⟨s, hs, le_refl s⟩ := by
        apply Subtype.ext
        simp [ht]
      simp only [shiftIncrement, coe_mk, z, Skorokhod.ofContinuous, ContinuousMap.const_apply]
      rw [ht', sub_self]
    rw [hzero]
    apply ProbabilityMeasure.toMeasure_injective
    simp [ProbabilityMeasure.toMeasure_map, Measure.map_const, stableProcessLaw, hθ, z]

end BGW.StableTrees
