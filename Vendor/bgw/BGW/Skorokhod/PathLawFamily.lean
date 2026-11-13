/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Restrict
public import BGW.Skorokhod.MeasurableMaps
public import BGW.Skorokhod.CompleteMetricCompleteness
public import BGW.Skorokhod.Separable
public import BGW.Skorokhod.Measurable
public import KolmogorovExtension4.KolmogorovExtension
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Consistent path-law families on growing horizons

Construct the unique law on compatible càdlàg path families from consistent laws on an
increasing sequence of time horizons.

The construction uses the Kolmogorov extension theorem of the vendored `kolmogorov_extension4`
(R. Degenne and P. Pfaffelhuber), applied to the projective family of restrictions; see also
O. Kallenberg, *Foundations of Modern Probability*, Theorem 8.21.
-/

@[expose] public section

open Set MeasureTheory

namespace BGW.Skorokhod

variable (b : ℕ → ℝ) (hb : StrictMono b)

/-- Compatible horizon families with adjacent restrictions agreeing. -/
def CompatiblePaths (b : ℕ → ℝ) (hb : StrictMono b) : Type :=
  {p : (n : ℕ) → D (b n) ℝ // ∀ n,
    restrict (hb.monotone (Nat.le_succ n)) (p (n + 1)) = p n}

/-- The compatible-family subtype carries its subspace measurable structure. -/
noncomputable instance (b : ℕ → ℝ) (hb : StrictMono b) :
    MeasurableSpace (CompatiblePaths b hb) :=
  (inferInstance : MeasurableSpace (Subtype _))

/-- The coordinate map of the compatible-family subtype. -/
def CompatiblePaths.coord {b : ℕ → ℝ} {hb : StrictMono b} (n : ℕ)
    (p : CompatiblePaths b hb) : D (b n) ℝ := p.1 n

/-- Coordinate maps on compatible families are measurable. -/
theorem CompatiblePaths.measurable_coord (b : ℕ → ℝ) (hb : StrictMono b) (n : ℕ) :
    Measurable (CompatiblePaths.coord (b := b) (hb := hb) n) :=
  (measurable_pi_apply n).comp measurable_subtype_coe

private theorem coord_eq_restrict_of_le (b : ℕ → ℝ) (hb : StrictMono b)
    (p : CompatiblePaths b hb) {n m : ℕ} (hnm : n ≤ m) :
    restrict (hb.monotone hnm) (CompatiblePaths.coord m p) = CompatiblePaths.coord n p := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      have hres : restrict (E := ℝ) (show b 0 ≤ b 0 from le_rfl) = id := by
        funext f
        ext t
        rfl
      rw [hres]
      rfl
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · have hcomp : (fun f : D (b (m + 1)) ℝ =>
            restrict (hb.monotone hnm')
              (restrict (hb.monotone (Nat.le_succ m)) f)) =
            restrict (hb.monotone (show n ≤ m + 1 by omega)) := by
          funext f
          ext t
          rfl
        calc
          restrict (hb.monotone (show n ≤ m + 1 by omega))
              (CompatiblePaths.coord (m + 1) p) =
              restrict (hb.monotone hnm')
                (restrict (hb.monotone (Nat.le_succ m)) (CompatiblePaths.coord (m + 1) p)) := by
            rw [← hcomp]
          _ = restrict (hb.monotone hnm') (CompatiblePaths.coord m p) := by
            exact congrArg (restrict (hb.monotone hnm')) (p.2 m)
          _ = CompatiblePaths.coord n p := ih hnm'
      · have hn : n = m + 1 := by omega
        subst n
        have hres : restrict (E := ℝ) (show b (m + 1) ≤ b (m + 1) from le_rfl) = id := by
          funext f
          ext t
          rfl
        rw [hres]
        rfl

private def coordFamily (b : ℕ → ℝ) (hb : StrictMono b) (J : Finset ℕ)
    (p : CompatiblePaths b hb) : (j : J) → D (b j) ℝ :=
  fun j => CompatiblePaths.coord j p

private theorem measurable_coordFamily (b : ℕ → ℝ) (hb : StrictMono b) (J : Finset ℕ) :
    Measurable (coordFamily b hb J) :=
  Measurable.of_eval fun j => CompatiblePaths.measurable_coord b hb j

private theorem map_coordFamily_eq_of_coord_map_eq (b : ℕ → ℝ) (hb : StrictMono b)
    {Q Q' : Measure (CompatiblePaths b hb)}
    (h : ∀ n, Q.map (CompatiblePaths.coord n) = Q'.map (CompatiblePaths.coord n))
    (J : Finset ℕ) :
    Q.map (coordFamily b hb J) = Q'.map (coordFamily b hb J) := by
  classical
  by_cases hJ : J.Nonempty
  · let N := J.sup id
    let r : D (b N) ℝ → (j : J) → D (b j) ℝ := fun f j =>
      restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f
    have hr : Measurable r := Measurable.of_eval fun j =>
      measurable_restrict (hb.monotone (Finset.le_sup (f := id) j.2))
    have hfactor : r ∘ CompatiblePaths.coord N = coordFamily b hb J := by
      funext p j
      exact coord_eq_restrict_of_le b hb p (Finset.le_sup (f := id) j.2)
    have hleft : Q.map (coordFamily b hb J) = (Q.map (CompatiblePaths.coord N)).map r := by
      rw [← hfactor]
      exact (Measure.map_map hr (CompatiblePaths.measurable_coord b hb N)).symm
    have hright : Q'.map (coordFamily b hb J) =
        (Q'.map (CompatiblePaths.coord N)).map r := by
      rw [← hfactor]
      exact (Measure.map_map hr (CompatiblePaths.measurable_coord b hb N)).symm
    calc
      Q.map (coordFamily b hb J) = (Q.map (CompatiblePaths.coord N)).map r := hleft
      _ = (Q'.map (CompatiblePaths.coord N)).map r := congrArg (fun μ => μ.map r) (h N)
      _ = Q'.map (coordFamily b hb J) := hright.symm
  · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    let r : D (b 0) ℝ → (j : (∅ : Finset ℕ)) → D (b j) ℝ := fun _ => default
    have hr : Measurable r := measurable_const
    have hfactor : r ∘ CompatiblePaths.coord 0 = coordFamily b hb ∅ := by
      funext p
      exact Subsingleton.elim _ _
    have hleft : Q.map (coordFamily b hb ∅) = (Q.map (CompatiblePaths.coord 0)).map r := by
      rw [← hfactor]
      exact (Measure.map_map hr (CompatiblePaths.measurable_coord b hb 0)).symm
    have hright : Q'.map (coordFamily b hb ∅) =
        (Q'.map (CompatiblePaths.coord 0)).map r := by
      rw [← hfactor]
      exact (Measure.map_map hr (CompatiblePaths.measurable_coord b hb 0)).symm
    calc
      Q.map (coordFamily b hb ∅) = (Q.map (CompatiblePaths.coord 0)).map r := hleft
      _ = (Q'.map (CompatiblePaths.coord 0)).map r := congrArg (fun μ => μ.map r) (h 0)
      _ = Q'.map (coordFamily b hb ∅) := hright.symm

/-- Finite measures on compatible paths are determined by their coordinate marginals. -/
theorem CompatiblePaths.measure_ext (b : ℕ → ℝ) (hb : StrictMono b)
    {Q Q' : Measure (CompatiblePaths b hb)} [IsFiniteMeasure Q]
    (h : ∀ n, Q.map (CompatiblePaths.coord (hb := hb) n) =
      Q'.map (CompatiblePaths.coord (hb := hb) n)) : Q = Q' := by
  classical
  let R : ∀ J : Finset ℕ, Measure ((j : J) → D (b j) ℝ) :=
    fun J => Q.map (coordFamily b hb J)
  let toAmbient : CompatiblePaths b hb → (n : ℕ) → D (b n) ℝ := fun p => p.1
  have htoAmbient : Measurable toAmbient := Measurable.of_eval fun n =>
    (measurable_pi_apply n).comp measurable_subtype_coe
  have hfinite (J : Finset ℕ) : IsFiniteMeasure (R J) := by
    dsimp [R]
    exact Measure.isFiniteMeasure_map Q (coordFamily b hb J)
  let (J : Finset ℕ) : IsFiniteMeasure (R J) := hfinite J
  have hlimQ : IsProjectiveLimit (Q.map toAmbient) R := by
    intro J
    change (Q.map toAmbient).map (Finset.restrict J) = Q.map (coordFamily b hb J)
    rw [Measure.map_map (Finset.measurable_restrict J) htoAmbient]
    rfl
  have hlimQ' : IsProjectiveLimit (Q'.map toAmbient) R := by
    intro J
    change (Q'.map toAmbient).map (Finset.restrict J) = Q.map (coordFamily b hb J)
    calc
      (Q'.map toAmbient).map (Finset.restrict J) = Q'.map (coordFamily b hb J) := by
        rw [Measure.map_map (Finset.measurable_restrict J) htoAmbient]
        rfl
      _ = Q.map (coordFamily b hb J) :=
        (map_coordFamily_eq_of_coord_map_eq b hb h J).symm
  have hmap : Q.map toAmbient = Q'.map toAmbient :=
    IsProjectiveLimit.unique hlimQ hlimQ'
  apply Measure.ext
  intro A hA
  have hcomap : MeasurableSpace.comap toAmbient
      (inferInstance : MeasurableSpace ((n : ℕ) → D (b n) ℝ)) =
      (inferInstance : MeasurableSpace (CompatiblePaths b hb)) := rfl
  have hA' : MeasurableSet[MeasurableSpace.comap toAmbient
      (inferInstance : MeasurableSpace ((n : ℕ) → D (b n) ℝ))] A := by
    rw [hcomap]
    exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  rw [← Measure.map_apply htoAmbient hB, ← Measure.map_apply htoAmbient hB]
  exact congrArg (fun μ : Measure ((n : ℕ) → D (b n) ℝ) => μ B) hmap

/-- The set of compatible product paths is measurable. -/
theorem measurableSet_compatible (b : ℕ → ℝ) (hb : StrictMono b) :
    MeasurableSet {p : (n : ℕ) → D (b n) ℝ |
      ∀ n, restrict (hb.monotone (Nat.le_succ n)) (p (n + 1)) = p n} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_eq_fun
    ((measurable_restrict (hb.monotone (Nat.le_succ n))).comp (measurable_pi_apply (n + 1)))
    (measurable_pi_apply n)

/-- Consistency at adjacent horizons implies consistency at every pair of horizons. -/
theorem map_restrict_eq_of_le (P : ∀ k, ProbabilityMeasure (D (b k) ℝ))
    (hP : ∀ k, (P (k + 1)).map (restrict (hb.monotone (Nat.le_succ k))) = P k)
    {n m : ℕ} (hnm : n ≤ m) :
    (P m).map (restrict (hb.monotone hnm)) = P n := by
  induction m with
  | zero =>
      have : n = 0 := by omega
      subst n
      have hres : restrict (E := ℝ) (show b 0 ≤ b 0 from le_rfl) = id := by
        funext f
        ext t
        rfl
      rw [hres]
      apply Subtype.ext
      change (P 0 : Measure (D (b 0) ℝ)).map id = (P 0 : Measure (D (b 0) ℝ))
      rw [Measure.map_id]
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · have hcomp : (fun f : D (b (m + 1)) ℝ =>
            restrict (hb.monotone hnm')
              (restrict (hb.monotone (Nat.le_succ m)) f)) =
            restrict (hb.monotone (show n ≤ m + 1 by omega)) := by
          funext f
          ext t
          rfl
        apply Subtype.ext
        change ((P (m + 1) : Measure (D (b (m + 1)) ℝ)).map
          (restrict (hb.monotone hnm))) = (P n : Measure (D (b n) ℝ))
        have hstep := congrArg (fun q : ProbabilityMeasure (D (b m) ℝ) =>
          (q : Measure (D (b m) ℝ))) (hP m)
        change ((P (m + 1) : Measure (D (b (m + 1)) ℝ)).map
          (restrict (hb.monotone (Nat.le_succ m)))) = (P m : Measure (D (b m) ℝ)) at hstep
        rw [show hnm = (show n ≤ m + 1 by omega) from Subsingleton.elim _ _]
        calc
          ((P (m + 1) : Measure (D (b (m + 1)) ℝ)).map
              (restrict (hb.monotone (show n ≤ m + 1 by omega)))) =
              ((P (m + 1) : Measure (D (b (m + 1)) ℝ)).map
                (restrict (hb.monotone (Nat.le_succ m)))).map
                (restrict (hb.monotone hnm')) := by
            rw [← hcomp]
            exact (Measure.map_map (measurable_restrict (hb.monotone hnm'))
              (measurable_restrict (hb.monotone (Nat.le_succ m)))).symm
          _ = (P m : Measure (D (b m) ℝ)).map (restrict (hb.monotone hnm')) := by
            rw [hstep]
          _ = (P n : Measure (D (b n) ℝ)) := by
            exact congrArg (fun q : ProbabilityMeasure (D (b n) ℝ) =>
              (q : Measure (D (b n) ℝ))) (ih hnm')
      · have hn : n = m + 1 := by omega
        subst n
        have hres : restrict (E := ℝ) (show b (m + 1) ≤ b (m + 1) from le_rfl) = id := by
          funext f
          ext t
          rfl
        rw [hres]
        apply Subtype.ext
        change (P (m + 1) : Measure (D (b (m + 1)) ℝ)).map id =
          (P (m + 1) : Measure (D (b (m + 1)) ℝ))
        rw [Measure.map_id]

/-- The law on a finite index set obtained by restricting the law at its largest horizon. -/
noncomputable def maxIndexLaw (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ)) (J : Finset ℕ) :
    Measure ((j : J) → D (b j) ℝ) :=
  (P (J.sup id) : Measure (D (b (J.sup id)) ℝ)).map
    (fun f (j : J) => restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f)

/-- The max-index laws form a projective family over finite index sets. -/
theorem isProjectiveMeasureFamily_maxIndexLaw (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    (hP : ∀ n, (P (n + 1)).map (restrict (hb.monotone (Nat.le_succ n))) = P n) :
    IsProjectiveMeasureFamily (α := fun n => D (b n) ℝ) (maxIndexLaw b hb P) := by
  classical
  intro I J hJI
  let M := I.sup id
  let N := J.sup id
  have hNM : N ≤ M := Finset.sup_mono hJI
  let rI : D (b M) ℝ → (i : I) → D (b i) ℝ := fun f i =>
    restrict (hb.monotone (Finset.le_sup (f := id) (b := (i : ℕ)) i.2)) f
  let rJ : D (b N) ℝ → (j : J) → D (b j) ℝ := fun f j =>
    restrict (hb.monotone (Finset.le_sup (f := id) (b := (j : ℕ)) j.2)) f
  let rMax : D (b M) ℝ → D (b N) ℝ := restrict (hb.monotone hNM)
  let rIJ : ((i : I) → D (b i) ℝ) → (j : J) → D (b j) ℝ :=
    Finset.restrict₂ (π := fun i => D (b i) ℝ) hJI
  have hrI : Measurable rI := Measurable.of_eval fun i =>
    measurable_restrict (hb.monotone (Finset.le_sup (f := id) (b := (i : ℕ)) i.2))
  have hrJ : Measurable rJ := Measurable.of_eval fun j =>
    measurable_restrict (hb.monotone (Finset.le_sup (f := id) (b := (j : ℕ)) j.2))
  have hrMax : Measurable rMax := measurable_restrict _
  have hrIJ : Measurable rIJ := Finset.measurable_restrict₂ (X := fun i => D (b i) ℝ) hJI
  have hfun : rIJ ∘ rI = rJ ∘ rMax := by
    funext f j
    ext t
    change (restrict (hb.monotone
        (Finset.le_sup (f := id) (b := (j : ℕ)) (hJI j.2))) f) t =
      (restrict (hb.monotone (Finset.le_sup (f := id) (b := (j : ℕ)) j.2))
        (restrict (hb.monotone hNM) f)) t
    simp only [restrict]
    congr 1
  have hcons := map_restrict_eq_of_le b hb P hP hNM
  have hcons' :
      (P M : Measure (D (b M) ℝ)).map rMax = (P N : Measure (D (b N) ℝ)) := by
    exact congrArg (fun q : ProbabilityMeasure (D (b N) ℝ) =>
      (q : Measure (D (b N) ℝ))) hcons
  change (P (J.sup id) : Measure (D (b (J.sup id)) ℝ)).map
      (fun (f : D (b (J.sup id)) ℝ) (j : J) =>
        restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f) =
    ((P (I.sup id) : Measure (D (b (I.sup id)) ℝ)).map
      (fun (f : D (b (I.sup id)) ℝ) (i : I) =>
        restrict (hb.monotone (Finset.le_sup (f := id) i.2)) f)).map
      (Finset.restrict₂ (π := fun i => D (b i) ℝ) hJI)
  calc
    (P N : Measure (D (b N) ℝ)).map rJ =
        ((P M : Measure (D (b M) ℝ)).map rMax).map rJ := by rw [hcons']
    _ = (P M : Measure (D (b M) ℝ)).map (rJ ∘ rMax) :=
      Measure.map_map hrJ hrMax
    _ = (P M : Measure (D (b M) ℝ)).map (rIJ ∘ rI) := by rw [← hfun]
    _ = ((P M : Measure (D (b M) ℝ)).map rI).map rIJ :=
      (Measure.map_map hrIJ hrI).symm

private def compatibleAt (b : ℕ → ℝ) (hb : StrictMono b) (n : ℕ) :
    Set ((k : ℕ) → D (b k) ℝ) :=
  {x | restrict (hb.monotone (Nat.le_succ n)) (x (n + 1)) = x n}

private theorem measurable_compatibleAt (b : ℕ → ℝ) (hb : StrictMono b) (n : ℕ) :
    MeasurableSet (compatibleAt b hb n) := by
  change MeasurableSet {x : (k : ℕ) → D (b k) ℝ |
    restrict (hb.monotone (Nat.le_succ n)) (x (n + 1)) = x n}
  exact measurableSet_eq_fun
    ((measurable_restrict (hb.monotone (Nat.le_succ n))).comp (measurable_pi_apply (n + 1)))
    (measurable_pi_apply n)

private def pairIndex (n : ℕ) : Finset ℕ := {n, n + 1}

private def pairLawEvent (b : ℕ → ℝ) (hb : StrictMono b) (n : ℕ) :
    Set ((j : pairIndex n) → D (b j) ℝ) :=
  {z | restrict (hb.monotone (Nat.le_succ n))
      (z (⟨n + 1, by simp [pairIndex]⟩ : pairIndex n)) =
        z (⟨n, by simp [pairIndex]⟩ : pairIndex n)}

private theorem measurable_pairLawEvent (b : ℕ → ℝ) (hb : StrictMono b) (n : ℕ) :
    MeasurableSet (pairLawEvent b hb n) := by
  exact measurableSet_eq_fun
    ((measurable_restrict (hb.monotone (Nat.le_succ n))).comp
      (measurable_pi_apply (⟨n + 1, by simp [pairIndex]⟩ : pairIndex n)))
    (measurable_pi_apply (⟨n, by simp [pairIndex]⟩ : pairIndex n))

private theorem cylinder_pairLawEvent_eq_compatibleAt (b : ℕ → ℝ)
    (hb : StrictMono b) (n : ℕ) :
    MeasureTheory.cylinder (pairIndex n) (pairLawEvent b hb n) = compatibleAt b hb n := by
  ext x
  simp [MeasureTheory.cylinder, pairLawEvent, pairIndex, compatibleAt, Finset.restrict]

private theorem maxIndexLaw_pairLawEvent (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ)) (n : ℕ) :
    maxIndexLaw b hb P (pairIndex n) (pairLawEvent b hb n) = 1 := by
  classical
  let r : D (b ((pairIndex n).sup id)) ℝ → (j : pairIndex n) → D (b j) ℝ := fun f j =>
    restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f
  have hr : Measurable r := Measurable.of_eval fun j =>
    measurable_restrict (hb.monotone (Finset.le_sup (f := id) j.2))
  have hn1mem : n + 1 ∈ pairIndex n := by simp [pairIndex]
  have hnmem : n ∈ pairIndex n := by simp [pairIndex]
  have hs1 : n + 1 ≤ (pairIndex n).sup id :=
    Finset.le_sup (f := id) hn1mem
  have hs0 : n ≤ (pairIndex n).sup id := Finset.le_sup (f := id) hnmem
  have hpre : r ⁻¹' pairLawEvent b hb n = Set.univ := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ, iff_true, pairLawEvent, Set.mem_ofPred_eq]
    change restrict (hb.monotone (Nat.le_succ n))
        (restrict (hb.monotone hs1) f) = restrict (hb.monotone hs0) f
    ext t
    rfl
  rw [maxIndexLaw]
  rw [Measure.map_apply hr (measurable_pairLawEvent b hb n)]
  rw [hpre]
  exact measure_univ

private def compatibleSet (b : ℕ → ℝ) (hb : StrictMono b) :
    Set ((n : ℕ) → D (b n) ℝ) :=
  {p | ∀ n, restrict (hb.monotone (Nat.le_succ n)) (p (n + 1)) = p n}

private theorem measurableSet_compatibleSet (b : ℕ → ℝ) (hb : StrictMono b) :
    MeasurableSet (compatibleSet b hb) := by
  change MeasurableSet {p : (n : ℕ) → D (b n) ℝ |
    ∀ n, restrict (hb.monotone (Nat.le_succ n)) (p (n + 1)) = p n}
  exact measurableSet_compatible b hb

private theorem projectiveLimit_measure_compatibleAt (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    {μ : Measure ((n : ℕ) → D (b n) ℝ)}
    (hμ : IsProjectiveLimit μ (maxIndexLaw b hb P)) (n : ℕ) :
    μ (compatibleAt b hb n) = 1 := by
  rw [← cylinder_pairLawEvent_eq_compatibleAt b hb n]
  rw [hμ.measure_cylinder (pairIndex n) (measurable_pairLawEvent b hb n)]
  exact maxIndexLaw_pairLawEvent b hb P n

private theorem projectiveLimit_measure_compatibleSet (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    {μ : Measure ((n : ℕ) → D (b n) ℝ)}
    (hμ : IsProjectiveLimit μ (maxIndexLaw b hb P)) (hMass : μ univ = 1) :
    μ (compatibleSet b hb) = 1 := by
  classical
  have hfull (n : ℕ) : μ (compatibleAt b hb n) = 1 :=
    projectiveLimit_measure_compatibleAt b hb P hμ n
  have hnull : μ (compatibleSet b hb)ᶜ = 0 := by
    have hset : compatibleSet b hb = ⋂ n, compatibleAt b hb n := by
      ext x
      simp [compatibleSet, compatibleAt]
    rw [hset, compl_iInter]
    apply measure_iUnion_null
    intro n
    rw [measure_compl (measurable_compatibleAt b hb n) (by rw [hfull n]; simp)]
    rw [hMass, hfull n]
    simp
  calc
    μ (compatibleSet b hb) = μ (compatibleSet b hb) + μ (compatibleSet b hb)ᶜ := by
      rw [hnull]
      simp
    _ = μ univ := measure_add_measure_compl (measurableSet_compatibleSet b hb)
    _ = 1 := hMass

private theorem projectiveLimit_coord (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    (hP : ∀ n, (P (n + 1)).map (restrict (hb.monotone (Nat.le_succ n))) = P n)
    {μ : Measure ((n : ℕ) → D (b n) ℝ)}
    (hμ : IsProjectiveLimit μ (maxIndexLaw b hb P)) (n : ℕ) :
    μ.map (fun f => f n) = (P n : Measure (D (b n) ℝ)) := by
  classical
  let J : Finset ℕ := {n}
  let jn : J := ⟨n, by simp [J]⟩
  let e : ((j : J) → D (b j) ℝ) → D (b n) ℝ := fun q => q jn
  let res : ((n : ℕ) → D (b n) ℝ) → (j : J) → D (b j) ℝ :=
    Finset.restrict (π := fun i => D (b i) ℝ) J
  have hres : Measurable res := Finset.measurable_restrict (X := fun i => D (b i) ℝ) J
  have he : Measurable e := measurable_pi_apply jn
  have hcomp : e ∘ res = fun f => f n := by
    funext f
    rfl
  calc
    μ.map (fun f => f n) = (μ.map res).map e := by
      rw [← hcomp]
      exact (Measure.map_map he hres).symm
    _ = (maxIndexLaw b hb P J).map e := by
      exact congrArg (fun ν => ν.map e) (hμ J)
    _ = (P n : Measure (D (b n) ℝ)) := by
      let N := J.sup id
      have hle : n ≤ N := Finset.le_sup (f := id) jn.2
      let r : D (b N) ℝ → (j : J) → D (b j) ℝ := fun f j =>
        restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f
      have hr : Measurable r := Measurable.of_eval fun j =>
        measurable_restrict (hb.monotone (Finset.le_sup (f := id) j.2))
      have hfactor : e ∘ r = restrict (hb.monotone hle) := by
        funext f
        ext t
        rfl
      change ((P N : Measure (D (b N) ℝ)).map r).map e =
        (P n : Measure (D (b n) ℝ))
      calc
        ((P N : Measure (D (b N) ℝ)).map r).map e =
            (P N : Measure (D (b N) ℝ)).map (e ∘ r) := Measure.map_map he hr
        _ = (P N : Measure (D (b N) ℝ)).map (restrict (hb.monotone hle)) := by
          rw [hfactor]
        _ = (P n : Measure (D (b n) ℝ)) := by
          exact congrArg (fun q : ProbabilityMeasure (D (b n) ℝ) =>
            (q : Measure (D (b n) ℝ))) (map_restrict_eq_of_le b hb P hP hle)

private def compatibleDefault (b : ℕ → ℝ) (hb : StrictMono b) : CompatiblePaths b hb :=
  ⟨fun n => ⟨fun _ => 0, IsCadlag.const⟩, fun n => by
    ext t
    rfl⟩

private noncomputable def liftCompatible (b : ℕ → ℝ) (hb : StrictMono b)
    (x : (n : ℕ) → D (b n) ℝ) : CompatiblePaths b hb := by
  classical
  exact ⟨if hx : x ∈ compatibleSet b hb then x else (compatibleDefault b hb).1, by
    split_ifs with hx
    · exact hx
    · exact (compatibleDefault b hb).2⟩

private theorem measurable_liftCompatible (b : ℕ → ℝ) (hb : StrictMono b) :
    Measurable (liftCompatible b hb) := by
  classical
  have hval : Measurable (fun x => (liftCompatible b hb x).1) := by
    change Measurable (fun x => if hx : x ∈ compatibleSet b hb then x else
      (compatibleDefault b hb).1)
    exact Measurable.ite (measurableSet_compatibleSet b hb) measurable_id measurable_const
  exact hval.subtype_mk (h := fun x => by
    dsimp [liftCompatible]
    split_ifs with hx
    · exact hx
    · exact (compatibleDefault b hb).2)

/-- Existence and uniqueness of the compatible path law with prescribed coordinate marginals. -/
theorem exists_unique_compatiblePathLaw
    (b : ℕ → ℝ) (hb : StrictMono b) (hb0 : ∀ n, 0 < b n)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    (hP : ∀ n, (P (n + 1)).map (restrict (hb.monotone (Nat.le_succ n))) = P n) :
    ∃! Q : ProbabilityMeasure (CompatiblePaths b hb),
      ∀ n, (Q : Measure (CompatiblePaths b hb)).map (CompatiblePaths.coord n) =
        (P n : Measure (D (b n) ℝ)) := by
  classical
  have _horizonPositive : ∀ n, 0 < b n := hb0
  let hproj := isProjectiveMeasureFamily_maxIndexLaw b hb P hP
  have hfinite (J : Finset ℕ) : IsFiniteMeasure (maxIndexLaw b hb P J) := by
    change IsFiniteMeasure (((P (J.sup id) : Measure (D (b (J.sup id)) ℝ)).map
      (fun f (j : J) => restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f)))
    infer_instance
  let μ : Measure ((n : ℕ) → D (b n) ℝ) :=
    @MeasureTheory.projectiveLimit ℕ (fun n => D (b n) ℝ)
      (fun n => inferInstance) (fun n => inferInstance) (fun n => inferInstance)
      (fun n => inferInstance) (fun n => inferInstance) (maxIndexLaw b hb P) hfinite hproj
  let hμ := @MeasureTheory.isProjectiveLimit_projectiveLimit ℕ (fun n => D (b n) ℝ)
    (fun n => inferInstance) (maxIndexLaw b hb P) (fun n => inferInstance)
    (fun n => inferInstance) (fun n => inferInstance) (fun n => inferInstance)
    hfinite hproj
  have hprob (J : Finset ℕ) : IsProbabilityMeasure (maxIndexLaw b hb P J) := by
    change IsProbabilityMeasure (((P (J.sup id) : Measure (D (b (J.sup id)) ℝ)).map
      (fun f (j : J) => restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f)))
    infer_instance
  have hMass : μ univ = 1 := by
    rw [hμ.measure_univ_eq (∅ : Finset ℕ)]
    exact (hprob ∅).measure_univ
  have hCmass : μ (compatibleSet b hb) = 1 :=
    projectiveLimit_measure_compatibleSet b hb P hμ hMass
  have hCnull : μ (compatibleSet b hb)ᶜ = 0 := by
    rw [measure_compl (measurableSet_compatibleSet b hb) (by rw [hCmass]; simp), hMass, hCmass]
    simp
  let μprob : ProbabilityMeasure ((n : ℕ) → D (b n) ℝ) := ⟨μ, ⟨hMass⟩⟩
  let Q : ProbabilityMeasure (CompatiblePaths b hb) := μprob.map (liftCompatible b hb)
  have hCae : ∀ᵐ x ∂μ, x ∈ compatibleSet b hb := by
    rw [ae_iff]
    exact hCnull
  have hcoord (n : ℕ) :
      (Q : Measure (CompatiblePaths b hb)).map (CompatiblePaths.coord n) =
        (P n : Measure (D (b n) ℝ)) := by
    have hAE : (fun x => CompatiblePaths.coord n (liftCompatible b hb x)) =ᵐ[
        (μprob : Measure ((k : ℕ) → D (b k) ℝ))]
        (fun x => x n) := by
      filter_upwards [hCae] with x hx
      simp [liftCompatible, hx, CompatiblePaths.coord]
    have hAEcomp : (CompatiblePaths.coord n ∘ liftCompatible b hb) =ᵐ[
        (μprob : Measure ((k : ℕ) → D (b k) ℝ))] (fun x => x n) := by
      filter_upwards [hAE] with x hx
      exact hx
    change ((μprob.map (liftCompatible b hb) : ProbabilityMeasure (CompatiblePaths b hb)) :
      Measure (CompatiblePaths b hb)).map (CompatiblePaths.coord n) = _
    rw [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map (CompatiblePaths.measurable_coord b hb n)
      (measurable_liftCompatible b hb)]
    calc
      Measure.map (CompatiblePaths.coord n ∘ liftCompatible b hb)
          (μprob : Measure ((k : ℕ) → D (b k) ℝ)) =
          Measure.map (fun f => f n) (μprob : Measure ((k : ℕ) → D (b k) ℝ)) := by
        exact Measure.map_congr hAEcomp
      _ = μ.map (fun f => f n) := rfl
      _ = (P n : Measure (D (b n) ℝ)) := projectiveLimit_coord b hb P hP hμ n
  refine ⟨Q, hcoord, ?_⟩
  intro Q' hQ'
  apply Subtype.ext
  have hQfinite : IsFiniteMeasure (Q : Measure (CompatiblePaths b hb)) := by
    infer_instance
  symm
  apply @CompatiblePaths.measure_ext b hb (Q : Measure (CompatiblePaths b hb))
    (Q' : Measure (CompatiblePaths b hb)) hQfinite
  intro n
  exact (hcoord n).trans (hQ' n).symm

end BGW.Skorokhod
