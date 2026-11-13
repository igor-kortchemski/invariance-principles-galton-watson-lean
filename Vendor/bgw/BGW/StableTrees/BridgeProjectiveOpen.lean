/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.PathLawFamily
public import BGW.Skorokhod.MeasurableLaws
public import BGW.StableTrees.BridgePrefix
public import BGW.StableTrees.StableProcessLaw

/-!
# Projective construction of the open stable bridge

The dyadic horizons approach one. Consistency of the tilted prefixes supplies a unique
probability law on their compatible families.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The bridge prefix horizons `a_n = 1 - 2^{-(n+1)}`. -/
noncomputable def bridgeHorizon (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (n + 1)

/-- The bridge horizons increase strictly. -/
theorem strictMono_bridgeHorizon : StrictMono bridgeHorizon := by
  intro n m hnm
  dsimp [bridgeHorizon]
  exact sub_lt_sub_left ((pow_right_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)) (Nat.add_lt_add_right hnm 1)) 1

/-- Every bridge horizon is positive. -/
theorem bridgeHorizon_pos (n : ℕ) : 0 < bridgeHorizon n := by
  dsimp [bridgeHorizon]
  have h := pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (by omega : n + 1 ≠ 0)
  linarith

/-- Every bridge horizon is strictly smaller than one. -/
theorem bridgeHorizon_lt_one (n : ℕ) : bridgeHorizon n < 1 := by
  dsimp [bridgeHorizon]
  have h : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  linarith

/-- Every time in `[0, 1)` lies below some horizon. -/
theorem exists_bridgeHorizon_ge {t : ℝ} (ht : t < 1) : ∃ n, t ≤ bridgeHorizon n := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr ht)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hpow : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  dsimp [bridgeHorizon]
  linarith

/-- The open-bridge carrier: compatible families of paths on `[0, a_n]`. Internal encoding of the
bridge construction: downstream results (closed-law characterization, reversal, minimum, Vervaat)
are stated on `D 1 ℝ` through `stableBridgeLaw`, not through `BridgeOpen`, `bridgeOpenLaw` or
`closeBridge`. -/
abbrev BridgeOpen : Type := CompatiblePaths bridgeHorizon strictMono_bridgeHorizon

open Classical in
/-- Totalized evaluation of an open bridge path: the value at `t ∈ [0, 1)` read in the first
coordinate whose horizon is at least `t`; `0` outside `[0, 1)`. -/
noncomputable def BridgeOpen.eval (f : BridgeOpen) (t : ℝ) : ℝ :=
  if h : 0 ≤ t ∧ ∃ n, t ≤ bridgeHorizon n then
    f.1 (Nat.find h.2) ⟨t, h.1, Nat.find_spec h.2⟩
  else 0

/-- Every later coordinate restricts to an earlier one. -/
theorem BridgeOpen.coord_restrict (f : BridgeOpen) {n m : ℕ} (hnm : n ≤ m) :
    restrict (strictMono_bridgeHorizon.monotone hnm) (f.1 m) = f.1 n := by
  induction m, hnm using Nat.le_induction with
  | base =>
    ext t
    rfl
  | succ m hnm ih =>
    have h := congrArg (restrict (strictMono_bridgeHorizon.monotone hnm)) (f.2 m)
    exact h.trans ih

/-- Evaluation is read consistently in every coordinate whose horizon contains `t`. -/
theorem BridgeOpen.eval_eq_coord (f : BridgeOpen) (n : ℕ) (t : Set.Icc (0 : ℝ) (bridgeHorizon n)) :
    f.eval t = f.1 n t := by
  classical
  have ht : 0 ≤ (t : ℝ) ∧ ∃ m, (t : ℝ) ≤ bridgeHorizon m :=
    ⟨t.property.1, ⟨n, t.property.2⟩⟩
  have hle : Nat.find ht.2 ≤ n := Nat.find_min' ht.2 t.property.2
  have hres := BridgeOpen.coord_restrict f hle
  have heq := congrArg (fun g : D (bridgeHorizon (Nat.find ht.2)) ℝ =>
    g ⟨(t : ℝ), t.property.1, Nat.find_spec ht.2⟩) hres
  simpa only [BridgeOpen.eval, dite_eq_left ht, BGW.Skorokhod.restrict, coe_mk] using heq.symm

/-- Evaluation of an open bridge at any fixed time is measurable. -/
theorem BridgeOpen.measurable_eval (t : ℝ) : Measurable (fun f : BridgeOpen => f.eval t) := by
  classical
  unfold BridgeOpen.eval
  split_ifs with h
  · exact (BGW.Skorokhod.measurable_eval (⟨t, h.1, Nat.find_spec h.2⟩ :
      Set.Icc (0 : ℝ) (bridgeHorizon (Nat.find h.2)))).comp
      (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon (Nat.find h.2))
  · exact measurable_const

open Classical in
/-- The tilted prefix laws as probability measures on `D(a_n, ℝ)` (mass one by
`isProbabilityMeasure_bridgePrefixLaw`). -/
noncomputable def bridgePrefixProb (θ : ℝ) (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (n : ℕ) :
    ProbabilityMeasure (D (bridgeHorizon n) ℝ) :=
  if h : (1 < θ ∧ θ ≤ 2) ∧ IsStableLevyLaw θ (bridgeHorizon n) (P (bridgeHorizon n)) then
    ⟨bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)),
      isProbabilityMeasure_bridgePrefixLaw h.1 (bridgeHorizon_pos n) (bridgeHorizon_lt_one n) h.2⟩
  else P (bridgeHorizon n)

/-- Under the hypotheses, `bridgePrefixProb` is the tilted prefix law. -/
theorem coe_bridgePrefixProb {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ))
    (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a)) (n : ℕ) :
    (bridgePrefixProb θ P n : Measure (D (bridgeHorizon n) ℝ)) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)) := by
  classical
  simp [bridgePrefixProb, hθ, hP _ (bridgeHorizon_pos n) (bridgeHorizon_lt_one n)]

/-- The tilted prefixes are compatible (from `bridgePrefix_consistent`). -/
theorem bridgePrefixProb_compatible {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a))
    (n : ℕ) :
    (bridgePrefixProb θ P (n + 1)).map
        (restrict (strictMono_bridgeHorizon.monotone (Nat.le_succ n))) =
      bridgePrefixProb θ P n := by
  apply Subtype.ext
  change Measure.map (BGW.Skorokhod.restrict
    (strictMono_bridgeHorizon.monotone (Nat.le_succ n)))
    (bridgePrefixProb θ P (n + 1) : Measure (D (bridgeHorizon (n + 1)) ℝ)) =
      (bridgePrefixProb θ P n : Measure (D (bridgeHorizon n) ℝ))
  simp only [coe_bridgePrefixProb hθ P hP]
  exact bridgePrefix_consistent hθ (bridgeHorizon_pos n)
    (strictMono_bridgeHorizon.monotone (Nat.le_succ n)) (bridgeHorizon_lt_one (n + 1))
    (hP _ (bridgeHorizon_pos n) (bridgeHorizon_lt_one n))
    (hP _ (bridgeHorizon_pos (n + 1)) (bridgeHorizon_lt_one (n + 1)))

/-- **Projective bridge: existence and uniqueness.** There is exactly one law on the open
bridge carrier whose `n`-th coordinate has the tilted law `w_{a_n} · P_{a_n}`. -/
theorem exists_unique_bridgeOpenLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ))
    (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a)) :
    ∃! Q : ProbabilityMeasure BridgeOpen,
      ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
        bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
          (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)) := by
  simpa only [coe_bridgePrefixProb hθ P hP] using
    exists_unique_compatiblePathLaw bridgeHorizon strictMono_bridgeHorizon bridgeHorizon_pos
      (bridgePrefixProb θ P) (bridgePrefixProb_compatible hθ P hP)


/-- Zero open path (junk). -/
def BridgeOpen.zero : BridgeOpen := ⟨fun _ => ⟨fun _ => 0, IsCadlag.const⟩, fun _ => rfl⟩

/-- **The open stable bridge law.** The `exists_unique_bridgeOpenLaw` witness for
`P = stableProcessLaw θ`; junk value (Dirac at the zero family) for `θ ∉ (1,2]`. -/
noncomputable def bridgeOpenLaw (θ : ℝ) : ProbabilityMeasure BridgeOpen :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    Classical.choose (exists_unique_bridgeOpenLaw hθ (fun a => stableProcessLaw θ a)
      (fun _ ha _ => isStableLevyLaw_stableProcessLaw hθ ha)).exists
  else ⟨Measure.dirac BridgeOpen.zero, inferInstance⟩

/-- Prefix characterization of the open stable bridge. -/
theorem map_coord_bridgeOpenLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (n : ℕ) :
    (bridgeOpenLaw θ : Measure BridgeOpen).map (CompatiblePaths.coord n) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (stableProcessLaw θ (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)) := by
  classical
  have heq : bridgeOpenLaw θ = Classical.choose (exists_unique_bridgeOpenLaw hθ
      (fun a => stableProcessLaw θ a)
      (fun _ ha _ => isStableLevyLaw_stableProcessLaw hθ ha)).exists := by
    exact dite_eq_left hθ
  rw [heq]
  exact (Classical.choose_spec (exists_unique_bridgeOpenLaw hθ
    (fun a => stableProcessLaw θ a)
    (fun _ ha _ => isStableLevyLaw_stableProcessLaw hθ ha)).exists) n

/-- Uniqueness of the open stable bridge law by its prefixes. -/
theorem eq_bridgeOpenLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure BridgeOpen}
    (hQ : ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (stableProcessLaw θ (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ))) :
    Q = bridgeOpenLaw θ := by
  exact (exists_unique_bridgeOpenLaw hθ (fun a => stableProcessLaw θ a)
    (fun _ ha _ => isStableLevyLaw_stableProcessLaw hθ ha)).unique hQ
      (map_coord_bridgeOpenLaw hθ)


end BGW.StableTrees
