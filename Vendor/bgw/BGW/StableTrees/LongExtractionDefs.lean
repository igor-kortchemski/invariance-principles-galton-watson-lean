/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ExitPartition
public import BGW.Skorokhod.CompleteMetricSpace
public import BGW.StableTrees.WalkPassage
public import BGW.StableTrees.StableExcursionSupport
public import BGW.StableTrees.MarkedExcursions
public import BGW.ContinuumTrees.ExcursionCarrier

/-!
# First long excursion and first long block: definitions

The first jump level of the passage process carrying an excursion of lifetime `> 1`, its marked
excursion, endpoints and stopped cut, the deterministic good-path predicate used for extraction,
and their discrete counterparts for scaled skip-free walks (ladder times, first long block,
endpoints and cut path).

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-! ### Continuum side -/

/-- The jump levels carrying a LONG excursion (lifetime `> 1`). -/
def longLabelSet (f : DLoc) : Set ℝ≥0 :=
  {x | x ∈ passageJumpSet f ∧ 1 < passageTime x f - passageTimeMinus x f}

/-- The first long label `L = inf {x ∈ J(f) | T_x - T_{x-} > 1}` (junk `0` when empty). -/
noncomputable def firstLongLabel (f : DLoc) : ℝ≥0 := sInf (longLabelSet f)

/-- The first long mark: the excursion cut at the first long label. -/
noncomputable def firstLongMark (f : DLoc) : Excursion := jumpExcursion (firstLongLabel f) f

/-- The selected physical interval `(T_{L-}, T_L)` as reals. -/
noncomputable def firstLongEnds (f : DLoc) : ℝ × ℝ :=
  ((passageTimeMinus (firstLongLabel f) f : ℝ≥0), (passageTime (firstLongLabel f) f : ℝ≥0))

/-- The limit triple `(g, d, cut restricted to [0,T])`. -/
noncomputable def longCutTriple (T : ℝ≥0) (f : DLoc) : ℝ × ℝ × D (T : ℝ) ℝ :=
  ((firstLongEnds f).1, (firstLongEnds f).2, excursionRestrict T (firstLongMark f))

/-- Regular excursion level: the geometric facts at a jump level `x` (see the module docstring,
item (iii)).  `R = reflectedFrom 0 f`; `R (t-)` is `Function.leftLim`. -/
def IsRegularExcursionLevel (f : DLoc) (x : ℝ≥0) : Prop :=
  cutValid (passageTimeMinus x f) (passageTime x f) f ∧
  ContinuousAt (reflectedFrom 0 f).1 (passageTimeMinus x f) ∧
  ContinuousAt (reflectedFrom 0 f).1 (passageTime x f) ∧
  (∀ a b : ℝ≥0, passageTimeMinus x f < a → a ≤ b → b < passageTime x f →
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ≥0, a ≤ t → t ≤ b →
      c ≤ (reflectedFrom 0 f).1 t ∧ c ≤ Function.leftLim (reflectedFrom 0 f).1 t) ∧
  (∀ η : ℝ≥0, 0 < η → ∃ x₁ x₂ : ℝ≥0, x₁ < x₂ ∧ x₂ < x ∧
    x₁ ∉ passageJumpSet f ∧ x₂ ∉ passageJumpSet f ∧
    passageTimeMinus x f < passageTime x₁ f + η ∧ passageTime x₂ f < passageTimeMinus x f) ∧
  (∀ η : ℝ≥0, 0 < η → ∃ x₁ x₂ : ℝ≥0, x < x₁ ∧ x₁ < x₂ ∧
    x₁ ∉ passageJumpSet f ∧ x₂ ∉ passageJumpSet f ∧
    passageTime x f < passageTime x₁ f ∧ passageTime x₂ f < passageTime x f + η)

/-- **Good path for first-long-excursion extraction** on the horizon `[0, M]`.  A bundle of
geometric facts about `f`; convergence of the extraction is NOT a field. -/
structure GoodLongExtractionPath (M : ℝ≥0) (f : DLoc) : Prop where
  zero : f.1 0 = 0
  /-- passage at level zero happens at time zero (excludes an initial plateau at the minimum;
  under the stable law this is `(ae_passageTime_eq_firstPassageBelow hθ).2`) -/
  passageZero : passageTime 0 f = 0
  noNegJumps : NoNegJumps f
  infContinuous : Continuous (runningInfLoc f)
  finitePassage : ∀ x : ℝ≥0, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)
  creeping : ∀ x : ℝ≥0, f.1 (passageTime x f) = -(x : ℝ)
  strictMono : StrictMono (fun x : ℝ≥0 => passageTime x f)
  regular : ∀ x ∈ passageJumpSet f, IsRegularExcursionLevel f x
  noLifetimeOne : ∀ x ∈ passageJumpSet f, passageTime x f - passageTimeMinus x f ≠ 1
  hasLongLabel : ∃ L, IsLeast (longLabelSet f) L
  end_lt : passageTime (firstLongLabel f) f < M

/-- Good path plus continuity of the selected cut at the cutoff `T`. -/
def GoodLongExtractionCutPath (M T : ℝ≥0) (f : DLoc) : Prop :=
  GoodLongExtractionPath M f ∧ ContinuousAt (firstLongMark f).path.1 T

/-! ### Discrete side -/

/-- A skip-free increment: `ξ - 1` with `ξ ∈ ℕ`. -/
def IsSkipFreeIncrement (a : ℝ) : Prop := ∃ k : ℕ, a = (k : ℝ) - 1

/-- Ladder time `L_r`: the (weak) hit of `(-∞, -r]`, finite reading. -/
noncomputable def ladderTime (ω : ℕ → ℝ) (r : ℕ) : ℕ := (walkHitTime r ω).toNat

/-- Blocks of size at least `n` (the block must exist: its end is a finite hit). -/
def longBlockSet (n : ℕ) (ω : ℕ → ℝ) : Set ℕ :=
  {r | walkHitTime (r + 1) ω ≠ ⊤ ∧ n ≤ ladderTime ω (r + 1) - ladderTime ω r}

/-- Index of the first long block (junk `0` when none). -/
noncomputable def firstLongIndex (n : ℕ) (ω : ℕ → ℝ) : ℕ := sInf (longBlockSet n ω)

/-- Selected endpoints `(L_r / n, L_{r+1} / n)` of the first long block. -/
noncomputable def extractionEndpoints (n : ℕ) (ω : ℕ → ℝ) : ℝ × ℝ :=
  ((ladderTime ω (firstLongIndex n ω) : ℝ) / n,
    (ladderTime ω (firstLongIndex n ω + 1) : ℝ) / n)

/-- Increments of block `r` with the final `-1` step replaced by `0` (and `0` afterwards). -/
noncomputable def blockIncrements (ω : ℕ → ℝ) (r : ℕ) (i : ℕ) : ℝ :=
  if i + 1 < ladderTime ω (r + 1) - ladderTime ω r then ω (ladderTime ω r + i) else 0

/-- The extraction triple `(g_n, d_n, cut_n)` at scale `n`, norming `b`, cutoff `T`. -/
noncomputable def extractionTriple (b : ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    ℝ × ℝ × D (T : ℝ) ℝ :=
  ((extractionEndpoints n ω).1, (extractionEndpoints n ω).2,
    realStepPath (T : ℝ) n b (blockIncrements ω (firstLongIndex n ω)))

end BGW.StableTrees
