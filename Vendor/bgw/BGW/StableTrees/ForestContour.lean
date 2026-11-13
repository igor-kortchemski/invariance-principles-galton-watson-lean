/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightness
public import BGW.Tree.ContourBracket
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The padded contour of a discrete forest

The forest is explored block by block, with two zero contour units after each
tree. Its contour is bracketed by the record-count height process, with a
normalized uniform-error estimate stated in terms of height oscillation and
adjacent height jumps.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace BGW.StableTrees.ForestContour

open BGW.PlaneTree
open BGW.StableTrees.DiscreteForest BGW.StableTrees.HeightTightness

/-- The discrete σ-algebra on plane trees, used locally for countable sums over trees. -/
local instance forestContourTreeMeasurable : MeasurableSpace PlaneTree := ⊤
local instance forestContourTreeSingleton : MeasurableSingletonClass PlaneTree :=
  ⟨fun _ => trivial⟩
/-- The discrete σ-algebra on words of natural numbers, used locally for countable sums. -/
local instance forestContourWordMeasurable : MeasurableSpace (List ℕ) := ⊤
local instance forestContourWordSingleton : MeasurableSingletonClass (List ℕ) :=
  ⟨fun _ => trivial⟩

/-- The block whose padded contour interval `[2 L r, 2 L (r+1))` contains the integer time `m`
(junk `0` when no block does, which happens only off `LadderFinite`). -/
noncomputable def contourBlock (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  sInf {r | m < 2 * ladderTime ω (r + 1)}

/-- **Padded forest contour** at integer time `m`: the contour of `blockTree ω r` at local time
`m - 2 L r`, `r = contourBlock ω m`, so that tree `r` occupies `[2 L r, 2 L (r+1)]` (its contour,
then two zero units); junk `0` off `LadderFinite`. -/
noncomputable def forestContour (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  if LadderFinite ω then
    (blockTree ω (contourBlock ω m)).contourAt (m - 2 * ladderTime ω (contourBlock ω m))
  else 0

/-- Linear interpolation of the padded forest contour at integer times. -/
noncomputable def forestContourLin (ω : ℕ → ℕ) (s : ℝ) : ℝ :=
  (1 - (s - ⌊s⌋₊)) * (forestContour ω ⌊s⌋₊ : ℝ) +
    (s - ⌊s⌋₊) * (forestContour ω (⌊s⌋₊ + 1) : ℝ)

/-- The normalized contour path `t ↦ (B n / n) * forestContourLin ω (2 n t)` on `[0,T]` (the
junk branch never occurs, `continuous_forestContourLin`). -/
noncomputable def forestContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  if h : Continuous (forestContourLin ω) then
    ⟨fun t => (B n / n) * forestContourLin ω (2 * (n : ℝ) * (t : ℝ)),
      continuous_const.mul (h.comp (continuous_const.mul continuous_subtype_val))⟩
  else 0

/-- The uniform distance on `[0,T]` between the normalized contour at time `2nt` and the
normalized interpolated height at time `nt`. -/
noncomputable def forestContourHeightError (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) (T : ℝ),
    |B n / n * forestContourLin ω (2 * (n : ℝ) * (t : ℝ)) -
      B n / n * forestHeightLin ω ((n : ℝ) * (t : ℝ))|

private theorem forestContourLin_cell (ω : ℕ → ℕ) (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc (n : ℝ) (n + 1)) :
    forestContourLin ω s = (1 - (s - n)) * (forestContour ω n : ℝ) +
      (s - n) * (forestContour ω (n + 1) : ℝ) := by
  by_cases he : s = n + 1
  · subst s
    have hf : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    simp [forestContourLin, hf]
  · have hf : ⌊s⌋₊ = n := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) hs.1)).2
      ⟨hs.1, lt_of_le_of_ne hs.2 he⟩
    simp only [forestContourLin, hf]

private theorem continuousOn_forestContourLin_cell (ω : ℕ → ℕ) (n : ℕ) :
    ContinuousOn (forestContourLin ω) (Icc (n : ℝ) (n + 1)) := by
  apply ContinuousOn.congr (f := fun s : ℝ =>
    (1 - (s - n)) * (forestContour ω n : ℝ) +
      (s - n) * (forestContour ω (n + 1) : ℝ)) (by fun_prop)
  intro s hs
  exact forestContourLin_cell ω n hs

private theorem continuousOn_forestContourLin_Iic (ω : ℕ → ℕ) (n : ℕ) :
    ContinuousOn (forestContourLin ω) (Iic (n : ℝ)) := by
  induction n with
  | zero =>
    apply ContinuousOn.congr (f := fun s : ℝ =>
      (1 - s) * (forestContour ω 0 : ℝ) + s * (forestContour ω 1 : ℝ)) (by fun_prop)
    intro s hs
    have hs0 : s ≤ 0 := by simpa using hs
    have hf : ⌊s⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [forestContourLin, hf]
  | succ n ih =>
    have hu : Iic (n : ℝ) ∪ Icc (n : ℝ) (n + 1) = Iic ((n + 1 : ℕ) : ℝ) := by
      ext s
      simp only [mem_union, mem_Iic, mem_Icc, Nat.cast_add, Nat.cast_one]
      constructor
      · rintro (h | h) <;> linarith [h]
      · intro h
        rcases le_total s (n : ℝ) with hn | hn
        · exact Or.inl hn
        · exact Or.inr ⟨hn, h⟩
    rw [← hu]
    exact ih.union_of_isClosed (continuousOn_forestContourLin_cell ω n)
      isClosed_Iic isClosed_Icc

/-- The interpolated padded contour is continuous. -/
theorem continuous_forestContourLin (ω : ℕ → ℕ) : Continuous (forestContourLin ω) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hs : s < ((⌊s⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one s
  exact (continuousOn_forestContourLin_Iic ω (⌊s⌋₊ + 1)).continuousAt (Iic_mem_nhds hs)

/-- Evaluation of the normalized padded-contour path. -/
theorem forestContourPath_apply (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    forestContourPath B n T ω t = B n / n * forestContourLin ω (2 * (n : ℝ) * (t : ℝ)) := by
  unfold forestContourPath
  split
  · rfl
  · rename_i h
    exact (h (continuous_forestContourLin ω)).elim

private theorem measurable_ladderTime_block (m r : ℕ) :
    MeasurableSet {ω : ℕ → ℕ | m < 2 * ladderTime ω (r + 1)} := by
  exact measurableSet_lt measurable_const
    (measurable_const.mul (measurable_ladderTime (r + 1)))

private theorem measurable_nat_contourFirstHit {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → ℕ → Prop) (hp : ∀ k, MeasurableSet {ω | p ω k}) :
    Measurable (fun ω => sInf {k | p ω k}) := by
  apply measurable_to_nat
  intro ω₀
  let n := sInf {k | p ω₀ k}
  change MeasurableSet {ω | sInf {k | p ω k} = n}
  by_cases hn : n = 0
  · rw [hn]
    have heq : {ω | sInf {k | p ω k} = 0} =
        {ω | p ω 0} ∪ ⋂ k, {ω | ¬p ω k} := by
      ext ω
      simp only [Nat.sInf_eq_zero, mem_union, mem_iInter, mem_ofPred_eq,
        Set.eq_empty_iff_forall_notMem]
    rw [heq]
    exact (hp 0).union (MeasurableSet.iInter fun k => (hp k).compl)
  · have heq : {ω | sInf {k | p ω k} = n} =
        {ω | p ω n} ∩ ⋂ k : ℕ, ⋂ (_ : k < n), {ω | ¬p ω k} := by
      ext ω
      simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · intro h
        have hex : Set.Nonempty {k | p ω k} :=
          Nat.nonempty_of_pos_sInf (by omega)
        refine ⟨h ▸ Nat.sInf_mem hex, ?_⟩
        intro k hk
        exact Nat.notMem_of_lt_sInf (h.symm ▸ hk)
      · intro h
        rw [Nat.sInf_def (s := {k | p ω k}) ⟨n, h.1⟩]
        exact (Nat.find_eq_iff _).mpr h
    rw [heq]
    exact (hp n).inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (hp k).compl)

private theorem measurable_contourBlock (m : ℕ) : Measurable (fun ω => contourBlock ω m) :=
  measurable_nat_contourFirstHit _ (measurable_ladderTime_block m)

private theorem measurableSet_ladderFinite : MeasurableSet {ω : ℕ → ℕ | LadderFinite ω} := by
  have heq : {ω : ℕ → ℕ | LadderFinite ω} =
      ⋂ r : ℕ, ⋃ k : ℕ, {ω | walk ω k = -(r : ℤ)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, LadderFinite]
  rw [heq]
  exact MeasurableSet.iInter fun r => MeasurableSet.iUnion fun k =>
    measurableSet_eq_fun (measurable_walk k) measurable_const

private theorem measurable_blockTree' (r : ℕ) : Measurable (fun ω => blockTree ω r) := by
  exact (measurable_of_countable (fun a : List ℕ =>
    (PlaneTree.ofDegrees? a).getD (PlaneTree.node []))).comp (measurable_blockDegrees r)

/-- Each integer-time padded-contour coordinate is measurable. -/
theorem measurable_forestContour (m : ℕ) : Measurable (fun ω => forestContour ω m) := by
  unfold forestContour
  apply Measurable.ite measurableSet_ladderFinite
  · have hr : Measurable (fun ω : ℕ → ℕ => contourBlock ω m) := measurable_contourBlock m
    have ht : Measurable (fun ω : ℕ → ℕ => blockTree ω (contourBlock ω m)) := by
      have hp : Measurable (fun p : (ℕ → ℕ) × ℕ => blockTree p.1 p.2) :=
        measurable_from_prod_countable_left fun r => measurable_blockTree' r
      exact hp.comp (measurable_id.prodMk hr)
    have hla : Measurable (fun p : (ℕ → ℕ) × ℕ => ladderTime p.1 p.2) :=
      measurable_from_prod_countable_left fun r => measurable_ladderTime r
    have hpair : Measurable (fun ω : ℕ → ℕ => (ω, contourBlock ω m)) :=
      measurable_id.prodMk hr
    have hl : Measurable (fun ω : ℕ → ℕ =>
        m - 2 * ladderTime ω (contourBlock ω m)) :=
      measurable_const.sub (measurable_const.mul (hla.comp hpair))
    exact (measurable_of_countable (fun p : PlaneTree × ℕ => p.1.contourAt p.2)).comp
      (ht.prodMk hl)
  · exact measurable_const

/-- The normalized padded-contour path on a compact horizon is measurable. -/
theorem measurable_forestContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestContourPath B n T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  simp_rw [forestContourPath_apply]
  unfold forestContourLin
  have hc : Measurable (fun a : ℕ => (a : ℝ)) := measurable_of_countable _
  exact (measurable_const.mul (hc.comp (measurable_forestContour _))).add
    (measurable_const.mul (hc.comp (measurable_forestContour _))) |>.const_mul _

private theorem dist_forestPaths (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    dist (forestContourPath B n T ω) (forestHeightPath B n T ω) =
      forestContourHeightError B n T ω := by
  rw [ContinuousMap.dist_eq_iSup]
  unfold forestContourHeightError
  apply iSup_congr
  intro t
  rw [forestContourPath_apply]
  rfl

/-- The uniform contour/height error is measurable. -/
theorem measurable_forestContourHeightError (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestContourHeightError B n T) := by
  change Measurable (fun ω : ℕ → ℕ => forestContourHeightError B n T ω)
  simp_rw [← dist_forestPaths]
  exact (measurable_forestContourPath B n T).dist
    (measurable_forestPairPath B n T).snd

/-- The error is the uniform distance between the contour and height paths. -/
theorem dist_forestContourPath_forestHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (ω : ℕ → ℕ) :
    dist (forestContourPath B n T ω) (forestHeightPath B n T ω) =
      forestContourHeightError B n T ω :=
  dist_forestPaths B n T ω

/-! ### Tree-by-tree adapters to K12a -/

/-- The padded clock: tree `r` occupies `2 z_r` time units, also when it is a singleton. -/
theorem two_mul_ladderTime_succ {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    2 * ladderTime ω (r + 1) = 2 * ladderTime ω r + 2 * (blockTree ω r).size := by
  rw [size_blockTree hω]
  have h := ladderTime_lt_succ hω r
  omega

private theorem contourBlock_eq {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    {m : ℕ} (hm : m < 2 * (blockTree ω r).size) :
    contourBlock ω (2 * ladderTime ω r + m) = r := by
  apply le_antisymm
  · apply Nat.sInf_le
    change 2 * ladderTime ω r + m < 2 * ladderTime ω (r + 1)
    rw [two_mul_ladderTime_succ hω]
    omega
  · apply Nat.le_of_not_gt
    intro hqr
    have hupper : 2 * ladderTime ω r + m < 2 * ladderTime ω (r + 1) := by
      rw [two_mul_ladderTime_succ hω]
      omega
    have hmem := Nat.sInf_mem (s := {q | 2 * ladderTime ω r + m <
      2 * ladderTime ω (q + 1)}) ⟨r, hupper⟩
    change 2 * ladderTime ω r + m <
      2 * ladderTime ω (contourBlock ω (2 * ladderTime ω r + m) + 1) at hmem
    have hmono := (strictMono_nat_of_lt_succ (ladderTime_lt_succ hω)).monotone
      (show contourBlock ω (2 * ladderTime ω r + m) + 1 ≤ r by omega)
    omega

/-- On block `r` the padded forest contour is the contour of `blockTree ω r`, followed by two
zero units (local times `2 z_r - 2` and `2 z_r - 1`). -/
theorem forestContour_two_mul_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    {m : ℕ} (hm : m < 2 * (blockTree ω r).size) :
    forestContour ω (2 * ladderTime ω r + m) = (blockTree ω r).contourAt m := by
  simp only [forestContour, hω, ↓reduceIte, contourBlock_eq hω r hm,
    Nat.add_sub_cancel_left]

private theorem forestHeight_ladderTime_eq_zero {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    forestHeight ω (ladderTime ω r) = 0 := by
  have h := forestHeight_eq_treeHeight hω r 0 (size_pos _)
  simp only [Nat.add_zero] at h
  rw [h]
  generalize blockTree ω r = t
  cases t with
  | node ts => rfl

private theorem forestContour_ladderTime_eq_zero {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    forestContour ω (2 * ladderTime ω r) = 0 := by
  rw [show 2 * ladderTime ω r = 2 * ladderTime ω r + 0 by omega,
    forestContour_two_mul_ladderTime_add hω r
      (by have := size_pos (blockTree ω r); omega)]
  generalize blockTree ω r = t
  cases t
  simp [contourAt]

private theorem forestContour_two_mul_ladderTime_add_le {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (r : ℕ) {m : ℕ} (hm : m ≤ 2 * (blockTree ω r).size) :
    forestContour ω (2 * ladderTime ω r + m) = (blockTree ω r).contourAt m := by
  rcases lt_or_eq_of_le hm with h | h
  · exact forestContour_two_mul_ladderTime_add hω r h
  · subst m
    have hend : 2 * ladderTime ω r + 2 * (blockTree ω r).size =
        2 * ladderTime ω (r + 1) := (two_mul_ladderTime_succ hω r).symm
    rw [hend, forestContour_ladderTime_eq_zero hω]
    exact (contourAt_of_lt _ (by have := size_pos (blockTree ω r); omega)).symm

/-- Forest heights on block `r` are the DFS heights of `blockTree ω r`, including the value
`0` at index `z_r` (the next root). -/
theorem forestHeight_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) {i : ℕ}
    (hi : i ≤ (blockTree ω r).size) :
    forestHeight ω (ladderTime ω r + i) = (blockTree ω r).heightSeq i := by
  by_cases hi' : i < (blockTree ω r).size
  · rw [forestHeight_eq_treeHeight hω r i hi', heightSeq_of_lt _ hi']
  · have hieq : i = (blockTree ω r).size := by omega
    subst i
    have hend : ladderTime ω r + (blockTree ω r).size = ladderTime ω (r + 1) := by
      rw [size_blockTree hω]
      have := ladderTime_lt_succ hω r
      omega
    rw [hend, forestHeight_ladderTime_eq_zero hω, heightSeq_of_le _ le_rfl]

private theorem forestContourLin_add_nat (ω : ℕ → ℕ) (a : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    forestContourLin ω ((a : ℝ) + s) =
      (1 - (s - ⌊s⌋₊)) * (forestContour ω (a + ⌊s⌋₊) : ℝ) +
        (s - ⌊s⌋₊) * (forestContour ω (a + ⌊s⌋₊ + 1) : ℝ) := by
  have hf : ⌊(a : ℝ) + s⌋₊ = a + ⌊s⌋₊ := by
    calc
      ⌊(a : ℝ) + s⌋₊ = ⌊s⌋₊ + a := by rw [add_comm, Nat.floor_add_natCast hs]
      _ = a + ⌊s⌋₊ := Nat.add_comm _ _
  rw [forestContourLin, hf]
  push_cast
  ring

private theorem forestHeightLin_add_nat (ω : ℕ → ℕ) (a : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    forestHeightLin ω ((a : ℝ) + u) =
      (1 - (u - ⌊u⌋₊)) * (forestHeight ω (a + ⌊u⌋₊) : ℝ) +
        (u - ⌊u⌋₊) * (forestHeight ω (a + ⌊u⌋₊ + 1) : ℝ) := by
  have hf : ⌊(a : ℝ) + u⌋₊ = a + ⌊u⌋₊ := by
    calc
      ⌊(a : ℝ) + u⌋₊ = ⌊u⌋₊ + a := by rw [add_comm, Nat.floor_add_natCast hu]
      _ = a + ⌊u⌋₊ := Nat.add_comm _ _
  rw [forestHeightLin, hf]
  push_cast
  ring

/-- Interpolated form, on the closed block `[2 L r, 2 L r + 2 z_r]`. -/
theorem forestContourLin_two_mul_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 * (blockTree ω r).size) :
    forestContourLin ω (2 * ladderTime ω r + s) = (blockTree ω r).contourLin s := by
  rw [show (2 * ladderTime ω r : ℝ) = ((2 * ladderTime ω r : ℕ) : ℝ) by norm_cast,
    forestContourLin_add_nat ω (2 * ladderTime ω r) hs0, contourLin]
  by_cases hend : s = 2 * (blockTree ω r).size
  · subst s
    have hf : ⌊(2 : ℝ) * ((blockTree ω r).size : ℝ)⌋₊ = 2 * (blockTree ω r).size := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.floor_natCast (2 * (blockTree ω r).size))
    simp only [hf, Nat.cast_mul, Nat.cast_ofNat, sub_self, sub_zero, zero_mul, add_zero, one_mul]
    exact_mod_cast forestContour_two_mul_ladderTime_add_le hω r le_rfl
  · have hslt : s < 2 * ((blockTree ω r).size : ℝ) := lt_of_le_of_ne hs hend
    have hk : ⌊s⌋₊ < 2 * (blockTree ω r).size := by
      have hk' : (⌊s⌋₊ : ℝ) < 2 * ((blockTree ω r).size : ℝ) :=
        lt_of_le_of_lt (Nat.floor_le hs0) hslt
      exact_mod_cast hk'
    rw [forestContour_two_mul_ladderTime_add_le hω r (m := ⌊s⌋₊) (by omega),
      show 2 * ladderTime ω r + ⌊s⌋₊ + 1 = 2 * ladderTime ω r + (⌊s⌋₊ + 1) by omega,
      forestContour_two_mul_ladderTime_add_le hω r (m := ⌊s⌋₊ + 1) (by omega)]

/-- Interpolated form, on the closed block `[L r, L r + z_r]`. -/
theorem forestHeightLin_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (blockTree ω r).size) :
    forestHeightLin ω (ladderTime ω r + u) = (blockTree ω r).heightLin u := by
  rw [show (ladderTime ω r : ℝ) = ((ladderTime ω r : ℕ) : ℝ) by norm_cast,
    forestHeightLin_add_nat ω (ladderTime ω r) hu0, heightLin]
  by_cases hend : u = (blockTree ω r).size
  · subst u
    simpa using forestHeight_ladderTime_add hω r le_rfl
  · have hult : u < ((blockTree ω r).size : ℝ) := lt_of_le_of_ne hu hend
    have hk : ⌊u⌋₊ < (blockTree ω r).size := by
      have hk' : (⌊u⌋₊ : ℝ) < ((blockTree ω r).size : ℝ) :=
        lt_of_le_of_lt (Nat.floor_le hu0) hult
      exact_mod_cast hk'
    rw [forestHeight_ladderTime_add hω r (i := ⌊u⌋₊) (by omega),
      show ladderTime ω r + ⌊u⌋₊ + 1 = ladderTime ω r + (⌊u⌋₊ + 1) by omega,
      forestHeight_ladderTime_add hω r (i := ⌊u⌋₊ + 1) (by omega)]

/-! ### Forest bracketing -/

/-- **Forest first visit**: the DFS vertex of global index `k` is first visited by the padded
contour at time `b_k = 2k - H_k`. -/
theorem forestContour_firstVisit {ω : ℕ → ℕ} (hω : LadderFinite ω) (k : ℕ) :
    forestContour ω (2 * k - forestHeight ω k) = forestHeight ω k := by
  obtain ⟨r, hkr, hkrs⟩ := exists_ladderTime_le_lt hω k
  let i := k - ladderTime ω r
  have hi : i < (blockTree ω r).size := by
    rw [size_blockTree hω]
    dsimp [i]
    omega
  have hk : k = ladderTime ω r + i := by dsimp [i]; omega
  have hH : forestHeight ω k = (blockTree ω r).heightSeq i := by
    rw [hk, forestHeight_ladderTime_add hω r hi.le]
  have htime : 2 * k - forestHeight ω k =
      2 * ladderTime ω r + (2 * i - (blockTree ω r).heightSeq i) := by
    rw [hH]
    have hHi := heightSeq_le (blockTree ω r) i
    omega
  rw [htime, forestContour_two_mul_ladderTime_add hω r (by omega), hH,
    contourAt_firstVisit _ hi]

/-- **Integer forest bracketing**: between the first visits `b_k` and `b_{k+1}`, the padded
contour stays within `|H_{k+1} - H_k| + 1` of `H_k` (across a tree boundary, `H_{k+1} = 0`). -/
theorem forestContour_bracket {ω : ℕ → ℕ} (hω : LadderFinite ω) {k m : ℕ}
    (hm1 : 2 * k - forestHeight ω k ≤ m) (hm2 : m ≤ 2 * (k + 1) - forestHeight ω (k + 1)) :
    |(forestContour ω m : ℤ) - forestHeight ω k| ≤
      |(forestHeight ω (k + 1) : ℤ) - forestHeight ω k| + 1 := by
  obtain ⟨r, hkr, hkrs⟩ := exists_ladderTime_le_lt hω k
  let i := k - ladderTime ω r
  have hi : i < (blockTree ω r).size := by
    rw [size_blockTree hω]
    dsimp [i]
    omega
  have hk : k = ladderTime ω r + i := by dsimp [i]; omega
  have hH : forestHeight ω k = (blockTree ω r).heightSeq i := by
    rw [hk, forestHeight_ladderTime_add hω r hi.le]
  have hnext : forestHeight ω (k + 1) = (blockTree ω r).heightSeq (i + 1) := by
    rw [show k + 1 = ladderTime ω r + (i + 1) by omega,
      forestHeight_ladderTime_add hω r (by omega)]
  have hb : 2 * k - forestHeight ω k =
      2 * ladderTime ω r + (2 * i - (blockTree ω r).heightSeq i) := by
    rw [hH]
    have := heightSeq_le (blockTree ω r) i
    omega
  have hbnext : 2 * (k + 1) - forestHeight ω (k + 1) =
      2 * ladderTime ω r + (2 * (i + 1) - (blockTree ω r).heightSeq (i + 1)) := by
    rw [hnext]
    have := heightSeq_le (blockTree ω r) (i + 1)
    omega
  have hbase : 2 * ladderTime ω r ≤ m := by omega
  have hm : m = 2 * ladderTime ω r + (m - 2 * ladderTime ω r) := by omega
  have hmlocal : m - 2 * ladderTime ω r ≤ 2 * (blockTree ω r).size := by
    have hsize := size_blockTree hω r
    omega
  rw [hm, forestContour_two_mul_ladderTime_add_le hω r hmlocal, hH, hnext]
  apply contourAt_bracket _ hi
  · omega
  · omega

private theorem contourBlock_spec {ω : ℕ → ℕ} (hω : LadderFinite ω) (m : ℕ) :
    2 * ladderTime ω (contourBlock ω m) ≤ m ∧
      m < 2 * ladderTime ω (contourBlock ω m + 1) := by
  obtain ⟨q, _, hq⟩ := exists_ladderTime_le_lt hω m
  have hex : Set.Nonempty {r | m < 2 * ladderTime ω (r + 1)} :=
    ⟨q, by show m < 2 * ladderTime ω (q + 1); omega⟩
  have hu : m < 2 * ladderTime ω (contourBlock ω m + 1) := Nat.sInf_mem hex
  refine ⟨?_, hu⟩
  by_cases hz : contourBlock ω m = 0
  · simp [hz, ladderTime_zero]
  · have hprev : contourBlock ω m - 1 < contourBlock ω m :=
      Nat.sub_lt (Nat.zero_lt_of_ne_zero hz) zero_lt_one
    have hn := Nat.notMem_of_lt_sInf (s := {r | m < 2 * ladderTime ω (r + 1)}) hprev
    have hsucc : contourBlock ω m - 1 + 1 = contourBlock ω m :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)
    simp only [mem_ofPred_eq, hsucc] at hn
    omega

/-- **Real-time forest bracketing**: every contour time `s ≥ 0` lies in a bracket `k` with
`s/2 - 1 ≤ k ≤ s/2 + H_k/2`, and the interpolated contour at `s` is within
`|H_{k+1} - H_k| + 1` of `H_k`. -/
theorem forestContourLin_bracket {ω : ℕ → ℕ} (hω : LadderFinite ω) {s : ℝ} (hs : 0 ≤ s) :
    ∃ k : ℕ, s / 2 - 1 ≤ k ∧ (k : ℝ) ≤ s / 2 + (forestHeight ω k : ℝ) / 2 ∧
      |forestContourLin ω s - forestHeight ω k| ≤
        |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| + 1 := by
  let r := contourBlock ω ⌊s⌋₊
  let u := s - 2 * (ladderTime ω r : ℝ)
  have hblock := contourBlock_spec hω ⌊s⌋₊
  have hu0 : 0 ≤ u := by
    have hf := Nat.floor_le hs
    have hb : (2 : ℝ) * (ladderTime ω r : ℝ) ≤ (⌊s⌋₊ : ℝ) := by
      exact_mod_cast hblock.1
    dsimp [u]
    linarith
  have hu : u ≤ 2 * (blockTree ω r).size := by
    have hf := Nat.lt_floor_add_one s
    have hsize := two_mul_ladderTime_succ hω r
    change s - 2 * (ladderTime ω r : ℝ) ≤ 2 * ((blockTree ω r).size : ℝ)
    have hupper : ⌊s⌋₊ < 2 * ladderTime ω (r + 1) := hblock.2
    have hupperR : (⌊s⌋₊ : ℝ) < 2 * (ladderTime ω (r + 1) : ℝ) := by exact_mod_cast hupper
    have hupperSuccR : (⌊s⌋₊ : ℝ) + 1 ≤ 2 * (ladderTime ω (r + 1) : ℝ) := by
      exact_mod_cast (show ⌊s⌋₊ + 1 ≤ 2 * ladderTime ω (r + 1) by omega)
    have hsizeR : 2 * (ladderTime ω (r + 1) : ℝ) =
        2 * (ladderTime ω r : ℝ) + 2 * ((blockTree ω r).size : ℝ) := by exact_mod_cast hsize
    nlinarith
  obtain ⟨i, hi, hlo, hhi, hC⟩ := contourLin_bracket (blockTree ω r) hu0 hu
  refine ⟨ladderTime ω r + i, ?_, ?_, ?_⟩
  · push_cast
    dsimp [u] at hlo
    nlinarith
  · have hH := forestHeight_ladderTime_add hω r hi.le
    change ((ladderTime ω r + i : ℕ) : ℝ) ≤
      s / 2 + (forestHeight ω (ladderTime ω r + i) : ℝ) / 2
    rw [hH]
    push_cast
    dsimp [u] at hhi
    nlinarith
  · have hH := forestHeight_ladderTime_add hω r hi.le
    have hnext := forestHeight_ladderTime_add hω r (i := i + 1) (by omega)
    have hcont : forestContourLin ω s = (blockTree ω r).contourLin u := by
      rw [show s = 2 * (ladderTime ω r : ℝ) + u by dsimp [u]; ring]
      exact forestContourLin_two_mul_ladderTime_add hω r hu0 hu
    rw [hcont, hH]
    simpa only [Nat.add_assoc, hnext] using hC

private theorem forestHeight_le_self (ω : ℕ → ℕ) (hω : LadderFinite ω) (k : ℕ) :
    forestHeight ω k ≤ k := by
  obtain ⟨r, hkr, hkrs⟩ := exists_ladderTime_le_lt hω k
  let i := k - ladderTime ω r
  have hi : i < (blockTree ω r).size := by
    rw [size_blockTree hω]
    dsimp [i]
    omega
  have hH : forestHeight ω k = (blockTree ω r).heightSeq i := by
    rw [show k = ladderTime ω r + i by dsimp [i]; omega,
      forestHeight_ladderTime_add hω r hi.le]
  rw [hH]
  exact (heightSeq_le (blockTree ω r) i).trans (by dsimp [i]; omega)

/-- **Normalized deterministic bound**: if `w ≥ 1` bounds half the heights of indices `≤ 2nT`
and `w + 1 ≤ n`, the contour/height error on `[0,T]` is at most the height oscillation at
scale `w/n` plus the largest adjacent jump, both on the horizon `T + 1`, plus `B_n/n`. -/
theorem forestContourHeightError_le {ω : ℕ → ℕ} (hω : LadderFinite ω) (B : ℕ → ℝ) {n : ℕ}
    (hB : 0 ≤ B n) (T : ℝ≥0) {w : ℝ} (hw1 : 1 ≤ w) (hwn : w + 1 ≤ n)
    (hw : ∀ j : ℕ, (j : ℝ) ≤ 2 * n * T → (forestHeight ω j : ℝ) / 2 ≤ w) :
    forestContourHeightError B n T ω ≤
      heightOscillation B n ((T : ℝ) + 1) (w / n) ω + maxHeightJump B n ((T : ℝ) + 1) ω +
        B n / n := by
  have hnNat : 0 < n := by
    have hn : (2 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast (show 0 < (n : ℝ) by linarith)
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnNat
  have ha : 0 ≤ B n / (n : ℝ) := div_nonneg hB (Nat.cast_nonneg n)
  let _ : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, by simp⟩⟩
  apply ciSup_le
  intro t
  let u : ℝ := (n : ℝ) * (t : ℝ)
  have hu0 : 0 ≤ u := mul_nonneg (Nat.cast_nonneg n) t.2.1
  obtain ⟨k, hklo, hkhi, hC⟩ := forestContourLin_bracket hω
    (s := 2 * u) (by positivity)
  have hHleNat : forestHeight ω k ≤ k := forestHeight_le_self ω hω k
  have hHle : (forestHeight ω k : ℝ) ≤ (k : ℝ) := by exact_mod_cast hHleNat
  have huT : u ≤ (n : ℝ) * (T : ℝ) := by
    dsimp [u]
    exact mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg n)
  have hk2u : (k : ℝ) ≤ 2 * u := by nlinarith
  have hkT : (k : ℝ) ≤ 2 * (n : ℝ) * (T : ℝ) := by nlinarith
  have hHhalf := hw k (by nlinarith [hkT])
  have hku : (k : ℝ) ≤ u + w := by nlinarith
  have hdist : |(k : ℝ) - u| ≤ w := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hkNR : (k : ℝ) ≤ (n : ℝ) * ((T : ℝ) + 1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr t.2.1)]
  let x : Set.Icc (0 : ℝ) ((T : ℝ) + 1) :=
    ⟨(k : ℝ) / n, div_nonneg (Nat.cast_nonneg k) hn.le,
      (div_le_iff₀ hn).2 (by nlinarith [hkNR])⟩
  let y : Set.Icc (0 : ℝ) ((T : ℝ) + 1) :=
    ⟨(t : ℝ), t.2.1, by linarith [t.2.2]⟩
  have hxy : |(x : ℝ) - y| ≤ w / n := by
    change |(k : ℝ) / n - (t : ℝ)| ≤ w / n
    have heq : (k : ℝ) / n - (t : ℝ) = ((k : ℝ) - u) / n := by
      dsimp [u]
      field_simp
    rw [heq, abs_div, abs_of_pos hn]
    exact (div_le_div_iff_of_pos_right hn).2 hdist
  have hosc := heightDifference_le_heightOscillation B n (by positivity) ω x y hxy
  have hkdiv : (n : ℝ) * ((k : ℝ) / n) = (k : ℝ) := mul_div_cancel₀ _ hn.ne'
  have hHk : forestHeightLin ω ((n : ℝ) * (x : ℝ)) = forestHeight ω k := by
    change forestHeightLin ω ((n : ℝ) * ((k : ℝ) / n)) = forestHeight ω k
    rw [hkdiv]
    simp [forestHeightLin]
  change |B n / n * forestHeightLin ω ((n : ℝ) * (x : ℝ)) - B n / n * forestHeightLin ω u| ≤
    heightOscillation B n ((T : ℝ) + 1) (w / n) ω at hosc
  rw [hHk] at hosc
  have hkFloor : k ≤ ⌊(n : ℝ) * ((T : ℝ) + 1)⌋₊ := Nat.le_floor hkNR
  have hjumpNat : ((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs ≤
      (Finset.range (⌊(n : ℝ) * ((T : ℝ) + 1)⌋₊ + 1)).sup
        (fun j => ((forestHeight ω (j + 1) : ℤ) - forestHeight ω j).natAbs) :=
    Finset.le_sup (f := fun j => ((forestHeight ω (j + 1) : ℤ) - forestHeight ω j).natAbs)
      (Finset.mem_range.mpr (by omega))
  have hjumpCast : |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| ≤
      (((Finset.range (⌊(n : ℝ) * ((T : ℝ) + 1)⌋₊ + 1)).sup
        (fun j => ((forestHeight ω (j + 1) : ℤ) - forestHeight ω j).natAbs) : ℕ) : ℝ) := by
    calc
      |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| =
          (((((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs : ℕ) : ℝ)) := by
        simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast]
      _ ≤ _ := by exact_mod_cast hjumpNat
  have hjump : B n / n * |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| ≤
      maxHeightJump B n ((T : ℝ) + 1) ω := by
    unfold maxHeightJump
    exact mul_le_mul_of_nonneg_left hjumpCast ha
  have hscaledH : B n / n * |(forestHeight ω k : ℝ) - forestHeightLin ω u| ≤
      heightOscillation B n ((T : ℝ) + 1) (w / n) ω := by
    calc
      B n / n * |(forestHeight ω k : ℝ) - forestHeightLin ω u| =
          |B n / n * (forestHeight ω k : ℝ) - B n / n * forestHeightLin ω u| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg ha]
      _ ≤ _ := hosc
  have htri : |forestContourLin ω (2 * u) - forestHeightLin ω u| ≤
      (|(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| + 1) +
        |(forestHeight ω k : ℝ) - forestHeightLin ω u| := by
    calc
      |forestContourLin ω (2 * u) - forestHeightLin ω u| ≤
          |forestContourLin ω (2 * u) - forestHeight ω k| +
            |(forestHeight ω k : ℝ) - forestHeightLin ω u| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hC le_rfl
  have hmul := mul_le_mul_of_nonneg_left htri ha
  have hfinal : |B n / n * forestContourLin ω (2 * u) - B n / n * forestHeightLin ω u| ≤
      heightOscillation B n ((T : ℝ) + 1) (w / n) ω + maxHeightJump B n ((T : ℝ) + 1) ω +
        B n / n := by
    rw [← mul_sub, abs_mul, abs_of_nonneg ha]
    nlinarith
  simpa only [u, mul_assoc] using hfinal

private theorem forestContourHeightError_nonneg (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (ω : ℕ → ℕ) : 0 ≤ forestContourHeightError B n T ω := by
  exact Real.iSup_nonneg fun _ => abs_nonneg _

/-- **Contour/height comparison** (blueprint K12) on every positive horizon:
`sup_{t ≤ T} |(B_n/n) C(2nt) - (B_n/n) H_lin(nt)| → 0` in probability. -/
theorem contour_height_error_tendstoInMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure (offspringSeqLaw μ : Measure (ℕ → ℕ))
      (fun n ω => forestContourHeightError B n T ω) atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro η hη
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro b hb
    obtain ⟨M, hM⟩ := forestHeight_sup_tight h (T := 2 * (T : ℝ)) (by positivity)
      (show 0 < b / 4 by positivity)
    let A (n : ℕ) : Set (ℕ → ℕ) := {ω | M < B n / n *
      (((Finset.range (⌊(n : ℝ) * (2 * (T : ℝ))⌋₊ + 1)).sup
        (fun k => forestHeight ω k) : ℕ) : ℝ)}
    let O (δ : ℝ) (n : ℕ) : Set (ℕ → ℕ) :=
      {ω | η / 4 < heightOscillation B n ((T : ℝ) + 1) δ ω}
    let J (n : ℕ) : Set (ℕ → ℕ) :=
      {ω | η / 4 ≤ ‖maxHeightJump B n ((T : ℝ) + 1) ω - 0‖}
    let E (n : ℕ) : Set (ℕ → ℕ) :=
      {ω | η ≤ ‖forestContourHeightError B n T ω - 0‖}
    have hprob (S : ℕ → Set (ℕ → ℕ)) : IsBoundedUnder (· ≤ ·) atTop
        (fun n => (offspringSeqLaw μ).toMeasure.real (S n)) :=
      isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩
    have hAevent : ∀ᶠ n : ℕ in atTop,
        (offspringSeqLaw μ).toMeasure.real (A n) < b / 2 := by
      exact eventually_lt_of_limsup_lt (hM.trans_lt (by linarith)) (hprob A)
    have hmod := forestHeight_modulus h (T := (T : ℝ) + 1) (by positivity)
      (η := η / 4) (by positivity)
    have hmodSmall := hmod.eventually (gt_mem_nhds (show 0 < b / 4 by positivity))
    obtain ⟨δ, hδlim, hδ⟩ := (hmodSmall.and self_mem_nhdsWithin).exists
    let w (n : ℕ) : ℝ := max 1 ((n : ℝ) * M / (2 * B n))
    have hden : Tendsto (fun n => 2 * B n) atTop atTop :=
      (Survival.tendsto_B_atTop h).const_mul_atTop (by norm_num)
    have hterm : Tendsto (fun n => M / (2 * B n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hterm' : Tendsto (fun n : ℕ => ((n : ℝ) * M / (2 * B n)) / n) atTop (𝓝 0) := by
      apply hterm.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hB := h.pos n hn
      field_simp [hnR.ne', hB.ne']
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hw : Tendsto (fun n => w n / n) atTop (𝓝 0) := by
      have hm : Tendsto (fun n : ℕ => max ((1 : ℝ) / n) (((n : ℝ) * M / (2 * B n)) / n))
          atTop (𝓝 (max 0 0)) := hinv.max hterm'
      rw [max_self] at hm
      apply hm.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact max_div_div_right (Nat.cast_nonneg n) (1 : ℝ) ((n : ℝ) * M / (2 * B n))
    have hwδ : ∀ᶠ n : ℕ in atTop, w n / n < δ :=
      hw.eventually (gt_mem_nhds hδ)
    have hOevent : ∀ᶠ n : ℕ in atTop,
        (offspringSeqLaw μ).toMeasure.real (O (w n / n) n) < b / 4 := by
      have hOfixed : ∀ᶠ n : ℕ in atTop,
          (offspringSeqLaw μ).toMeasure.real (O δ n) < b / 4 :=
        eventually_lt_of_limsup_lt hδlim (hprob (O δ))
      filter_upwards [hOfixed, hwδ] with n hn hnδ
      apply (measureReal_mono ?_ (measure_ne_top _ _)).trans_lt hn
      intro ω hω
      exact hω.trans_le (heightOscillation_mono B n (by positivity) hδ.le hnδ.le ω)
    have hJevent : ∀ᶠ n : ℕ in atTop,
        (offspringSeqLaw μ).toMeasure.real (J n) < b / 4 := by
      have hj := (tendstoInMeasure_iff_measureReal_norm.mp
        (maxHeightJump_tendstoInMeasure h (T := (T : ℝ) + 1) (by positivity)))
        (η / 4) (by positivity)
      exact hj.eventually (gt_mem_nhds (show 0 < b / 4 by positivity))
    have hscale : ∀ᶠ n : ℕ in atTop, B n / n < η / 4 :=
      (Survival.tendsto_B_div_n h).eventually (gt_mem_nhds (show 0 < η / 4 by positivity))
    have hBbig : ∀ᶠ n : ℕ in atTop, 2 * |M| < B n :=
      (Survival.tendsto_B_atTop h).eventually_gt_atTop (2 * |M|)
    filter_upwards [hAevent, hOevent, hJevent, hscale, hBbig,
      eventually_ge_atTop 2] with n hnA hnO hnJ hnscale hnB hn2
    have hn1 : 1 ≤ n := by omega
    have hB : 0 < B n := h.pos n hn1
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hMB : M < B n := by
      have hle := le_abs_self M
      have hnonneg := abs_nonneg M
      linarith
    have hratio : (n : ℝ) * M / (2 * B n) ≤ (n : ℝ) / 2 := by
      have hmul : (n : ℝ) * M < (n : ℝ) * B n := mul_lt_mul_of_pos_left hMB hnR
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * B n)).2
      nlinarith
    have hwn : w n + 1 ≤ (n : ℝ) := by
      dsimp [w]
      rcases le_total (1 : ℝ) ((n : ℝ) * M / (2 * B n)) with hr | hr
      · rw [max_eq_right hr]
        nlinarith
      · rw [max_eq_left hr]
        exact_mod_cast hn2
    have hsub : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
        ω ∈ E n → ω ∈ A n ∪ (O (w n / n) n ∪ J n) := by
      filter_upwards [ae_ladderFinite μ h.critical h.nondegenerate] with ω hω
      intro hE
      by_cases ha : ω ∈ A n
      · exact Or.inl ha
      by_cases ho : ω ∈ O (w n / n) n
      · exact Or.inr (Or.inl ho)
      by_cases hj : ω ∈ J n
      · exact Or.inr (Or.inr hj)
      exfalso
      have hw_height : ∀ j : ℕ, (j : ℝ) ≤ 2 * n * T →
          (forestHeight ω j : ℝ) / 2 ≤ w n := by
        intro j hj
        have hmax : B n / n * (((Finset.range (⌊(n : ℝ) * (2 * (T : ℝ))⌋₊ + 1)).sup
            (fun k => forestHeight ω k) : ℕ) : ℝ) ≤ M := le_of_not_gt ha
        have hjFloor : j ≤ ⌊(n : ℝ) * (2 * (T : ℝ))⌋₊ := Nat.le_floor (by nlinarith)
        have hjMem : j ∈ Finset.range (⌊(n : ℝ) * (2 * (T : ℝ))⌋₊ + 1) :=
          Finset.mem_range.mpr (by omega)
        have hjSup : forestHeight ω j ≤ (Finset.range
            (⌊(n : ℝ) * (2 * (T : ℝ))⌋₊ + 1)).sup (fun k => forestHeight ω k) :=
          Finset.le_sup (f := fun k => forestHeight ω k) hjMem
        have hjSupR : (forestHeight ω j : ℝ) ≤ (((Finset.range
            (⌊(n : ℝ) * (2 * (T : ℝ))⌋₊ + 1)).sup
            (fun k => forestHeight ω k) : ℕ) : ℝ) := by exact_mod_cast hjSup
        have hjM : (B n * (forestHeight ω j : ℝ)) / n ≤ M := by
          have hh := (mul_le_mul_of_nonneg_left hjSupR (div_nonneg hB.le hnR.le)).trans hmax
          convert hh using 1
          ring
        have hjM' := (div_le_iff₀ hnR).mp hjM
        apply le_max_of_le_right
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
          (by positivity : (0 : ℝ) < 2 * B n)).2
        nlinarith
      have he := forestContourHeightError_le hω B hB.le T (le_max_left _ _) hwn hw_height
      have ho' : heightOscillation B n ((T : ℝ) + 1) (w n / n) ω ≤ η / 4 :=
        le_of_not_gt ho
      have hjnonneg : 0 ≤ maxHeightJump B n ((T : ℝ) + 1) ω := by
        unfold maxHeightJump
        positivity
      have hj' : maxHeightJump B n ((T : ℝ) + 1) ω ≤ η / 4 := by
        have hlt : ‖maxHeightJump B n ((T : ℝ) + 1) ω - 0‖ < η / 4 := lt_of_not_ge hj
        simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hjnonneg] using hlt.le
      have he0 : 0 ≤ forestContourHeightError B n T ω := forestContourHeightError_nonneg B n T ω
      change η ≤ ‖forestContourHeightError B n T ω - 0‖ at hE
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg he0] at hE
      linarith
    calc
      (offspringSeqLaw μ).toMeasure.real (E n) ≤
          (offspringSeqLaw μ).toMeasure.real (A n ∪ (O (w n / n) n ∪ J n)) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
      _ ≤ (offspringSeqLaw μ).toMeasure.real (A n) +
          (offspringSeqLaw μ).toMeasure.real (O (w n / n) n ∪ J n) := measureReal_union_le _ _
      _ ≤ (offspringSeqLaw μ).toMeasure.real (A n) +
          ((offspringSeqLaw μ).toMeasure.real (O (w n / n) n) +
            (offspringSeqLaw μ).toMeasure.real (J n)) :=
        add_le_add le_rfl (measureReal_union_le _ _)
      _ < b := by linarith

end BGW.StableTrees.ForestContour
