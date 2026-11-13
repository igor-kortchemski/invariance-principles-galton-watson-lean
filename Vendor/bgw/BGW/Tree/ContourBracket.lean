/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Height
public import BGW.Tree.ContourVertices
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic

import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Max

/-!
# Finite-tree contour bracketing by DFS heights

This module compares the discrete contour of a finite plane tree with its
depth-first height sequence, using the exact first-visit times.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- DFS heights extended by `0`: `|v_i|` for `i < size`, and `0` for `i ≥ size`. -/
def heightSeq (t : PlaneTree) (i : ℕ) : ℕ := ((t.vertices[i]?).map List.length).getD 0

/-- The contour at integer time `m` (original speed), `0` after the end of the contour. -/
def contourAt (t : PlaneTree) (m : ℕ) : ℕ := t.contour.getD m 0

/-- Linear interpolation of the heights at integer times (used for `u ≥ 0`). -/
noncomputable def heightLin (t : PlaneTree) (u : ℝ) : ℝ :=
  (1 - (u - ⌊u⌋₊)) * (t.heightSeq ⌊u⌋₊ : ℝ) + (u - ⌊u⌋₊) * (t.heightSeq (⌊u⌋₊ + 1) : ℝ)

/-- Linear interpolation of the contour at integer times (used for `s ≥ 0`). -/
noncomputable def contourLin (t : PlaneTree) (s : ℝ) : ℝ :=
  (1 - (s - ⌊s⌋₊)) * (t.contourAt ⌊s⌋₊ : ℝ) + (s - ⌊s⌋₊) * (t.contourAt (⌊s⌋₊ + 1) : ℝ)

/-! ### Heights -/

/-- On an existing DFS index, the extended height sequence is the vertex depth. -/
theorem heightSeq_of_lt (t : PlaneTree) {i : ℕ} (hi : i < t.size) :
    t.heightSeq i = t.height ⟨i, hi⟩ := by
  have hi' : i < t.vertices.length := by simpa only [length_vertices] using hi
  simp [heightSeq, height, List.getElem?_eq_getElem hi']

/-- At and beyond the size, the extended height sequence is zero. -/
theorem heightSeq_of_le (t : PlaneTree) {i : ℕ} (hi : t.size ≤ i) :
    t.heightSeq i = 0 := by
  have hi' : t.vertices.length ≤ i := by simpa only [length_vertices] using hi
  simp [heightSeq, List.getElem?_eq_none hi']

/-- A vertex is deeper than its DFS index at most. -/
theorem heightSeq_le (t : PlaneTree) (i : ℕ) : t.heightSeq i ≤ i := by
  by_cases hi : i < t.size
  · rw [heightSeq_of_lt t hi]
    have h := t.height_eq_card_recordMin ⟨i, hi⟩
    calc
      t.height ⟨i, hi⟩ =
          ((Finset.range i).filter
            (fun j => ∀ k, j ≤ k → k ≤ i → t.lukasiewicz j ≤ t.lukasiewicz k)).card := h
      _ ≤ (Finset.range i).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = i := Finset.card_range _
  · rw [heightSeq_of_le t (Nat.le_of_not_gt hi)]
    exact Nat.zero_le _

/-- Heights increase by at most one along the DFS order. -/
theorem heightSeq_succ_le (t : PlaneTree) (i : ℕ) :
    t.heightSeq (i + 1) ≤ t.heightSeq i + 1 := by
  by_cases hi : i < t.size
  · by_cases his : i + 1 < t.size
    · rw [heightSeq_of_lt t hi, heightSeq_of_lt t his]
      let S : Finset ℕ := (Finset.range i).filter
        (fun j => ∀ k, j ≤ k → k ≤ i → t.lukasiewicz j ≤ t.lukasiewicz k)
      let T : Finset ℕ := (Finset.range (i + 1)).filter
        (fun j => ∀ k, j ≤ k → k ≤ i + 1 → t.lukasiewicz j ≤ t.lukasiewicz k)
      have hS : S.card = (t.height ⟨i, hi⟩) := by
        simpa only [S] using (t.height_eq_card_recordMin ⟨i, hi⟩).symm
      have hT : T.card = (t.height ⟨i + 1, his⟩) := by
        simpa only [T] using (t.height_eq_card_recordMin ⟨i + 1, his⟩).symm
      have hsub : T ⊆ insert i S := by
        intro j hj
        rw [Finset.mem_insert]
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          have hjT := (Finset.mem_filter.mp hj)
          have hjrange : j < i := by
            have := Finset.mem_range.mp hjT.1
            omega
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr hjrange, ?_⟩
          intro k hjk hki
          exact hjT.2 k hjk (by omega)
      have hcard : T.card ≤ (insert i S).card := Finset.card_le_card hsub
      have hnot : i ∉ S := by simp [S]
      rw [Finset.card_insert_of_notMem hnot] at hcard
      omega
    · rw [heightSeq_of_le t (by omega)]
      have h := heightSeq_le t i
      omega
  · rw [heightSeq_of_le t (Nat.le_of_not_gt hi), heightSeq_of_le t (by omega)]
    omega

/-- At a natural time, linear interpolation recovers the DFS height. -/
theorem heightLin_natCast (t : PlaneTree) (i : ℕ) : t.heightLin i = t.heightSeq i := by
  simp [heightLin]

/-- At an integer time, linear interpolation recovers the contour value. -/
theorem contourLin_natCast (t : PlaneTree) (m : ℕ) : t.contourLin m = t.contourAt m := by
  simp [contourLin]

/-! ### Contour values -/

/-- Beyond the contour's final listed time, the totalized contour is zero. -/
theorem contourAt_of_lt (t : PlaneTree) {m : ℕ} (hm : 2 * (t.size - 1) < m) :
    t.contourAt m = 0 := by
  have hp := size_pos t
  have hlen := length_contour t
  have hmi : t.contour.length ≤ m := by rw [hlen]; omega
  exact List.getD_eq_default _ _ hmi

/-- First visit of the DFS vertex `i` at time `2i - H_i`. -/
theorem contourAt_firstVisit (t : PlaneTree) {i : ℕ} (hi : i < t.size) :
    t.contourAt (2 * i - t.heightSeq i) = t.heightSeq i := by
  have hiv : i < t.vertices.length := by simpa only [length_vertices] using hi
  let u := t.vertices[i]'hiv
  have hget : t.vertices[i]? = some u := List.getElem?_eq_getElem hiv
  have hfirst := getElem?_contour_first_visit hget
  have hheight : t.heightSeq i = u.length := by
    rw [heightSeq_of_lt t hi]
    rfl
  simp [contourAt, hheight, List.getD_eq_getElem?_getD, hfirst]

/-- Every contour value is at most the depth of some vertex (a depth, before the end). -/
theorem exists_contourAt_le_heightSeq (t : PlaneTree) (m : ℕ) :
    ∃ i < t.size, t.contourAt m ≤ t.heightSeq i := by
  by_cases hm : m < t.contour.length
  · let c := t.contour[m]'hm
    have hmem : c ∈ t.contour := List.mem_of_getElem? (List.getElem?_eq_getElem hm)
    obtain ⟨u, hu, hlen⟩ := (mem_contour_iff t c).mp hmem
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ((mem_vertices_iff t u).mpr hu)
    have hip : i < t.size := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simpa only [length_vertices] using this
    have hheight : t.heightSeq i = u.length := by
      rw [heightSeq_of_lt t hip]
      unfold height
      have hidx : t.vertices[i]'(by simpa only [length_vertices] using hip) = u :=
        (List.getElem?_eq_some_iff.mp hi).2
      rw [hidx, hlen]
    refine ⟨i, hip, ?_⟩
    have hval : t.contourAt m = u.length := by
      change t.contour.getD m 0 = u.length
      rw [List.getD_eq_getElem _ _ hm]
      change c = u.length
      exact hlen.symm
    rw [hval, hheight]
  · refine ⟨0, size_pos t, ?_⟩
    rw [contourAt]
    have hz : t.contour.getD m 0 = 0 := by
      apply List.getD_eq_default _ _
      exact Nat.le_of_not_gt hm
    rw [hz]
    simp [heightSeq]

/-- Before the end, every contour value is the depth of some vertex. -/
theorem exists_contourAt_eq_heightSeq (t : PlaneTree) {m : ℕ} (hm : m < 2 * t.size - 1) :
    ∃ i < t.size, t.contourAt m = t.heightSeq i := by
  have hlen : t.contour.length = 2 * t.size - 1 := by
    rw [length_contour]
    have hp := size_pos t
    omega
  have hmi : m < t.contour.length := by rw [hlen]; exact hm
  let c := t.contour[m]'hmi
  have hmem : c ∈ t.contour := List.mem_of_getElem? (List.getElem?_eq_getElem hmi)
  obtain ⟨u, hu, hdepth⟩ := (mem_contour_iff t c).mp hmem
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ((mem_vertices_iff t u).mpr hu)
  have hip : i < t.size := by
    simpa only [length_vertices] using (List.getElem?_eq_some_iff.mp hi).1
  have hheight : t.heightSeq i = u.length := by
    rw [heightSeq_of_lt t hip]
    unfold height
    have hidx : t.vertices[i]'(by simpa only [length_vertices] using hip) = u :=
      (List.getElem?_eq_some_iff.mp hi).2
    rw [hidx, hdepth]
  refine ⟨i, hip, ?_⟩
  have hval : t.contourAt m = u.length := by
    change t.contour.getD m 0 = u.length
    rw [List.getD_eq_getElem _ _ hmi]
    change c = u.length
    exact hdepth.symm
  rw [hval, hheight]

/-! ### Local bracketing -/

private theorem vertexContour_getElem?_firstVisit {t : PlaneTree} {i : ℕ} {u : List ℕ}
    (hi : t.vertices[i]? = some u) :
    t.vertexContour[2 * i - u.length]? = some u := by
  obtain ⟨hb, heq, _⟩ := List.idxOf?_eq_some_iff.mp
    (idxOf?_vertexContour_of_getElem?_vertices hi)
  exact List.getElem?_eq_some_iff.mpr ⟨hb, heq⟩

private theorem vertexContour_depth_eq_contourAt (t : PlaneTree) {m : ℕ}
    (hm : m < t.vertexContour.length) :
    t.contourAt m = (t.vertexContour[m]'hm).length := by
  have h := congrArg (fun xs : List ℕ => xs[m]?) (map_length_vertexContour t)
  have hget : t.contour[m]? = some (t.vertexContour[m]'hm).length := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hm, Option.map_some] using h.symm
  change t.contour.getD m 0 = (t.vertexContour[m]'hm).length
  simp [List.getD_eq_getElem?_getD, hget]

private theorem graphDist_le_add_of_isChain {xs : List (List ℕ)}
    (hchain : xs.IsChain (fun u v => graphDist u v = 1)) {a d : ℕ}
    (hbound : a + d < xs.length) :
    graphDist (xs.get ⟨a, by omega⟩) (xs.get ⟨a + d, by omega⟩) ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hleft : a + d < xs.length := by omega
    have hprev := ih hleft
    rw [List.isChain_iff_getElem] at hchain
    have hstep := hchain (a + d) (by omega)
    have hstep' : graphDist (xs.get ⟨a + d, by omega⟩)
        (xs.get ⟨a + d + 1, by omega⟩) = 1 := by
      simpa [Nat.add_assoc] using hstep
    have hstep'' : graphDist (xs.get ⟨a + d, by omega⟩)
        (xs.get ⟨a + (d + 1), by omega⟩) = 1 := by
      simpa [Nat.add_assoc] using hstep'
    calc
      graphDist (xs.get ⟨a, by omega⟩) (xs.get ⟨a + (d + 1), by omega⟩) ≤
          graphDist (xs.get ⟨a, by omega⟩) (xs.get ⟨a + d, by omega⟩) +
            graphDist (xs.get ⟨a + d, by omega⟩) (xs.get ⟨a + (d + 1), by omega⟩) :=
        graphDist_triangle _ _ _
      _ ≤ d + 1 := by
        rw [hstep'']
        exact Nat.add_le_add_right hprev 1

private theorem graphDist_le_vertexContour_gap {t : PlaneTree} {a b : ℕ} {u v : List ℕ}
    (ha : t.vertexContour[a]? = some u) (hb : t.vertexContour[b]? = some v)
    (hab : a ≤ b) : graphDist u v ≤ b - a := by
  obtain ⟨ha', hau⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hb', hvb⟩ := List.getElem?_eq_some_iff.mp hb
  have h := graphDist_le_add_of_isChain (isChain_vertexContour t)
    (a := a) (d := b - a) (by omega)
  simpa only [List.get_eq_getElem, Nat.add_sub_of_le hab, hau, hvb] using h

private theorem lca_height_on_geodesic {u v w : List ℕ}
    (hgeo : graphDist u w + graphDist w v = graphDist u v) :
    (lca u v).length ≤ w.length ∧ w.length ≤ max u.length v.length := by
  let a := lca u w
  let b := lca w v
  have hapre : a <+: w := lca_prefix_right u w
  have hbpre : b <+: w := lca_prefix_left w v
  have haLen : a.length ≤ w.length := hapre.length_le
  have hbLen : b.length ≤ w.length := hbpre.length_le
  have habsum : graphDist u w + 2 * a.length = u.length + w.length := by
    simpa only [a] using graphDist_add_two_lca u w
  have hbsum : graphDist w v + 2 * b.length = w.length + v.length := by
    simpa only [b] using graphDist_add_two_lca w v
  have hlsum : graphDist u v + 2 * (lca u v).length = u.length + v.length :=
    graphDist_add_two_lca u v
  have hlenEq : w.length + (lca u v).length = a.length + b.length := by omega
  rcases List.prefix_or_prefix_of_prefix hapre hbpre with hab | hba
  · have hav : a <+: v := hab.trans (lca_prefix_right w v)
    have hal : a <+: lca u v := (prefix_lca_iff _ _ _).mpr ⟨lca_prefix_left u w, hav⟩
    have hLleA : (lca u v).length ≤ a.length := by omega
    have hae : a.length = (lca u v).length := le_antisymm hal.length_le hLleA
    have haeq : a = lca u v := hal.eq_of_length hae
    have hLprefix : lca u v <+: w := by rw [← haeq]; exact hapre
    have hwlen : w.length = b.length := by omega
    refine ⟨hLprefix.length_le, ?_⟩
    rw [hwlen]
    exact (lca_prefix_right w v).length_le.trans (le_max_right _ _)
  · have hbu : b <+: u := hba.trans (lca_prefix_left u w)
    have hbl : b <+: lca u v := (prefix_lca_iff _ _ _).mpr ⟨hbu, lca_prefix_right w v⟩
    have hLleB : (lca u v).length ≤ b.length := by omega
    have hbe : b.length = (lca u v).length := le_antisymm hbl.length_le hLleB
    have hbeq : b = lca u v := hbl.eq_of_length hbe
    have hLprefix : lca u v <+: w := by rw [← hbeq]; exact hbpre
    have hwlen : w.length = a.length := by omega
    refine ⟨hLprefix.length_le, ?_⟩
    rw [hwlen]
    exact (lca_prefix_left u w).length_le.trans (le_max_left _ _)

/-- **Integer bracketing**: between the first visits of `v_i` and `v_{i+1}` (with `b_z = 2z`),
the contour stays within `|H_{i+1} - H_i| + 1` of `H_i`. -/
theorem contourAt_bracket (t : PlaneTree) {i m : ℕ} (hi : i < t.size)
    (hm1 : 2 * i - t.heightSeq i ≤ m) (hm2 : m ≤ 2 * (i + 1) - t.heightSeq (i + 1)) :
    |(t.contourAt m : ℤ) - t.heightSeq i| ≤ |(t.heightSeq (i + 1) : ℤ) - t.heightSeq i| + 1 := by
  let bi := 2 * i - t.heightSeq i
  have hiv : i < t.vertices.length := by simpa only [length_vertices] using hi
  let u := t.vertices[i]'hiv
  have hiGet : t.vertices[i]? = some u := List.getElem?_eq_getElem hiv
  have huHeight : u.length = t.heightSeq i := by
    rw [heightSeq_of_lt t hi]
    rfl
  have hbiAddr : t.vertexContour[bi]? = some u := by
    simpa [bi, huHeight] using vertexContour_getElem?_firstVisit hiGet
  obtain ⟨hbiLt, hbiEq⟩ := List.getElem?_eq_some_iff.mp hbiAddr
  by_cases hnext : i + 1 < t.size
  · let bj := 2 * (i + 1) - t.heightSeq (i + 1)
    have hjv : i + 1 < t.vertices.length := by simpa only [length_vertices] using hnext
    let v := t.vertices[i + 1]'hjv
    have hjGet : t.vertices[i + 1]? = some v := List.getElem?_eq_getElem hjv
    have hvHeight : v.length = t.heightSeq (i + 1) := by
      rw [heightSeq_of_lt t hnext]
      rfl
    have hbjAddr : t.vertexContour[bj]? = some v := by
      simpa [bj, hvHeight] using vertexContour_getElem?_firstVisit hjGet
    obtain ⟨hbjLt, hbjEq⟩ := List.getElem?_eq_some_iff.mp hbjAddr
    have hbm : bi ≤ bj := by
      dsimp [bi, bj]
      have hH := heightSeq_succ_le t i
      omega
    have hmLt : m < t.vertexContour.length := lt_of_le_of_lt hm2 hbjLt
    let w := t.vertexContour[m]'hmLt
    have hmAddr : t.vertexContour[m]? = some w := List.getElem?_eq_getElem hmLt
    have hseg1 : graphDist u w ≤ m - bi :=
      graphDist_le_vertexContour_gap hbiAddr hmAddr (by omega)
    have hseg2 : graphDist w v ≤ bj - m :=
      graphDist_le_vertexContour_gap hmAddr hbjAddr hm2
    have hdistLe : graphDist u v ≤ bj - bi := by
      have htri := graphDist_triangle u w v
      omega
    have hgap : bj - bi = 2 + t.heightSeq i - t.heightSeq (i + 1) := by
      dsimp [bi, bj]
      have hHi := heightSeq_le t i
      have hHj := heightSeq_le t (i + 1)
      omega
    have hdistFormula := graphDist_add_two_lca u v
    have hLupper : (lca u v).length ≤ t.heightSeq (i + 1) := by
      rw [← hvHeight]
      exact (lca_prefix_right u v).length_le
    have hLlower : t.heightSeq (i + 1) - 1 ≤ (lca u v).length := by
      rw [huHeight, hvHeight] at hdistFormula
      have hdistBound : graphDist u v ≤ 2 + t.heightSeq i - t.heightSeq (i + 1) := by
        rw [← hgap]
        exact hdistLe
      have hsucc := heightSeq_succ_le t i
      have hnextSmall : t.heightSeq (i + 1) ≤ 2 + t.heightSeq i := by omega
      have hformulaInt : (graphDist u v : ℤ) + 2 * (lca u v).length =
          t.heightSeq i + t.heightSeq (i + 1) := by exact_mod_cast hdistFormula
      have hboundInt : (graphDist u v : ℤ) ≤
          2 + (t.heightSeq i : ℤ) - t.heightSeq (i + 1) := by
        exact_mod_cast hdistBound
      have htargetInt : (t.heightSeq (i + 1) : ℤ) ≤ (lca u v).length + 1 := by
        linarith [hformulaInt, hboundInt]
      have htargetNat : t.heightSeq (i + 1) ≤ (lca u v).length + 1 := by exact_mod_cast htargetInt
      omega
    have hLlt : (lca u v).length < t.heightSeq (i + 1) := by
      by_contra hnot
      have hLe : t.heightSeq (i + 1) ≤ (lca u v).length := by omega
      have hEq : (lca u v).length = v.length := by omega
      have hL_eq_v : lca u v = v := (lca_prefix_right u v).eq_of_length hEq
      have hvPrefix : v <+: u := by simpa [hL_eq_v] using lca_prefix_left u v
      obtain ⟨subtree, hsubtree⟩ := (mem_vertices_iff t v).mp (List.mem_of_getElem? hjGet)
      have horder :=
        (isPrefix_iff_dfs_in_fringe hjGet hiGet hsubtree).mp hvPrefix
      omega
    have hLlen : (lca u v).length = t.heightSeq (i + 1) - 1 := by omega
    have hdistEq : graphDist u v = bj - bi := by
      rw [huHeight, hvHeight, hLlen] at hdistFormula
      omega
    have hgeo : graphDist u w + graphDist w v = graphDist u v := by
      have htri := graphDist_triangle u w v
      omega
    have hwBounds := lca_height_on_geodesic hgeo
    have hdepth := vertexContour_depth_eq_contourAt t hmLt
    rw [← hdepth] at hwBounds
    rw [huHeight, hvHeight, hLlen] at hwBounds
    have hC := hwBounds.2
    have hLow := hwBounds.1
    have hnextPos : 0 < t.heightSeq (i + 1) := by omega
    have hCIntLower : (t.heightSeq (i + 1) : ℤ) - 1 ≤ t.contourAt m := by
      have hcast : ((t.heightSeq (i + 1) - 1 : ℕ) : ℤ) ≤ (t.contourAt m : ℤ) := by
        exact_mod_cast hLow
      simpa [Nat.cast_sub (by omega : 1 ≤ t.heightSeq (i + 1))] using hcast
    by_cases horder : t.heightSeq i ≤ t.heightSeq (i + 1)
    · rw [max_eq_right horder] at hC
      have hupper : (t.contourAt m : ℤ) ≤ (t.heightSeq (i + 1) : ℤ) := by exact_mod_cast hC
      have hHi : (t.heightSeq i : ℤ) ≤ t.heightSeq (i + 1) := by exact_mod_cast horder
      have hdiff : 0 ≤ (t.heightSeq (i + 1) : ℤ) - t.heightSeq i := by omega
      rw [abs_of_nonneg hdiff]
      apply abs_le.mpr
      constructor <;> omega
    · have horder' : t.heightSeq (i + 1) ≤ t.heightSeq i := by omega
      rw [max_eq_left horder'] at hC
      have hupper : (t.contourAt m : ℤ) ≤ (t.heightSeq i : ℤ) := by exact_mod_cast hC
      have hdiff : 0 ≤ (t.heightSeq i : ℤ) - t.heightSeq (i + 1) := by
        have hle : (t.heightSeq (i + 1) : ℤ) ≤ t.heightSeq i := by exact_mod_cast horder'
        omega
      rw [abs_of_nonpos (by omega : (t.heightSeq (i + 1) : ℤ) - t.heightSeq i ≤ 0)]
      apply abs_le.mpr
      constructor <;> omega
  · have hterminal : i + 1 = t.size := by omega
    have hHnext : t.heightSeq (i + 1) = 0 := by
      rw [hterminal]
      exact heightSeq_of_le t le_rfl
    have hduration : 2 * (t.size - 1) = 2 * i := by omega
    by_cases hmEnd : 2 * (t.size - 1) < m
    · have hcontourZero := contourAt_of_lt t hmEnd
      rw [hHnext, hcontourZero]
      omega
    · have hmD : m ≤ 2 * (t.size - 1) := by omega
      have hDlt : 2 * (t.size - 1) < t.vertexContour.length := by
        rw [length_vertexContour]
        omega
      have hDGet : t.vertexContour[2 * (t.size - 1)]? = some [] := by
        have hlast := getLast?_vertexContour t
        have hne := vertexContour_ne_nil t
        have hlastGet := List.getLast?_eq_getLast_of_ne_nil hne
        have hlastVal : t.vertexContour.getLast hne = [] := by
          exact (Option.some.inj (hlast.symm.trans hlastGet)).symm
        have hidx : 2 * (t.size - 1) = t.vertexContour.length - 1 := by
          rw [length_vertexContour]
          omega
        rw [hidx, List.getElem?_eq_getElem (by omega), ← List.getLast_eq_getElem]
        simpa using congrArg some hlastVal
      have hmAddr : t.vertexContour[m]? = some (t.vertexContour[m]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      let w := t.vertexContour[m]'(by omega)
      have hseg1 : graphDist u w ≤ m - bi :=
        graphDist_le_vertexContour_gap hbiAddr hmAddr (by omega)
      have hseg2 : graphDist w [] ≤ 2 * (t.size - 1) - m :=
        graphDist_le_vertexContour_gap hmAddr hDGet hmD
      have hgeo : graphDist u w + graphDist w [] = graphDist u [] := by
        have htri := graphDist_triangle u w []
        have hroot : graphDist u [] = u.length := by
          rw [graphDist_comm, graphDist_root]
        rw [hroot] at htri ⊢
        have huLen : u.length = t.heightSeq i := huHeight
        have hbiDef : bi = 2 * i - t.heightSeq i := rfl
        have htime : 2 * (t.size - 1) - bi = t.heightSeq i := by
          rw [← hterminal]
          dsimp [bi]
          omega
        omega
      have hwBounds := lca_height_on_geodesic hgeo
      have hdepth := vertexContour_depth_eq_contourAt t (m := m) (by omega)
      simp only [lca_nil_right, List.length_nil, max_eq_left (Nat.zero_le _)] at hwBounds
      rw [← hdepth] at hwBounds
      have hcontourLe : t.contourAt m ≤ t.heightSeq i := by
        calc
          t.contourAt m ≤ u.length := hwBounds.2
          _ = t.heightSeq i := huHeight
      rw [hHnext]
      have hcontourNonneg : (0 : ℤ) ≤ (t.contourAt m : ℤ) := Nat.cast_nonneg _
      have hcontourHi : (t.contourAt m : ℤ) ≤ (t.heightSeq i : ℤ) := by exact_mod_cast hcontourLe
      have hHiNonneg : (0 : ℤ) ≤ (t.heightSeq i : ℤ) := Nat.cast_nonneg _
      have hleft : |(t.contourAt m : ℤ) - t.heightSeq i| =
          (t.heightSeq i : ℤ) - t.contourAt m := by
        rw [abs_of_nonpos (sub_nonpos.mpr hcontourHi)]
        ring
      have hright : |(0 : ℤ) - t.heightSeq i| = t.heightSeq i := by
        rw [abs_of_nonpos (by linarith [hHiNonneg])]
        norm_num
      calc
        |(t.contourAt m : ℤ) - t.heightSeq i| =
            (t.heightSeq i : ℤ) - t.contourAt m := hleft
        _ ≤ t.heightSeq i := by omega
        _ = |(0 : ℤ) - t.heightSeq i| := hright.symm
        _ ≤ |(0 : ℤ) - t.heightSeq i| + 1 := by omega

private theorem exists_integer_bracket_at (t : PlaneTree) {k : ℕ}
    (hk : k < 2 * t.size) :
    ∃ i < t.size, 2 * i - t.heightSeq i ≤ k ∧
      k + 1 ≤ 2 * (i + 1) - t.heightSeq (i + 1) := by
  classical
  let b := fun i => 2 * i - t.heightSeq i
  let S := (Finset.range t.size).filter (fun i => b i ≤ k)
  have hsize := size_pos t
  have hzero : t.heightSeq 0 = 0 := by have := heightSeq_le t 0; omega
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S, b, hsize, hzero]
  let i := S.max' hS
  have hiS : i < t.size ∧ b i ≤ k := by
    simpa [i, S, Finset.mem_filter, Finset.mem_range] using Finset.max'_mem S hS
  have hnext : k < b (i + 1) := by
    by_contra hnot
    have hbn : b (i + 1) ≤ k := by omega
    by_cases hnextLt : i + 1 < t.size
    · have hmem : i + 1 ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr hnextLt, hbn⟩
      have hmax : i + 1 ≤ i := by
        simpa [i] using (Finset.le_max' (s := S) (i + 1) hmem)
      omega
    · have hnextEq : i + 1 = t.size := by omega
      have hzeroNext : t.heightSeq (i + 1) = 0 := by
        rw [hnextEq]
        exact heightSeq_of_le t le_rfl
      dsimp [b] at hbn
      rw [hnextEq] at hbn
      have hzeroSize : t.heightSeq t.size = 0 := heightSeq_of_le t le_rfl
      rw [hzeroSize] at hbn
      omega
  refine ⟨i, hiS.1, hiS.2, ?_⟩
  have hle := Nat.succ_le_of_lt hnext
  simpa [b] using hle

/-- **Real-time bracketing**: every contour time `s ∈ [0, 2z]` lies in a bracket `i` with
`s/2 - 1 ≤ i ≤ s/2 + H_i/2`, and the interpolated contour at `s` is within
`|H_{i+1} - H_i| + 1` of `H_i`. -/
theorem contourLin_bracket (t : PlaneTree) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 * t.size) :
    ∃ i < t.size, s / 2 - 1 ≤ i ∧ (i : ℝ) ≤ s / 2 + (t.heightSeq i : ℝ) / 2 ∧
      |t.contourLin s - t.heightSeq i| ≤ |(t.heightSeq (i + 1) : ℝ) - t.heightSeq i| + 1 := by
  let zR : ℝ := t.size
  have hsBound : s ≤ (2 : ℝ) * zR := by simpa [zR] using hs
  by_cases hsEnd : s = (2 : ℝ) * zR
  · let i := t.size - 1
    have hi : i < t.size := by
      have hp := size_pos t
      dsimp [i]
      omega
    have hnextZero : t.heightSeq (i + 1) = 0 := by
      have hiEq : i + 1 = t.size := by dsimp [i]; omega
      rw [hiEq]
      exact heightSeq_of_le t le_rfl
    have hbiLe : 2 * i - t.heightSeq i ≤ 2 * t.size :=
      (Nat.sub_le _ _).trans (Nat.mul_le_mul_left 2 hi.le)
    have hInt := contourAt_bracket t hi hbiLe (by
      rw [hnextZero]
      dsimp [i]
      omega)
    have hreal : |(t.contourAt (2 * t.size) : ℝ) - t.heightSeq i| ≤
        |(t.heightSeq (i + 1) : ℝ) - t.heightSeq i| + 1 := by
      exact_mod_cast hInt
    have htime : t.contourLin ((2 : ℝ) * zR) = (t.contourAt (2 * t.size) : ℝ) := by
      have h := contourLin_natCast t (2 * t.size)
      have hz : (2 : ℝ) * zR = (2 * t.size : ℝ) := by
        norm_num [zR, Nat.cast_mul]
      rw [hz]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · rw [hsEnd]
      dsimp [i, zR]
      have hsub : ((t.size - 1 : ℕ) : ℝ) = (t.size : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hsub]
      norm_num
    · rw [hsEnd]
      dsimp [i, zR]
      have hsub : ((t.size - 1 : ℕ) : ℝ) = (t.size : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hsub]
      have hH : 0 ≤ (t.heightSeq (t.size - 1) : ℝ) := Nat.cast_nonneg _
      nlinarith
    · rw [hsEnd, htime]
      exact hreal
  · have hslt : s < (2 : ℝ) * zR := by
      rcases lt_or_eq_of_le hsBound with h | h
      · exact_mod_cast h
      · exact (hsEnd h).elim
    let k := ⌊s⌋₊
    have hkLo : (k : ℝ) ≤ s := Nat.floor_le hs0
    have hkHi : s < (k : ℝ) + 1 := Nat.lt_floor_add_one s
    have hkLtReal : (k : ℝ) < 2 * (t.size : ℝ) := by
      simpa [zR] using lt_of_le_of_lt hkLo hslt
    have hk : k < 2 * t.size := by exact_mod_cast hkLtReal
    obtain ⟨i, hi, hbi, hbk⟩ := exists_integer_bracket_at t hk
    let H := t.heightSeq i
    let Hnext := t.heightSeq (i + 1)
    let θ := s - (k : ℝ)
    have hθ0 : 0 ≤ θ := by dsimp [θ]; linarith
    have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
    have hC0 := contourAt_bracket t (i := i) (m := k) hi hbi (by omega)
    have hC1 := contourAt_bracket t (i := i) (m := k + 1) hi (by omega) (by omega)
    have hC0Real : |(t.contourAt k : ℝ) - H| ≤ |(Hnext : ℝ) - H| + 1 := by
      exact_mod_cast hC0
    have hC1Real : |(t.contourAt (k + 1) : ℝ) - H| ≤ |(Hnext : ℝ) - H| + 1 := by
      exact_mod_cast hC1
    have htime : (i : ℝ) ≤ s / 2 + H / 2 := by
      have hcast : ((2 * i - H : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hbi
      have hheightLe : H ≤ i := by dsimp [H]; exact heightSeq_le t i
      have hsub : H ≤ 2 * i := by omega
      rw [Nat.cast_sub hsub] at hcast
      have hcast' : 2 * (i : ℝ) - (H : ℝ) ≤ (k : ℝ) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcast
      change (i : ℝ) ≤ s / 2 + H / 2
      nlinarith [hkLo, hcast']
    have htimeLower : s / 2 - 1 ≤ i := by
      have hki : k + 1 ≤ 2 * (i + 1) := by
        exact le_trans hbk (Nat.sub_le _ _)
      have hkiReal : (k : ℝ) + 1 ≤ 2 * ((i : ℝ) + 1) := by exact_mod_cast hki
      nlinarith [hkHi]
    have hlin : t.contourLin s =
        (1 - θ) * (t.contourAt k : ℝ) + θ * (t.contourAt (k + 1) : ℝ) := by
      simp [contourLin, k, θ]
    have hcombo : t.contourLin s - H =
        (1 - θ) * ((t.contourAt k : ℝ) - H) + θ * ((t.contourAt (k + 1) : ℝ) - H) := by
      rw [hlin]
      ring
    have hcoef0 : 0 ≤ 1 - θ := by linarith
    have hE : 0 ≤ |(Hnext : ℝ) - H| + 1 := by positivity
    have h0lo := (abs_le.mp hC0Real).1
    have h0hi := (abs_le.mp hC0Real).2
    have h1lo := (abs_le.mp hC1Real).1
    have h1hi := (abs_le.mp hC1Real).2
    have h0lo' : -(1 - θ) * (|(Hnext : ℝ) - H| + 1) ≤
        (1 - θ) * ((t.contourAt k : ℝ) - H) := by
      have hmul := mul_le_mul_of_nonneg_left h0lo hcoef0
      nlinarith
    have h0hi' : (1 - θ) * ((t.contourAt k : ℝ) - H) ≤
        (1 - θ) * (|(Hnext : ℝ) - H| + 1) := by
      exact mul_le_mul_of_nonneg_left h0hi hcoef0
    have h1lo' : -θ * (|(Hnext : ℝ) - H| + 1) ≤
        θ * ((t.contourAt (k + 1) : ℝ) - H) := by
        have hmul := mul_le_mul_of_nonneg_left h1lo hθ0
        nlinarith
    have h1hi' : θ * ((t.contourAt (k + 1) : ℝ) - H) ≤
        θ * (|(Hnext : ℝ) - H| + 1) := by
      exact mul_le_mul_of_nonneg_left h1hi hθ0
    have hdev : |t.contourLin s - H| ≤ |(Hnext : ℝ) - H| + 1 := by
      rw [abs_le, hcombo]
      constructor <;> nlinarith [h0lo', h0hi', h1lo', h1hi']
    refine ⟨i, hi, htimeLower, htime, ?_⟩
    simpa [H, Hnext] using hdev
/-- **Prefix-local comparison** of the contour at time `2u` with the interpolated height at
`u`: if `ω ≥ 1` bounds half the heights of the vertices of index `≤ 2u`, and `δ` bounds the
oscillation of `heightLin` over windows of width `ω` inside `[0, z]`, then the two differ by at
most `2δ + 1`.  Only indices `≤ 2u` are used (K16 applies it on a larger prefix `a' < 1`). -/
theorem contourLin_two_mul_sub_heightLin_le (t : PlaneTree) {u ω δ : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ t.size) (hω1 : 1 ≤ ω)
    (hω2 : ∀ j : ℕ, j < t.size → (j : ℝ) ≤ 2 * u → (t.heightSeq j : ℝ) / 2 ≤ ω)
    (hδ : ∀ x y : ℝ, 0 ≤ x → x ≤ t.size → 0 ≤ y → y ≤ t.size → |x - y| ≤ ω →
      |t.heightLin x - t.heightLin y| ≤ δ) :
    |t.contourLin (2 * u) - t.heightLin u| ≤ 2 * δ + 1 := by
  obtain ⟨i, hi, hlo, hhi, hC⟩ :=
    contourLin_bracket t (s := 2 * u) (by positivity) (by nlinarith [hu])
  let H := t.heightSeq i
  let Hnext := t.heightSeq (i + 1)
  have hi0 : 0 ≤ (i : ℝ) := by positivity
  have hiLe : (i : ℝ) ≤ t.size := by exact_mod_cast hi.le
  have hiSuccLe : (i + 1 : ℝ) ≤ t.size := by exact_mod_cast (Nat.succ_le_of_lt hi)
  have hHle : (H : ℝ) ≤ i := by
    dsimp [H]
    exact_mod_cast heightSeq_le t i
  have hiLe2u : (i : ℝ) ≤ 2 * u := by
    dsimp [H] at hHle
    nlinarith [hhi, hHle]
  have hHhalf : (H : ℝ) / 2 ≤ ω := hω2 i hi hiLe2u
  have hdist : |u - (i : ℝ)| ≤ ω := by
    apply abs_le.mpr
    constructor
    · have hleft : u - (i : ℝ) ≤ 1 := by linarith [hlo]
      linarith [hω1]
    · linarith [hhi, hHhalf]
  have hδui := hδ u i hu0 hu hi0 hiLe hdist
  have hunit : |(i : ℝ) - (i + 1 : ℝ)| ≤ ω := by
    rw [abs_of_nonpos (by linarith)]
    norm_num
    exact hω1
  have hδjump := hδ (i : ℝ) (i + 1) hi0 hiLe (by positivity) hiSuccLe hunit
  have hHinterp : t.heightLin (i : ℝ) = H := by
    simpa [H] using t.heightLin_natCast i
  have hHnextInterp : t.heightLin (i + 1) = Hnext := by
    simpa [Hnext] using t.heightLin_natCast (i + 1)
  have hheightOsc : |(H : ℝ) - t.heightLin u| ≤ δ := by
    calc
      |(H : ℝ) - t.heightLin u| = |t.heightLin (i : ℝ) - t.heightLin u| := by
        rw [← hHinterp]
      _ = |t.heightLin u - t.heightLin (i : ℝ)| := abs_sub_comm _ _
      _ ≤ δ := hδui
  have hheightJump : |(Hnext : ℝ) - H| ≤ δ := by
    calc
      |(Hnext : ℝ) - H| = |t.heightLin (i + 1) - t.heightLin (i : ℝ)| := by
        rw [← hHnextInterp, ← hHinterp]
      _ = |t.heightLin (i : ℝ) - t.heightLin (i + 1)| := abs_sub_comm _ _
      _ ≤ δ := hδjump
  have hcontourBound : |t.contourLin (2 * u) - H| ≤ |(Hnext : ℝ) - H| + 1 := by
    simpa [H, Hnext] using hC
  calc
    |t.contourLin (2 * u) - t.heightLin u| ≤
        |t.contourLin (2 * u) - H| + |(H : ℝ) - t.heightLin u| := by
      calc
        |t.contourLin (2 * u) - t.heightLin u| =
            |(t.contourLin (2 * u) - H) + (H - t.heightLin u)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    _ ≤ (|(Hnext : ℝ) - H| + 1) + δ := add_le_add hcontourBound hheightOsc
    _ ≤ 2 * δ + 1 := by linarith [hheightJump]

end BGW.PlaneTree
