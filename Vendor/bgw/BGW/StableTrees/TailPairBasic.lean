/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTail
public import BGW.StableTrees.JointExcursion
public import BGW.StableTrees.ForestContour

/-!
# Tail-conditioned tree pair paths and extraction estimates

The walk retains its terminal step. The continuous height is interpolated and stopped at
zero at the tree size. Both coordinates always use the same tree and the sample-size clock.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

private theorem interpolation_cell (a : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (n : ℝ) (n + 1)) :
    (fun t : ℝ => (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1)) t =
      (1 - (t - n)) * (a n) + (t - n) * (a (n + 1)) := by
  by_cases he : t = n + 1
  · subst t
    have hf : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    simp [hf]
  · have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) ht.1)).2
      ⟨ht.1, lt_of_le_of_ne ht.2 he⟩
    simp only [hf]

private theorem continuousOn_interpolation_cell (a : ℕ → ℝ) (n : ℕ) :
    ContinuousOn (fun t : ℝ =>
      (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1))
      (Icc (n : ℝ) (n + 1)) := by
  apply ContinuousOn.congr (f := fun t : ℝ =>
    (1 - (t - n)) * (a n) + (t - n) * (a (n + 1)))
      (by fun_prop)
  intro t ht
  exact interpolation_cell a n ht

private theorem continuousOn_interpolation_Iic (a : ℕ → ℝ) (n : ℕ) :
    ContinuousOn (fun t : ℝ =>
      (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1)) (Iic (n : ℝ)) := by
  induction n with
  | zero =>
    apply ContinuousOn.congr (f := fun t : ℝ =>
      (1 - t) * (a 0) + t * (a 1)) (by fun_prop)
    intro t ht
    have ht0 : t ≤ 0 := by simpa using ht
    have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [hf]
  | succ n ih =>
    have hu : Iic (n : ℝ) ∪ Icc (n : ℝ) (n + 1) = Iic ((n + 1 : ℕ) : ℝ) := by
      ext t
      simp only [mem_union, mem_Iic, mem_Icc, Nat.cast_add, Nat.cast_one]
      constructor
      · rintro (h | h) <;> linarith [h]
      · intro h
        rcases le_total t (n : ℝ) with hn | hn
        · exact Or.inl hn
        · exact Or.inr ⟨hn, h⟩
    rw [← hu]
    exact ih.union_of_isClosed (continuousOn_interpolation_cell a n) isClosed_Iic isClosed_Icc

/-- The interpolated height is continuous. -/
private theorem continuous_interpolation (a : ℕ → ℝ) :
    Continuous (fun t : ℝ =>
      (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have ht : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  exact (continuousOn_interpolation_Iic a (⌊t⌋₊ + 1)).continuousAt (Iic_mem_nhds ht)

/-! ### Tree height and pair paths -/

/-- Linear interpolation at real time `u` of the DFS heights of a locally finite tree: the
`PlaneTree.heightLin` of the decoded finite tree (heights `|v_i|` for `i < z`, then `0`), and
`0` for an infinite tree. -/
noncomputable def treeHeightLin (τ : BGW.LocallyFinite.Tree) (u : ℝ) : ℝ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).heightLin u
  else 0

/-- The interpolated tree height is continuous (the junk branch of `treeHeightPath` never
occurs). -/
theorem continuous_treeHeightLin (τ : BGW.LocallyFinite.Tree) :
    Continuous (treeHeightLin τ) := by
  change Continuous (fun u => treeHeightLin τ u)
  by_cases hτ : BGW.LocallyFinite.FiniteVertices τ
  · simpa only [treeHeightLin, dite_eq_left hτ, PlaneTree.heightLin] using
      continuous_interpolation (fun i =>
        ((PlaneTree.equivFiniteVertices.symm ⟨τ, hτ⟩).heightSeq i : ℝ))
  · simpa only [treeHeightLin, dite_eq_right hτ] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

/-- **Tree height path** on `[0,T]`: `t ↦ (B n / n) * treeHeightLin τ (n t)`, with the sample
size `n` (not the tree size) as time scale; junk `0` if the interpolation were discontinuous
(never, `continuous_treeHeightLin`). -/
noncomputable def treeHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (τ : BGW.LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  if h : Continuous (treeHeightLin τ) then
    ⟨fun t => B n / n * treeHeightLin τ ((n : ℝ) * (t : ℝ)),
      continuous_const.mul (h.comp (continuous_const.mul continuous_subtype_val))⟩
  else 0

/-- **Tree pair path** on `[0,T]`: the sealed walk path `W_⌊nt⌋ / B n` and the height path
of the same tree. -/
noncomputable def treePairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (τ : BGW.LocallyFinite.Tree) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (treePrefixPath B n T τ, treeHeightPath B n T τ)

/-- **The size-tail pair law** on `[0,T]`: the (walk, height) pair of a BGW tree conditioned on
size `≥ n`, at scales `nt`, `1/B n`, `B n / n`. -/
noncomputable def tailPairLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (tailTreeLaw μ n).map (treePairPath B n T)

/-- The height of the block `[g, d]` read off a height function `h`: `h (g + t)` for
`t ≤ d - g`, and `0` afterwards (stopped at zero). -/
noncomputable def extractedHeight (h : ℝ → ℝ) (g d t : ℝ) : ℝ :=
  if t ≤ d - g then h (g + t) else 0

/-! ### Measurability and consistency -/

theorem measurable_treeHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treeHeightPath B n T) := by
  have hc : Set.Countable {τ : BGW.LocallyFinite.Tree |
      BGW.LocallyFinite.FiniteVertices τ} := by
    apply (Set.to_countable (Set.univ : Set PlaneTree)).image _ |>.mono
    rintro τ hτ
    obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
    exact ⟨t, Set.mem_univ _, rfl⟩
  apply measurable_of_measurable_on_compl_countable _ hc
  have he : (fun τ : {τ : BGW.LocallyFinite.Tree |
      ¬ BGW.LocallyFinite.FiniteVertices τ} => treeHeightPath B n T τ) =
      fun _ => 0 := by
    funext τ
    apply ContinuousMap.ext
    intro x
    change treeHeightPath B n T τ x = 0
    rw [treeHeightPath, dite_eq_left (continuous_treeHeightLin _)]
    change B n / n * treeHeightLin τ ((n : ℝ) * x) = 0
    rw [treeHeightLin, dite_eq_right τ.property, mul_zero]
  change Measurable (fun τ : {τ : BGW.LocallyFinite.Tree |
    ¬ BGW.LocallyFinite.FiniteVertices τ} => treeHeightPath B n T τ)
  rw [he]
  exact measurable_const

theorem measurable_treePairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treePairPath B n T) := by
  exact (measurable_treePrefixPath B n T).prodMk (measurable_treeHeightPath B n T)

/-- On a finite tree the height path is the scaled `PlaneTree.heightLin` (decoding inverts
`toLocallyFinite`). -/
theorem treeHeightPath_toLocallyFinite (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (t : PlaneTree)
    (x : Set.Icc (0 : ℝ) (T : ℝ)) :
    treeHeightPath B n T t.toLocallyFinite x = B n / n * t.heightLin ((n : ℝ) * (x : ℝ)) :=
  by
    simp only [treeHeightPath, dite_eq_left (continuous_treeHeightLin _), ContinuousMap.coe_mk,
      treeHeightLin, dite_eq_left t.finiteVertices_toLocallyFinite]
    change _ *
      (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).heightLin _ = _
    rw [Equiv.symm_apply_apply]

/-- The height path vanishes from time `z/n` on, `z` the size of the tree (stopped at zero). -/
theorem treeHeightPath_eq_zero (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (t : PlaneTree)
    (x : Set.Icc (0 : ℝ) (T : ℝ)) (hx : (t.size : ℝ) ≤ (n : ℝ) * (x : ℝ)) :
    treeHeightPath B n T t.toLocallyFinite x = 0 := by
  rw [treeHeightPath_toLocallyFinite, PlaneTree.heightLin,
    PlaneTree.heightSeq_of_le _ (Nat.le_floor hx),
    PlaneTree.heightSeq_of_le _ (by have := Nat.le_floor hx; omega)]
  simp

/-- The first marginal of the pair law is exactly the sealed tail walk law. -/
theorem tailPairLaw_map_fst (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    (tailPairLaw μ B n T).map Prod.fst = tailWalkLaw μ B n T := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_map measurable_fst (measurable_treePairPath B n T)

/-- **Selected discrete tree** (`firstLongTree_law`): the pair law is the image of the iid
offspring sequence under the pair path of its first ladder block of size `≥ n`. -/
theorem map_offspringSeqLaw_firstLongTree {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (n : ℕ) (T : ℝ≥0) :
    (offspringSeqLaw μ).map (fun ω => treePairPath B n T (firstLongTree n ω)) =
      tailPairLaw μ B n T := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (treePairPath B n T ∘ firstLongTree n) _ = _
  rw [← Measure.map_map (measurable_treePairPath B n T) (measurable_firstLongTree n)]
  exact congrArg (fun P : ProbabilityMeasure BGW.LocallyFinite.Tree =>
    P.toMeasure.map (treePairPath B n T))
      (firstLongTree_law μ h.critical h.nondegenerate n)

/-- **Selected limit mark** (`map_firstLongMark`): the target is the image of the stable
law under the excursion/height pair of its first excursion longer than `1`. -/
theorem map_firstLongMark_excursionPair {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (stableLocalLaw θ).map (fun f => excursionPair θ T (firstLongMark f)) = tailExcLaw θ T :=
  by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (excursionPair θ T ∘ firstLongMark) _ = _
    rw [← AEMeasurable.map_map_of_aemeasurable (measurable_excursionPair θ T).aemeasurable
      (aemeasurable_firstLongMark hθ), map_firstLongMark hθ]
    rfl

/-! ### Locality on both sides and the finite-window coupling bound -/

/-- **Discrete locality** (deterministic, from `forestHeight_eq_treeHeight`): the height path of
the `r`-th ladder block is the normalized forest height extracted at the block endpoints
`(L_r / n, L_{r+1} / n)`. -/
theorem treeHeightPath_blockLF (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (T : ℝ≥0) {ω : ℕ → ℕ}
    (hω : LadderFinite ω) (r : ℕ) (x : Set.Icc (0 : ℝ) (T : ℝ)) :
    treeHeightPath B n T (blockLF ω r) x =
      extractedHeight (fun s => B n / n * forestHeightLin ω ((n : ℝ) * s))
        ((DiscreteForest.ladderTime ω r : ℝ) / n)
        ((DiscreteForest.ladderTime ω (r + 1) : ℝ) / n) x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsize : ((blockTree ω r).size : ℝ) =
      (DiscreteForest.ladderTime ω (r + 1) : ℝ) - DiscreteForest.ladderTime ω r := by
    rw [size_blockTree hω, Nat.cast_sub (DiscreteForest.ladderTime_lt_succ hω r).le]
  rw [blockLF, treeHeightPath_toLocallyFinite, extractedHeight]
  by_cases hx : (x : ℝ) ≤ (DiscreteForest.ladderTime ω (r + 1) : ℝ) / n -
      (DiscreteForest.ladderTime ω r : ℝ) / n
  · rw [ite_eq_left hx]
    have hu : (n : ℝ) * x ≤ ((blockTree ω r).size : ℝ) := by
      rw [hsize]
      have hh := (le_div_iff₀ hn').mp (show (x : ℝ) ≤
        ((DiscreteForest.ladderTime ω (r + 1) : ℝ) - DiscreteForest.ladderTime ω r) / n by
          rwa [sub_div])
      nlinarith
    rw [show (n : ℝ) * ((DiscreteForest.ladderTime ω r : ℝ) / n + x) =
      DiscreteForest.ladderTime ω r + (n : ℝ) * x by field_simp,
      ForestContour.forestHeightLin_ladderTime_add hω r
        (mul_nonneg (Nat.cast_nonneg _) x.property.1) hu]
  · rw [ite_eq_right hx]
    have hu : ((blockTree ω r).size : ℝ) ≤ (n : ℝ) * x := by
      rw [hsize]
      have hh := (div_lt_iff₀ hn').mp (show
        ((DiscreteForest.ladderTime ω (r + 1) : ℝ) - DiscreteForest.ladderTime ω r) / n < (x : ℝ) by
          rw [sub_div]; exact lt_of_not_ge hx)
      nlinarith
    have hz := treeHeightPath_eq_zero B n T (blockTree ω r) x hu
    rwa [treeHeightPath_toLocallyFinite] at hz

/-- **Continuous locality** (height locality at the first long label): almost surely the
height of the first excursion longer than `1` is the continuous host height extracted at its
endpoints. -/
theorem ae_excursionHeight_firstLongMark {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      excursionHeight θ (firstLongMark f) t =
        extractedHeight (fun s => heightLoc θ f s.toNNReal) (firstLongEnds f).1
          (firstLongEnds f).2 t := by
  filter_upwards [ae_jumpExcursion_heightVersion hθ, ae_firstLongLabel_mem hθ,
    ae_jumpExcursion_spec hθ] with f hf hm hs
  intro t
  have hle := (hs (firstLongLabel f) hm.1).1.1.le
  have he := (hf (firstLongLabel f) hm.1).2 t
  simpa only [firstLongMark, firstLongEnds, extractedHeight, NNReal.coe_sub hle,
    ← NNReal.coe_le_coe, ← NNReal.coe_add, Real.toNNReal_coe] using he

/-- **Finite-window coupling bound** (deterministic): the extracted-height error is at most the
uniform error `ε` on `[0,M]` plus the oscillation `η` of the limit height at lag
`|g_n - g| + |d_n - d|`, given the limit endpoint zero `H d = 0`. -/
theorem abs_extractedHeight_sub_le {Hn H : ℝ → ℝ} {gn dn g d M ε η t : ℝ}
    (hg : 0 ≤ g) (hgd : g ≤ d) (hdM : d ≤ M) (hgn : 0 ≤ gn) (hdnM : dn ≤ M)
    (hε : ∀ s ∈ Set.Icc 0 M, |Hn s - H s| ≤ ε) (hd : H d = 0)
    (hη : ∀ x ∈ Set.Icc 0 M, ∀ y ∈ Set.Icc 0 M, |x - y| ≤ |gn - g| + |dn - d| →
      |H x - H y| ≤ η)
    (ht : 0 ≤ t) :
    |extractedHeight Hn gn dn t - extractedHeight H g d t| ≤ ε + η := by
  have hM : 0 ≤ M := hg.trans (hgd.trans hdM)
  have he0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 ⟨le_rfl, hM⟩)
  have hη0 : 0 ≤ η := (abs_nonneg _).trans
    (hη 0 ⟨le_rfl, hM⟩ 0 ⟨le_rfl, hM⟩ (by
      simpa using add_nonneg (abs_nonneg (gn - g)) (abs_nonneg (dn - d))))
  have hdmem : d ∈ Icc 0 M := ⟨hg.trans hgd, hdM⟩
  have hl : -( |gn - g| + |dn - d|) ≤ gn - g := by
    linarith [neg_abs_le (gn - g), abs_nonneg (dn - d)]
  have hr : dn - d ≤ |gn - g| + |dn - d| := by
    linarith [le_abs_self (dn - d), abs_nonneg (gn - g)]
  have hl2 := neg_abs_le (dn - d)
  have hr2 := le_abs_self (gn - g)
  unfold extractedHeight
  split_ifs with hn hh hh
  · have hnm : gn + t ∈ Icc 0 M := ⟨by linarith, by linarith⟩
    have hm : g + t ∈ Icc 0 M := ⟨by linarith, by linarith⟩
    have he := hε (gn + t) hnm
    have ho := hη (gn + t) hnm (g + t) hm (by
      simpa only [add_sub_add_right_eq_sub] using
        (le_add_of_nonneg_right (abs_nonneg (dn - d)) :
          |gn - g| ≤ |gn - g| + |dn - d|))
    calc
      _ ≤ |Hn (gn + t) - H (gn + t)| + |H (gn + t) - H (g + t)| :=
        abs_sub_le _ _ _
      _ ≤ ε + η := add_le_add he ho
  · have hnm : gn + t ∈ Icc 0 M := ⟨by linarith, by linarith⟩
    have he := hε (gn + t) hnm
    have ho := hη (gn + t) hnm d hdmem (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [hd] at ho
    simpa using (abs_sub_le (Hn (gn + t)) (H (gn + t)) 0).trans (add_le_add he ho)
  · have hm : g + t ∈ Icc 0 M := ⟨by linarith, by linarith⟩
    have ho := hη (g + t) hm d hdmem (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [hd, sub_zero] at ho
    simpa only [zero_sub, abs_neg] using ho.trans (le_add_of_nonneg_left he0)
  · simpa using add_nonneg he0 hη0

end BGW.StableTrees.TailPair
