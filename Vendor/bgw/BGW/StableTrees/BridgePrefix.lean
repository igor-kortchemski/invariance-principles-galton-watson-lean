/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.StableDensityAPI
public import BGW.StableTrees.StableLevyLaw
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Independence.Basic

/-! # Stable bridge prefix laws

The stable transition density defines normalized, consistent changes of measure on every
strict prefix of the unit interval.

References: J. Bertoin, *Lévy Processes* (1996), ch. VIII (bridges); L. Chaumont, *Excursion
normalisée, méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997);
item C31 of `CLASSICAL_THEORY_INPUTS.md`.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BGW.StableTrees

open BGW.Skorokhod

/-- The prefix weight `wₐ(f) = p_{1-a}(-f(a)) / p₁(0)`. -/
noncomputable def bridgePrefixWeight (θ a : ℝ) (ha : 0 ≤ a) (f : D a ℝ) : ℝ :=
  stableDensityAt θ (1 - a) (-f ⟨a, ha, le_rfl⟩) / Scalar.stableDensity θ 0

/-- The prefix measure obtained by weighting a path law by `bridgePrefixWeight`. -/
noncomputable def bridgePrefixLaw (θ a : ℝ) (ha : 0 ≤ a) (P : Measure (D a ℝ)) :
    Measure (D a ℝ) :=
  P.withDensity fun f => ENNReal.ofReal (bridgePrefixWeight θ a ha f)

/-- The bridge prefix weight is nonnegative whenever `a < 1`. -/
theorem bridgePrefixWeight_nonneg {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 ≤ a) (ha1 : a < 1)
    (f : D a ℝ) : 0 ≤ bridgePrefixWeight θ a ha f := by
  have ht : 0 < 1 - a := by linarith
  have hnum := stableDensityAt_nonneg hθ ht (-f ⟨a, ha, le_rfl⟩)
  have hden := Scalar.stableDensity_zero_pos hθ
  exact div_nonneg hnum (le_of_lt hden)

/-- The bridge prefix weight is measurable for the Borel σ-algebra on path space. -/
theorem measurable_bridgePrefixWeight {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 ≤ a) :
    Measurable (bridgePrefixWeight θ a ha) := by
  have hden : Scalar.stableDensity θ 0 ≠ 0 := (Scalar.stableDensity_zero_pos hθ).ne'
  have heval : Measurable (fun f : D a ℝ => f ⟨a, ha, le_rfl⟩) := measurable_eval _
  have hnum : Measurable (fun f : D a ℝ =>
      stableDensityAt θ (1 - a) (-f ⟨a, ha, le_rfl⟩)) :=
    (stableDensityAt_continuous hθ).measurable.comp (heval.neg)
  exact hnum.div_const _

/-- For each fixed `a < 1`, the bridge prefix weight is bounded. -/
theorem bridgePrefixWeight_le {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, ∀ f : D a ℝ, bridgePrefixWeight θ a ha f ≤ C := by
  have ht : 0 < 1 - a := by linarith
  obtain ⟨C, hC⟩ := stableDensityAt_le_of_ge hθ ht
  have hden : 0 < Scalar.stableDensity θ 0 := Scalar.stableDensity_zero_pos hθ
  refine ⟨C / Scalar.stableDensity θ 0, fun f => ?_⟩
  exact div_le_div_of_nonneg_right (hC (1 - a) le_rfl _) hden.le

private theorem map_eval_endpoint_eq_stableLawAt {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    Measure.map (fun f : D T ℝ => f ⟨T, hT.le, le_rfl⟩) (P : Measure (D T ℝ)) =
      (stableLawAt θ T : Measure ℝ) := by
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  let e : Set.Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
  let τ : Fin 2 → Set.Icc (0 : ℝ) T := fun i => if i.val = 0 then z else e
  have hτ : StrictMono τ := by
    intro i j hij
    have hij' : i.val < j.val := Fin.lt_def.mp hij
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · omega
    · have hi0 : i = 0 := Fin.ext hi
      have hj1 : j = 1 := Fin.ext hj
      change (τ i : ℝ) < (τ j : ℝ)
      simpa [τ, hi0, hj1, z, e] using hT
    · omega
    · omega
  let inc : D T ℝ → (Fin 1 → ℝ) := fun f i => f (τ i.succ) - f (τ i.castSucc)
  let coord : (Fin 1 → ℝ) → ℝ := fun x => x 0
  have hinc : Measure.map inc (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin 1 =>
        (stableLawAt θ ((τ i.succ : ℝ) - τ i.castSucc) : Measure ℝ)) :=
    hP.map_increments 1 τ hτ
  have hincMeas : Measurable inc := Measurable.of_eval fun i =>
    (measurable_eval (τ i.succ)).sub (measurable_eval (τ i.castSucc))
  have hcoord : Measurable coord := measurable_pi_apply 0
  have hcoordlaw : Measure.map coord (Measure.pi fun i : Fin 1 =>
      (stableLawAt θ ((τ i.succ : ℝ) - τ i.castSucc) : Measure ℝ)) =
      (stableLawAt θ ((e : ℝ) - z) : Measure ℝ) := by
    rw [show coord = Function.eval (⟨0, by omega⟩ : Fin 1) from rfl,
      Measure.pi_map_eval]
    simp [τ, z, e]
  have hcomp : (fun f : D T ℝ => f e - f z) = coord ∘ inc := by
    funext f
    simp [coord, inc, τ, z, e]
  have hstart : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), f z = 0 := by
    simpa [z] using hP.start hT.le
  have hae : (fun f : D T ℝ => f e) =ᵐ[(P : Measure (D T ℝ))]
      fun f => f e - f z := by
    filter_upwards [hstart] with f hf
    simp [hf]
  calc
    Measure.map (fun f : D T ℝ => f e) (P : Measure (D T ℝ)) =
        Measure.map (fun f : D T ℝ => f e - f z) (P : Measure (D T ℝ)) :=
      Measure.map_congr hae
    _ = Measure.map (coord ∘ inc) (P : Measure (D T ℝ)) := by rw [hcomp]
    _ = Measure.map coord (Measure.map inc (P : Measure (D T ℝ))) :=
      (Measure.map_map hcoord hincMeas).symm
    _ = Measure.map coord (Measure.pi fun i : Fin 1 =>
          (stableLawAt θ ((τ i.succ : ℝ) - τ i.castSucc) : Measure ℝ)) :=
      congrArg (Measure.map coord) hinc
    _ = (stableLawAt θ T : Measure ℝ) := by
      simpa [e, z] using hcoordlaw

/-- **Mass one.** Every stable Lévy law on `[0,a]` integrates the bridge weight to one. -/
theorem bridgePrefix_mass_one {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (ha1 : a < 1)
    {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    ∫⁻ f, ENNReal.ofReal (bridgePrefixWeight θ a ha.le f) ∂(P : Measure (D a ℝ)) = 1 := by
  have hweightMeas := measurable_bridgePrefixWeight hθ ha.le
  have hweightNonneg (f : D a ℝ) := bridgePrefixWeight_nonneg hθ ha.le ha1 f
  obtain ⟨C, hC⟩ := bridgePrefixWeight_le hθ ha.le ha1
  have hweightBound : ∀ f : D a ℝ,
      ‖bridgePrefixWeight θ a ha.le f‖ ≤ |C| := by
    intro f
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hweightNonneg f, abs_nonneg C], le_trans (hC f) (le_abs_self C)⟩
  have hweightInt : Integrable (bridgePrefixWeight θ a ha.le) (P : Measure (D a ℝ)) := by
    exact (MemLp.of_bound hweightMeas.aestronglyMeasurable |C|
      (ae_of_all _ hweightBound)).integrable le_rfl
  have hweightAE : 0 ≤ᵐ[(P : Measure (D a ℝ))] bridgePrefixWeight θ a ha.le :=
    ae_of_all _ hweightNonneg
  have hden : 0 < Scalar.stableDensity θ 0 := Scalar.stableDensity_zero_pos hθ
  have hnum : ∫ f, stableDensityAt θ (1 - a) (-f ⟨a, ha.le, le_rfl⟩)
      ∂(P : Measure (D a ℝ)) = Scalar.stableDensity θ 0 := by
    let ev : D a ℝ → ℝ := fun f => f ⟨a, ha.le, le_rfl⟩
    have hev : Measurable ev := measurable_eval _
    have hlaw := map_eval_endpoint_eq_stableLawAt ha hP
    have hgmeas : Measurable (fun y : ℝ => stableDensityAt θ (1 - a) (-y)) :=
      (stableDensityAt_continuous hθ).comp continuous_neg |>.measurable
    have hgm : AEStronglyMeasurable (fun y : ℝ => stableDensityAt θ (1 - a) (-y))
        (Measure.map ev (P : Measure (D a ℝ))) := by
      rw [hlaw]
      exact hgmeas.aestronglyMeasurable
    calc
      ∫ f, stableDensityAt θ (1 - a) (-ev f) ∂(P : Measure (D a ℝ)) =
          ∫ y, stableDensityAt θ (1 - a) (-y) ∂Measure.map ev (P : Measure (D a ℝ)) := by
        exact (integral_map hev.aemeasurable hgm).symm
      _ = ∫ y, stableDensityAt θ (1 - a) (-y) ∂(stableLawAt θ a : Measure ℝ) := by
        rw [hlaw]
      _ = ∫ y, stableDensityAt θ a y * stableDensityAt θ (1 - a) (0 - y) := by
        rw [stableLawAt_eq_withDensity hθ ha]
        rw [integral_withDensity_eq_integral_toReal_smul (μ := volume)
          (f := fun y => ENNReal.ofReal (stableDensityAt θ a y))
          (ENNReal.measurable_ofReal.comp (stableDensityAt_continuous hθ).measurable)
          (ae_of_all _ (fun y => ENNReal.ofReal_lt_top))
          (fun y => stableDensityAt θ (1 - a) (-y))]
        apply integral_congr_ae
        filter_upwards [] with y
        simp [smul_eq_mul, ENNReal.toReal_ofReal
          (stableDensityAt_nonneg hθ ha y)]
      _ = stableDensityAt θ 1 0 := by
        simpa [mul_comm] using (integral_stableDensityAt_mul hθ
          (s := a) (t := 1 - a) ha (by linarith) (0 : ℝ))
      _ = Scalar.stableDensity θ 0 := stableDensityAt_one θ 0
  have hreal : ∫ f, bridgePrefixWeight θ a ha.le f ∂(P : Measure (D a ℝ)) = 1 := by
    change (∫ f, stableDensityAt θ (1 - a) (-f ⟨a, ha.le, le_rfl⟩) /
      Scalar.stableDensity θ 0 ∂(P : Measure (D a ℝ))) = 1
    calc
      _ = (∫ f, stableDensityAt θ (1 - a) (-f ⟨a, ha.le, le_rfl⟩)
          ∂(P : Measure (D a ℝ))) * (Scalar.stableDensity θ 0)⁻¹ := by
        rw [show (fun f : D a ℝ => stableDensityAt θ (1 - a)
            (-f ⟨a, ha.le, le_rfl⟩) / Scalar.stableDensity θ 0) =
            fun f => stableDensityAt θ (1 - a) (-f ⟨a, ha.le, le_rfl⟩) *
              (Scalar.stableDensity θ 0)⁻¹ from by funext f; exact div_eq_mul_inv _ _,
          integral_mul_const]
      _ = 1 := by rw [hnum]; exact mul_inv_cancel₀ hden.ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hweightInt hweightAE, hreal]
  norm_num

/-- A normalized bridge prefix is a probability measure. -/
theorem isProbabilityMeasure_bridgePrefixLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (ha1 : a < 1) {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    IsProbabilityMeasure (bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))) := by
  refine ⟨?_⟩
  rw [bridgePrefixLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact bridgePrefix_mass_one hθ ha ha1 hP

/-- The prefix law does not depend on the choice of the stable law `P` (uniqueness). -/
theorem bridgePrefixLaw_unique {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    {P Q : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) (hQ : IsStableLevyLaw θ a Q) :
    bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ)) =
      bridgePrefixLaw θ a ha.le (Q : Measure (D a ℝ)) := by
  have h := hP.unique hθ ha hQ
  rw [h]

private def cumulativeP {n : ℕ} (x : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ j : Fin i.val, x ⟨j.val, by omega⟩

private theorem sum_range_sub_seqP (g : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (g (j + 1) - g j)) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem eval_eq_cumulativeP {T : ℝ} {n : ℕ}
    (v : Fin (n + 1) → Set.Icc (0 : ℝ) T) (f : BGW.Skorokhod.D T ℝ)
    (i : Fin (n + 1)) :
    f (v i) = f (v 0) + cumulativeP (fun j => f (v j.succ) - f (v j.castSucc)) i := by
  have hin : i.val ≤ n := by omega
  let g : ℕ → ℝ := fun j => f (v ⟨min j n, by omega⟩)
  let d : Fin n → ℝ := fun j => f (v j.succ) - f (v j.castSucc)
  have hsum :
      (∑ j ∈ Finset.range i.val, (g (j + 1) - g j)) = cumulativeP d i := by
    rw [← Fin.sum_univ_eq_sum_range]
    dsimp [cumulativeP, d]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j.val < n := by omega
    have hj1n : j.val + 1 ≤ n := by omega
    simp only [g, min_eq_left hjn.le, min_eq_left hj1n]
  have htel := sum_range_sub_seqP g i.val
  have hg_i : g i.val = f (v i) := by
    change f (v ⟨min i.val n, by omega⟩) = f (v i)
    apply congrArg (fun j : Fin (n + 1) => f (v j))
    exact Fin.ext (min_eq_left hin)
  have hg_0 : g 0 = f (v 0) := by
    change f (v ⟨min 0 n, by omega⟩) = f (v 0)
    apply congrArg (fun j : Fin (n + 1) => f (v j))
    exact Fin.ext (min_eq_left (Nat.zero_le n))
  rw [hsum] at htel
  rw [hg_i, hg_0] at htel
  linarith

private theorem indepCoordsP {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (inc : Ω → Fin n → ℝ) (μ : Fin n → Measure ℝ)
    (hmeas : Measurable inc) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hinc : Measure.map inc P = Measure.pi μ) :
    iIndepFun (fun i x => inc x i) P := by
  classical
  have hmarg (i : Fin n) : Measure.map (fun x => inc x i) P = μ i := by
    rw [show (fun x => inc x i) = Function.eval i ∘ inc by rfl,
      ← Measure.map_map (measurable_pi_apply i) hmeas, hinc,
      Measure.pi_map_eval]
    simp
  have hpi : Measure.pi μ = Measure.pi (fun i => Measure.map (fun x => inc x i) P) := by
    apply Measure.pi_eq
    intro s hs
    rw [Measure.pi_pi]
    exact Finset.prod_congr rfl fun i hi => by rw [hmarg i]
  refine (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    ((measurable_pi_apply i).comp hmeas).aemeasurable)).2 ?_
  calc
    Measure.map (fun x i => inc x i) P = Measure.pi μ := by simpa using hinc
    _ = Measure.pi (fun i => Measure.map (fun x => inc x i) P) := hpi

private theorem evalFinset_indep_incrementP {θ : ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {P : ProbabilityMeasure (BGW.Skorokhod.D b ℝ)}
    (hP : BGW.StableTrees.IsStableLevyLaw θ b P)
    (s : Finset (Set.Icc (0 : ℝ) b)) (hs : ∀ q ∈ s, (q : ℝ) ≤ a) :
    IndepFun (fun f : BGW.Skorokhod.D b ℝ => fun q : s => f q.val)
      (fun f => f ⟨b, le_trans (le_of_lt ha) hab.le, le_rfl⟩ -
        f ⟨a, le_of_lt ha, hab.le⟩)
      (↑P) := by
  classical
  let z : Set.Icc (0 : ℝ) b := ⟨0, le_rfl, le_trans (le_of_lt ha) hab.le⟩
  let aPoint : Set.Icc (0 : ℝ) b := ⟨a, le_of_lt ha, hab.le⟩
  let bt : Set.Icc (0 : ℝ) b := ⟨b, le_trans (le_of_lt ha) hab.le, le_rfl⟩
  let r := insert z (insert aPoint (insert bt s))
  have hrpos : 0 < r.card := Finset.card_pos.mpr ⟨z, Finset.mem_insert_self _ _⟩
  let n := r.card - 1
  have hn : n + 1 = r.card := by dsimp [n]; omega
  let e : Fin (n + 1) ≃o r := (Fin.castOrderIso hn).trans (r.orderIsoOfFin rfl)
  let v : Fin (n + 1) → Set.Icc (0 : ℝ) b := fun i => (e i).val
  let rz : r := ⟨z, Finset.mem_insert_self _ _⟩
  let ra : r := ⟨aPoint, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  let rb : r := ⟨bt, Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
  let iz := e.symm rz
  let ia := e.symm ra
  let ib := e.symm rb
  have hv : StrictMono v := by
    intro i j hij
    change e i < e j
    exact e.strictMono hij
  have hv0 : v 0 = z := by
    apply Subtype.ext
    have hmin : e 0 ≤ rz := by
      have hle := e.monotone (Fin.zero_le (e.symm rz))
      simpa [iz] using hle
    change ((e 0).val : ℝ) = 0
    apply le_antisymm
    · exact_mod_cast hmin
    · exact (e 0).val.property.1
  have hva : v ia = aPoint := by
    apply Subtype.ext
    change ((e (e.symm ra)).val : ℝ) = (aPoint : ℝ)
    exact congrArg (fun q : r => (q.val : ℝ)) (e.apply_symm_apply ra)
  have hvb : v ib = bt := by
    apply Subtype.ext
    change ((e (e.symm rb)).val : ℝ) = (bt : ℝ)
    exact congrArg (fun q : r => (q.val : ℝ)) (e.apply_symm_apply rb)
  have hiaib : ia < ib := by
    apply e.symm.strictMono
    change a < b
    exact hab
  have hia_lt_n : ia.val < n := by
    have := Fin.lt_def.mp hiaib
    omega
  let ia' : Fin n := ⟨ia.val, hia_lt_n⟩
  have hsucc : ia'.succ = ib := by
    apply Fin.ext
    have hgap : ia.val + 1 = ib.val := by
      have hlt : ia.val + 1 ≤ ib.val := by
        have := Fin.lt_def.mp hiaib
        omega
      by_contra hne
      have hstrict : ia.val + 1 < ib.val := by omega
      let j : Fin (n + 1) := ⟨ia.val + 1, by omega⟩
      have hja : ia < j := by apply Fin.lt_def.mpr; simp [j]
      have hjb : j < ib := Fin.lt_def.mpr (by simpa [j] using hstrict)
      have hjlow : a < (v j : ℝ) := by
        have h := hv hja
        rw [hva] at h
        exact h
      have hjhigh : (v j : ℝ) < b := by
        have h := hv hjb
        rw [hvb] at h
        exact h
      have hjmem : (e j).val ∈ r := (e j).property
      simp only [r, Finset.mem_insert] at hjmem
      rcases hjmem with hjz | hrest
      · have : (v j : ℝ) = 0 := by simpa [v] using congrArg Subtype.val hjz
        linarith [le_of_lt ha]
      · rcases hrest with hja' | hrest
        · have : (v j : ℝ) = a := by simpa [v, aPoint] using congrArg Subtype.val hja'
          linarith
        · rcases hrest with hjb' | hrest
          · have : (v j : ℝ) = b := by simpa [v, bt] using congrArg Subtype.val hjb'
            linarith
          · have hq : (e j).val ∈ s := hrest
            have : (v j : ℝ) ≤ a := hs ((e j).val) hq
            linarith
    simpa [ia'] using hgap
  let inc : BGW.Skorokhod.D b ℝ → Fin n → ℝ :=
    fun f i => f (v i.succ) - f (v i.castSucc)
  let μ : Fin n → Measure ℝ := fun i =>
    (BGW.StableTrees.stableLawAt θ ((v i.succ : ℝ) - v i.castSucc) : Measure ℝ)
  have hincMeas : Measurable inc := Measurable.of_eval fun i =>
    (measurable_eval (v i.succ)).sub (measurable_eval (v i.castSucc))
  have hsource : Measure.map inc (P : Measure (BGW.Skorokhod.D b ℝ)) = Measure.pi μ :=
    hP.map_increments n v hv
  have hcoords : iIndepFun (fun i f => inc f i) (P : Measure (BGW.Skorokhod.D b ℝ)) :=
    indepCoordsP _ inc μ hincMeas (fun i => inferInstance) hsource
  let S : Finset (Fin n) := Finset.univ.filter (fun i => i.val < ia'.val)
  have hdisj : Disjoint S {ia'} := by
    rw [Finset.disjoint_singleton_right]
    simp [S, ia']
  let Tfin : Finset (Fin n) := {ia'}
  have hprefix := hcoords.indepFun_finset S Tfin hdisj
    (fun i => (measurable_pi_apply i).comp hincMeas)
  let pre : BGW.Skorokhod.D b ℝ → S → ℝ := fun f i => inc f i
  let ev : BGW.Skorokhod.D b ℝ → s → ℝ := fun f q => f q.val
  let extend : (S → ℝ) → Fin n → ℝ := fun x i =>
    if hi : i.val < ia'.val then
      x ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩ else 0
  let recon : (S → ℝ) → s → ℝ := fun x q => cumulativeP (extend x) (e.symm ⟨q.val,
    by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact q.property⟩)
  have hmeasRecon : Measurable recon := by
    apply Measurable.of_eval
    intro q
    simp only [recon, cumulativeP]
    fun_prop
  let iaMem : Tfin := ⟨ia', by simp [Tfin]⟩
  let get : (Tfin → ℝ) → ℝ := fun x => x iaMem
  have hmeasGet : Measurable get := by
    exact measurable_pi_apply iaMem
  have hdep := hprefix.comp hmeasRecon hmeasGet
  have hae : ev =ᵐ[(P : Measure (BGW.Skorokhod.D b ℝ))] recon ∘ pre := by
    have hstart : ∀ᵐ f : BGW.Skorokhod.D b ℝ ∂(P : Measure _), f z = 0 := by
      simpa [z] using hP.start (le_trans (le_of_lt ha) hab.le)
    filter_upwards [hstart] with f hf
    funext q
    let rq : r := ⟨q.val, by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact q.property⟩
    let iq := e.symm rq
    have hqA : rq ≤ ra := by
      apply Subtype.mk_le_mk.mpr
      exact hs q.val q.property
    have hiqA : iq ≤ ia := e.symm.monotone hqA
    have htime : v iq = q.val := by
      apply Subtype.ext
      simp [v, iq, rq]
    have heval := eval_eq_cumulativeP v f iq
    have hzero : f (v 0) = 0 := by rw [hv0]; exact hf
    rw [htime, hzero, zero_add] at heval
    have hsum : cumulativeP (fun i => f (v i.succ) - f (v i.castSucc)) iq =
        cumulativeP (extend (pre f)) iq := by
      unfold cumulativeP
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j.val < ia'.val := by
        have : j.val < iq.val := j.isLt
        have hiq := Fin.le_iff_val_le_val.mp hiqA
        simp [ia'] at *
        omega
      let jn : Fin n := ⟨j.val, by omega⟩
      have hjval : jn.val < ia'.val := by simpa [jn] using hjlt
      have hext : extend (pre f) jn = inc f jn := by
        simp only [extend]
        rw [dite_eq_left hjval]
      change inc f jn = extend (pre f) jn
      rw [hext]
    simpa [ev, recon, rq, iq, pre] using heval.trans (congrArg (fun x => x) hsum)
  have hright : get ∘ (fun f i => inc f i) =ᵐ[(P : Measure (BGW.Skorokhod.D b ℝ))]
      fun f => inc f ia' := by
    filter_upwards [] with f
    simp [get, iaMem, Tfin]
  have hfinal := hdep.congr hae.symm hright
  have hincEq : (fun f => inc f ia') =
      (fun f => f bt - f aPoint) := by
    funext f
    dsimp [inc]
    have hcast : ia'.castSucc = ia := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast, hva, hvb]
  simpa [bt, aPoint] using hincEq ▸ hfinal

private def bridgeIncrementPathP {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    BGW.Skorokhod.D b ℝ → ℝ := fun f =>
  f ⟨b, ha.trans hab, le_rfl⟩ - f ⟨a, ha, hab⟩

@[instance_reducible] private def bridgeIncrementSigmaP {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MeasurableSpace (BGW.Skorokhod.D b ℝ) :=
  MeasurableSpace.comap (bridgeIncrementPathP ha hab) (inferInstance : MeasurableSpace ℝ)

private theorem path_indep_incrementP {θ : ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {P : ProbabilityMeasure (BGW.Skorokhod.D b ℝ)}
    (hP : BGW.StableTrees.IsStableLevyLaw θ b P) :
    Indep (MeasurableSpace.comap (BGW.Skorokhod.restrict (le_of_lt hab))
        (inferInstance : MeasurableSpace (BGW.Skorokhod.D a ℝ)))
      (bridgeIncrementSigmaP (le_of_lt ha) hab.le)
      (_mΩ := BGW.Skorokhod.instMeasurableSpace)
      (μ := ProbabilityMeasure.toMeasure P) := by
  classical
  let A := {q : Set.Icc (0 : ℝ) b // (q : ℝ) ≤ a}
  let times : Finset A → Finset (Set.Icc (0 : ℝ) b) :=
    fun s => s.image Subtype.val
  let evalVec (s : Finset A) : BGW.Skorokhod.D b ℝ → times s → ℝ :=
    fun f q => f q.val
  let coordSigma (q : Set.Icc (0 : ℝ) b) : MeasurableSpace (BGW.Skorokhod.D b ℝ) :=
    MeasurableSpace.comap (fun f : BGW.Skorokhod.D b ℝ => f q)
      (inferInstance : MeasurableSpace ℝ)
  let m (s : Finset A) : MeasurableSpace (BGW.Skorokhod.D b ℝ) :=
    MeasurableSpace.comap (evalVec s) inferInstance
  let μP : @Measure (BGW.Skorokhod.D b ℝ) BGW.Skorokhod.instMeasurableSpace :=
    @ProbabilityMeasure.toMeasure (BGW.Skorokhod.D b ℝ)
      BGW.Skorokhod.instMeasurableSpace P
  have hm_indep (s : Finset A) := by
    have ht : ∀ q ∈ times s, (q : ℝ) ≤ a := by
      intro q hq
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
      exact u.property
    have hfinite := evalFinset_indep_incrementP ha hab hP (times s) ht
    exact (IndepFun_iff_Indep _ _ _).mp hfinite
  have hm_le (s : Finset A) : m s ≤ BGW.Skorokhod.instMeasurableSpace := by
    change MeasurableSpace.comap (evalVec s) inferInstance ≤ _
    have hev : @Measurable (BGW.Skorokhod.D b ℝ) (times s → ℝ)
        BGW.Skorokhod.instMeasurableSpace inferInstance (evalVec s) :=
      Measurable.of_eval (fun q : times s => measurable_eval q.val)
    exact hev.comap_le
  have hmy_le : bridgeIncrementSigmaP (le_of_lt ha) hab.le ≤ BGW.Skorokhod.instMeasurableSpace := by
    change MeasurableSpace.comap (bridgeIncrementPathP (le_of_lt ha) hab.le)
      (inferInstance : MeasurableSpace ℝ) ≤ _
    have hy : Measurable (bridgeIncrementPathP (le_of_lt ha) hab.le) := by
      exact (measurable_eval (⟨b, le_trans (le_of_lt ha) hab.le, le_rfl⟩ : Set.Icc (0 : ℝ) b)).sub
        (measurable_eval (⟨a, le_of_lt ha, hab.le⟩ : Set.Icc (0 : ℝ) b))
    exact hy.comap_le
  have hm_directed : Directed (· ≤ ·) m := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · change MeasurableSpace.comap (evalVec s) inferInstance ≤
        MeasurableSpace.comap (evalVec (s ∪ t)) inferInstance
      rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
      apply iSup_le
      intro q
      obtain ⟨u, hu, hqu⟩ := Finset.mem_image.mp q.property
      let q' : times (s ∪ t) := ⟨q.val, Finset.mem_image.mpr ⟨u,
        Finset.mem_union_left _ hu, hqu⟩⟩
      exact le_iSup_of_le q' (by rfl)
    · change MeasurableSpace.comap (evalVec t) inferInstance ≤
        MeasurableSpace.comap (evalVec (s ∪ t)) inferInstance
      rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
      apply iSup_le
      intro q
      obtain ⟨u, hu, hqu⟩ := Finset.mem_image.mp q.property
      let q' : times (s ∪ t) := ⟨q.val, Finset.mem_image.mpr ⟨u,
        Finset.mem_union_right _ hu, hqu⟩⟩
      exact le_iSup_of_le q' (by rfl)
  have hsup : (⨆ s : Finset A, m s) = ⨆ q : A, coordSigma q.val := by
    apply le_antisymm
    · apply iSup_le
      intro s
      change MeasurableSpace.comap (evalVec s) inferInstance ≤ _
      rw [MeasurableSpace.comap_process_pi]
      apply iSup_le
      intro q
      obtain ⟨u, hu, hqu⟩ := Finset.mem_image.mp q.property
      rw [← hqu]
      exact le_iSup_of_le u le_rfl
    · apply iSup_le
      intro q
      let s : Finset A := {q}
      let t : times s := ⟨q.val, Finset.mem_image.mpr ⟨q, by simp [s], rfl⟩⟩
      refine le_iSup_of_le s ?_
      change coordSigma q.val ≤ MeasurableSpace.comap (evalVec s) inferInstance
      rw [MeasurableSpace.comap_process_pi]
      exact le_iSup_of_le t (by rfl)
  have hspace :
      (inferInstance : MeasurableSpace (BGW.Skorokhod.D a ℝ)).comap
          (BGW.Skorokhod.restrict (le_of_lt hab)) = ⨆ q : A, coordSigma q.val := by
    rw [BGW.Skorokhod.measurableSpace_eq_iSup_comap_eval (T := a) (E := ℝ)
      (S := univ) dense_univ (le_of_lt ha) (by simp)]
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Set.mem_univ]
    simp only [iSup_true]
    apply le_antisymm
    · apply iSup_le
      intro q
      let q' : A := ⟨⟨q.val, q.property.1, q.property.2.trans hab.le⟩, q.property.2⟩
      change coordSigma q'.val ≤ _
      exact le_iSup_of_le q' (by rfl)
    · apply iSup_le
      intro q
      let q' : Set.Icc (0 : ℝ) a := ⟨q.val, q.val.property.1, q.property⟩
      exact le_iSup_of_le q' (by rfl)
  have hindep := ProbabilityTheory.indep_iSup_of_directed_le
    (m := m) (m1 := bridgeIncrementSigmaP (le_of_lt ha) hab.le)
    (_mΩ := BGW.Skorokhod.instMeasurableSpace) (μ := μP)
    hm_indep hm_le hmy_le hm_directed
  rw [hsup, ← hspace] at hindep
  simpa [bridgeIncrementSigmaP, bridgeIncrementPathP] using hindep

private theorem map_prefix_incrementP {θ : ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {P : ProbabilityMeasure (BGW.Skorokhod.D b ℝ)}
    (hP : BGW.StableTrees.IsStableLevyLaw θ b P) :
    Measure.map (bridgeIncrementPathP (le_of_lt ha) hab.le)
      (ProbabilityMeasure.toMeasure P) =
      (BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ) := by
  classical
  let z : Set.Icc (0 : ℝ) b := ⟨0, le_rfl, le_trans (le_of_lt ha) hab.le⟩
  let aPoint : Set.Icc (0 : ℝ) b := ⟨a, le_of_lt ha, hab.le⟩
  let bt : Set.Icc (0 : ℝ) b := ⟨b, le_trans (le_of_lt ha) hab.le, le_rfl⟩
  let τ : Fin 3 → Set.Icc (0 : ℝ) b :=
    fun i => if i.val = 0 then z else if i.val = 1 then aPoint else bt
  have hτ : StrictMono τ := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · simp [τ, z, aPoint]
      exact_mod_cast ha
    · simp [τ, aPoint, bt]
      exact_mod_cast hab
  let inc : BGW.Skorokhod.D b ℝ → Fin 2 → ℝ :=
    fun f i => f (τ i.succ) - f (τ i.castSucc)
  let μ : Fin 2 → Measure ℝ := fun i =>
    (BGW.StableTrees.stableLawAt θ ((τ i.succ : ℝ) - τ i.castSucc) : Measure ℝ)
  have hinc : Measure.map inc (ProbabilityMeasure.toMeasure P) = Measure.pi μ :=
    hP.map_increments 2 τ hτ
  let coord : (Fin 2 → ℝ) → ℝ := fun x => x ⟨1, by omega⟩
  have hcoord : Measurable coord := measurable_pi_apply _
  have hcoordlaw : Measure.map coord (Measure.pi μ) =
      (BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ) := by
    rw [show coord = Function.eval (⟨1, by omega⟩ : Fin 2) from rfl,
      Measure.pi_map_eval]
    simp [τ, μ, z, aPoint, bt]
  have hcomp : bridgeIncrementPathP (le_of_lt ha) hab.le = coord ∘ inc := by
    funext f
    simp [bridgeIncrementPathP, coord, inc, τ, aPoint, bt]
  have hincMeas : Measurable inc := Measurable.of_eval fun i =>
    (measurable_eval (τ i.succ)).sub (measurable_eval (τ i.castSucc))
  calc
    Measure.map (bridgeIncrementPathP (le_of_lt ha) hab.le) (ProbabilityMeasure.toMeasure P) =
        Measure.map (coord ∘ inc) (ProbabilityMeasure.toMeasure P) := by rw [hcomp]
    _ = Measure.map coord (Measure.map inc (ProbabilityMeasure.toMeasure P)) :=
      (Measure.map_map hcoord hincMeas).symm
    _ = Measure.map coord (Measure.pi μ) := by rw [hinc]
    _ = (BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ) := hcoordlaw

private theorem convolution_lintegralP {θ a b x : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (_ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∫⁻ y, ENNReal.ofReal
        (BGW.StableTrees.stableDensityAt θ (1 - b) (-(x + y)) /
          BGW.StableTrees.Scalar.stableDensity θ 0)
      ∂(BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ) =
      ENNReal.ofReal (BGW.StableTrees.stableDensityAt θ (1 - a) (-x) /
        BGW.StableTrees.Scalar.stableDensity θ 0) := by
  let s := b - a
  let t := 1 - b
  let p0 := BGW.StableTrees.Scalar.stableDensity θ 0
  let g : ℝ → ℝ := fun y => BGW.StableTrees.stableDensityAt θ t (-(x + y))
  have hs : 0 < s := by dsimp [s]; linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have hden : 0 < p0 := by exact BGW.StableTrees.Scalar.stableDensity_zero_pos hθ
  have hgmeas : Measurable g := by
    dsimp [g]
    exact (BGW.StableTrees.stableDensityAt_continuous hθ).measurable.comp
      (measurable_const.add measurable_id |>.neg)
  obtain ⟨C, hC⟩ := BGW.StableTrees.stableDensityAt_le_of_ge hθ ht
  have hgbound : ∀ y : ℝ, ‖g y‖ ≤ |C| := by
    intro y
    rw [Real.norm_eq_abs, abs_le]
    have hnonneg := BGW.StableTrees.stableDensityAt_nonneg hθ ht (-(x + y))
    exact ⟨by linarith [abs_nonneg C], le_trans (hC t le_rfl (-(x + y))) (le_abs_self C)⟩
  have hgint : Integrable g (BGW.StableTrees.stableLawAt θ s : Measure ℝ) := by
    exact (MemLp.of_bound hgmeas.aestronglyMeasurable |C|
      (ae_of_all _ hgbound)).integrable le_rfl
  have hgae : 0 ≤ᵐ[(BGW.StableTrees.stableLawAt θ s : Measure ℝ)] g :=
    ae_of_all _ fun y => BGW.StableTrees.stableDensityAt_nonneg hθ ht (-(x + y))
  have hdivInt : Integrable (fun y => g y / p0)
      (BGW.StableTrees.stableLawAt θ s : Measure ℝ) := hgint.div_const p0
  have hdivAE : 0 ≤ᵐ[(BGW.StableTrees.stableLawAt θ s : Measure ℝ)] fun y => g y / p0 :=
    hgae.mono fun y hy => div_nonneg hy hden.le
  have hconv : ∫ y, g y ∂(BGW.StableTrees.stableLawAt θ s : Measure ℝ) =
      BGW.StableTrees.stableDensityAt θ (s + t) (-x) := by
    rw [BGW.StableTrees.stableLawAt_eq_withDensity hθ hs]
    rw [integral_withDensity_eq_integral_toReal_smul (μ := volume)
      (f := fun y => ENNReal.ofReal (BGW.StableTrees.stableDensityAt θ s y))
      (ENNReal.measurable_ofReal.comp
        (BGW.StableTrees.stableDensityAt_continuous hθ).measurable)
      (ae_of_all _ (fun y => ENNReal.ofReal_lt_top))
      (fun y => g y)]
    calc
      (∫ y, ENNReal.toReal (ENNReal.ofReal (BGW.StableTrees.stableDensityAt θ s y)) •
          g y ∂volume) = ∫ y, BGW.StableTrees.stableDensityAt θ s y *
            BGW.StableTrees.stableDensityAt θ t ((-x) - y) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [show (-x) - y = -(x + y) by ring]
        simp [g, t, smul_eq_mul, ENNReal.toReal_ofReal
          (BGW.StableTrees.stableDensityAt_nonneg hθ hs y)]
      _ = BGW.StableTrees.stableDensityAt θ (s + t) (-x) := by
        exact BGW.StableTrees.integral_stableDensityAt_mul hθ hs ht (-x)
  calc
    _ = ENNReal.ofReal (∫ y, g y / p0
        ∂(BGW.StableTrees.stableLawAt θ s : Measure ℝ)) :=
      (ofReal_integral_eq_lintegral_ofReal hdivInt hdivAE).symm
    _ = ENNReal.ofReal ((∫ y, g y ∂(BGW.StableTrees.stableLawAt θ s : Measure ℝ)) / p0) := by
      rw [integral_div]
    _ = ENNReal.ofReal (BGW.StableTrees.stableDensityAt θ (1 - a) (-x) /
          BGW.StableTrees.Scalar.stableDensity θ 0) := by
      rw [hconv]
      congr 2
      simp [s, t]


private theorem bridgePrefix_consistent_lt {θ a b : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    {Pa : ProbabilityMeasure (BGW.Skorokhod.D a ℝ)}
    {Pb : ProbabilityMeasure (BGW.Skorokhod.D b ℝ)}
    (hPa : BGW.StableTrees.IsStableLevyLaw θ a Pa)
    (hPb : BGW.StableTrees.IsStableLevyLaw θ b Pb) :
    (BGW.StableTrees.bridgePrefixLaw θ b (ha.le.trans hab.le)
      (Pb : Measure (BGW.Skorokhod.D b ℝ))).map (BGW.Skorokhod.restrict hab.le) =
      BGW.StableTrees.bridgePrefixLaw θ a ha.le (Pa : Measure (BGW.Skorokhod.D a ℝ)) := by
  classical
  let r : BGW.Skorokhod.D b ℝ → BGW.Skorokhod.D a ℝ := BGW.Skorokhod.restrict hab.le
  let y : BGW.Skorokhod.D b ℝ → ℝ := bridgeIncrementPathP (le_of_lt ha) hab.le
  have hr : Measurable r := BGW.Skorokhod.measurable_restrict hab.le
  have hy : Measurable y := by
    change Measurable (fun f : BGW.Skorokhod.D b ℝ =>
      f ⟨b, le_trans (le_of_lt ha) hab.le, le_rfl⟩ - f ⟨a, le_of_lt ha, hab.le⟩)
    exact (measurable_eval _).sub (measurable_eval _)
  have hPathIndep := path_indep_incrementP ha hab hPb
  have hIndep : r ⟂ᵢ[(Pb : Measure (BGW.Skorokhod.D b ℝ))] y := by
    apply (IndepFun_iff_Indep r y (Pb : Measure (BGW.Skorokhod.D b ℝ))).2
    change Indep (MeasurableSpace.comap r inferInstance)
      (MeasurableSpace.comap y inferInstance) (Pb : Measure (BGW.Skorokhod.D b ℝ))
    exact hPathIndep
  have hPair : Measure.map (fun f => (r f, y f)) (Pb : Measure (BGW.Skorokhod.D b ℝ)) =
      (Measure.map r (Pb : Measure (BGW.Skorokhod.D b ℝ))).prod
        (Measure.map y (Pb : Measure (BGW.Skorokhod.D b ℝ)) : Measure ℝ) :=
    hIndep.map_prod_eq_prod_map_map hr.aemeasurable hy.aemeasurable
  have hrestrictLaw : Pb.map (BGW.Skorokhod.restrict hab.le) = Pa :=
    (hPa.unique hθ ha (hPb.map_restrict hθ ha hab.le)).symm
  have hrestrictMeasure : Measure.map r (Pb : Measure (BGW.Skorokhod.D b ℝ)) =
      (Pa : Measure (BGW.Skorokhod.D a ℝ)) := by
    rw [← ProbabilityMeasure.toMeasure_map]
    exact congrArg ProbabilityMeasure.toMeasure hrestrictLaw
  have hyLaw : Measure.map y (Pb : Measure (BGW.Skorokhod.D b ℝ)) =
      (BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ) := by
    exact map_prefix_incrementP ha hab hPb
  have hPairMeas : Measurable (fun f : BGW.Skorokhod.D b ℝ =>
      ((r f, y f) : BGW.Skorokhod.D a ℝ × ℝ)) := hr.prodMk hy
  apply Measure.ext
  intro A hA
  let evA : BGW.Skorokhod.D a ℝ → ℝ := fun f => f ⟨a, ha.le, le_rfl⟩
  let arg : BGW.Skorokhod.D a ℝ × ℝ → ℝ := fun z => -(evA z.1 + z.2)
  let q : BGW.Skorokhod.D a ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal
    (BGW.StableTrees.stableDensityAt θ (1 - b) (arg z) /
      BGW.StableTrees.Scalar.stableDensity θ 0)
  let g : BGW.Skorokhod.D a ℝ × ℝ → ℝ≥0∞ := fun z => if z.1 ∈ A then q z else 0
  have hpre : MeasurableSet (r ⁻¹' A) := hr hA
  have hevA : Measurable evA := measurable_eval _
  have harg : Measurable arg := by
    dsimp [arg]
    exact ((hevA.comp measurable_fst).add measurable_snd).neg
  have hnum : Measurable (fun z : BGW.Skorokhod.D a ℝ × ℝ =>
      BGW.StableTrees.stableDensityAt θ (1 - b) (arg z)) :=
    (BGW.StableTrees.stableDensityAt_continuous hθ).measurable.comp harg
  have hq : Measurable q := by
    exact ENNReal.measurable_ofReal.comp (hnum.div_const _)
  have hg : Measurable g := Measurable.ite ((measurable_fst :
      Measurable (fun z : BGW.Skorokhod.D a ℝ × ℝ => z.1)) hA) hq measurable_const
  have hweight (f : BGW.Skorokhod.D b ℝ) :
      q (r f, y f) = ENNReal.ofReal
        (BGW.StableTrees.bridgePrefixWeight θ b (ha.le.trans hab.le) f) := by
    apply congrArg ENNReal.ofReal
    change BGW.StableTrees.stableDensityAt θ (1 - b) (-(evA (r f) + y f)) /
        BGW.StableTrees.Scalar.stableDensity θ 0 =
      BGW.StableTrees.stableDensityAt θ (1 - b)
        (-f ⟨b, le_trans (le_of_lt ha) hab.le, le_rfl⟩) /
          BGW.StableTrees.Scalar.stableDensity θ 0
    have hev : evA (r f) = f ⟨a, le_of_lt ha, hab.le⟩ := rfl
    have hyval : y f = f ⟨b, le_trans (le_of_lt ha) hab.le, le_rfl⟩ -
        f ⟨a, le_of_lt ha, hab.le⟩ := rfl
    rw [hev, hyval]
    congr 1
    congr 1
    ring
  have hleft :
      ((BGW.StableTrees.bridgePrefixLaw θ b (ha.le.trans hab.le)
          (Pb : Measure (BGW.Skorokhod.D b ℝ))).map r) A =
        ∫⁻ z, g z ∂((Measure.map r (Pb : Measure (BGW.Skorokhod.D b ℝ))).prod
          (BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ)) := by
    rw [Measure.map_apply hr hA, BGW.StableTrees.bridgePrefixLaw,
      withDensity_apply _ hpre, ← lintegral_indicator hpre]
    calc
      ∫⁻ f, (r ⁻¹' A).indicator
          (fun f => ENNReal.ofReal
            (BGW.StableTrees.bridgePrefixWeight θ b (ha.le.trans hab.le) f)) f
          ∂(Pb : Measure (BGW.Skorokhod.D b ℝ)) =
        ∫⁻ f, g (r f, y f) ∂(Pb : Measure (BGW.Skorokhod.D b ℝ)) := by
          apply lintegral_congr
          intro f
          simp only [Set.indicator_apply, Set.mem_preimage]
          by_cases hf : r f ∈ A
          · simp only [ite_eq_left hf, g]
            exact (hweight f).symm
          · simp [hf, g]
      _ = ∫⁻ z, g z ∂Measure.map (fun f => (r f, y f))
          (Pb : Measure (BGW.Skorokhod.D b ℝ)) := (lintegral_map hg hPairMeas).symm
      _ = ∫⁻ z, g z ∂((Measure.map r (Pb : Measure (BGW.Skorokhod.D b ℝ))).prod
          (BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ)) := by
          rw [hPair, hrestrictMeasure, hyLaw]
  have hconv (x : BGW.Skorokhod.D a ℝ) :
      ∫⁻ z, g (x, z) ∂(BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ) =
      (if x ∈ A then ENNReal.ofReal
          (BGW.StableTrees.bridgePrefixWeight θ a ha.le x) else 0) := by
    by_cases hx : x ∈ A
    · simp only [g, ite_eq_left hx]
      simpa [q, arg, evA, BGW.StableTrees.bridgePrefixWeight] using
        (convolution_lintegralP (x := evA x) hθ ha hab hb)
    · simp [g, hx]
  have hright :
      BGW.StableTrees.bridgePrefixLaw θ a ha.le (Pa : Measure (BGW.Skorokhod.D a ℝ)) A =
        ∫⁻ x, A.indicator
          (fun f => ENNReal.ofReal
            (BGW.StableTrees.bridgePrefixWeight θ a ha.le f)) x
          ∂(Pa : Measure (BGW.Skorokhod.D a ℝ)) := by
    rw [BGW.StableTrees.bridgePrefixLaw, withDensity_apply _ hA,
      ← lintegral_indicator hA]
  calc
    _ = ∫⁻ x, ∫⁻ y, g (x, y)
        ∂(BGW.StableTrees.stableLawAt θ (b - a) : Measure ℝ)
        ∂(Measure.map r (Pb : Measure (BGW.Skorokhod.D b ℝ))) := by
          rw [hleft, lintegral_prod _ hg.aemeasurable]
    _ = ∫⁻ x, (if x ∈ A then ENNReal.ofReal
        (BGW.StableTrees.bridgePrefixWeight θ a ha.le x) else 0)
        ∂(Measure.map r (Pb : Measure (BGW.Skorokhod.D b ℝ))) := by
          apply lintegral_congr
          intro x
          exact hconv x
    _ = ∫⁻ x, A.indicator
        (fun f => ENNReal.ofReal (BGW.StableTrees.bridgePrefixWeight θ a ha.le f)) x
        ∂(Pa : Measure (BGW.Skorokhod.D a ℝ)) := by
          rw [hrestrictMeasure]
          apply lintegral_congr
          intro x
          by_cases hx : x ∈ A <;> simp [hx]
    _ = _ := hright.symm


/-- **Consistency at the level of measures on `D a ℝ`.** Restricting the tilted law at `b` gives
    the tilted law at `a`. -/
theorem bridgePrefix_consistent {θ a b : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) {Pa : ProbabilityMeasure (D a ℝ)} {Pb : ProbabilityMeasure (D b ℝ)}
    (hPa : IsStableLevyLaw θ a Pa) (hPb : IsStableLevyLaw θ b Pb) :
    (bridgePrefixLaw θ b (ha.le.trans hab) (Pb : Measure (D b ℝ))).map (restrict hab) =
      bridgePrefixLaw θ a ha.le (Pa : Measure (D a ℝ)) := by
  by_cases hEq : a = b
  · subst b
    have hlaw : Pb = Pa := hPb.unique hθ ha hPa
    rw [hlaw]
    have hre : BGW.Skorokhod.restrict (E := ℝ) (T := a) (a := a) hab =
        (id : D a ℝ → D a ℝ) := by
      funext f
      apply BGW.Skorokhod.ext
      intro t
      rfl
    rw [hre, Measure.map_id]
  · exact bridgePrefix_consistent_lt hθ ha (lt_of_le_of_ne hab hEq) hb hPa hPb

/-- Abstract-family form: the bridge prefix laws are probability measures and consistent. -/
theorem bridgePrefix_family {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (hP : ∀ a, 0 < a → IsStableLevyLaw θ a (P a)) :
    ∀ a b (ha : 0 < a) (hab : a ≤ b) (_hb : b < 1),
      IsProbabilityMeasure (bridgePrefixLaw θ a ha.le (P a : Measure (D a ℝ))) ∧
      (bridgePrefixLaw θ b (ha.le.trans hab) (P b : Measure (D b ℝ))).map (restrict hab) =
        bridgePrefixLaw θ a ha.le (P a : Measure (D a ℝ)) := by
  intro a b ha hab _hb
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have ha1 : a < 1 := lt_of_le_of_lt hab _hb
  exact ⟨isProbabilityMeasure_bridgePrefixLaw hθ ha ha1 (hP a ha),
    bridgePrefix_consistent hθ ha hab _hb (hP a ha) (hP b hbpos)⟩

end BGW.StableTrees
