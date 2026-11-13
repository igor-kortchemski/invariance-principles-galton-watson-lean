/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.MeasurableLaws
public import BGW.Skorokhod.MeasurableMaps
public import BGW.Skorokhod.Restrict
public import BGW.Skorokhod.Scaling
public import BGW.StableTrees.StableLaw
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Characterization of the stable Lévy law on Skorokhod space

Finite-dimensional increments characterize the law and are preserved under restriction and
stable scaling.

The predicate characterizes the spectrally positive θ-stable Lévy law only for `1 < θ ≤ 2` and
`0 < T`; outside that range `stableLaw` is a junk Dirac mass and the zero-path law satisfies it.

References: J. Bertoin, *Lévy Processes* (1996), ch. I and VII; K. Sato, *Lévy Processes and
Infinitely Divisible Distributions* (1999), §§11, 14.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod

/-- `P` is a law of a spectrally positive θ-stable Lévy process on `[0,T]`, expressed through
its finite-dimensional increments and its initial value. -/
structure IsStableLevyLaw (θ T : ℝ) (P : ProbabilityMeasure (D T ℝ)) : Prop where
  /-- The path starts at zero almost surely whenever the horizon is nonnegative. -/
  start : ∀ h : 0 ≤ T, ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), f ⟨0, le_rfl, h⟩ = 0
  /-- Increments along increasing times starting at zero have independent stable laws. -/
  increments : ∀ (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T),
    StrictMono t → (t 0 : ℝ) = 0 →
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))

private theorem map_pi_succ {k : ℕ} (μ : Fin (k + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    Measure.map (fun x : Fin (k + 1) → ℝ => fun i : Fin k => x i.succ) (Measure.pi μ) =
      Measure.pi (fun i : Fin k => μ i.succ) := by
  classical
  refine (Measure.pi_eq (μ := fun i : Fin k => μ i.succ)
    (μ' := Measure.map (fun x : Fin (k + 1) → ℝ => fun i : Fin k => x i.succ)
      (Measure.pi μ)) ?_).symm
  intro s hs
  rw [Measure.map_apply (Measurable.of_eval fun i => measurable_pi_apply i.succ)
    (MeasurableSet.univ_pi hs)]
  have hpre :
      (fun x : Fin (k + 1) → ℝ => fun i : Fin k => x i.succ) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (Fin.cases Set.univ s) := by
    ext x
    constructor
    · intro hx i
      cases i using Fin.cases with
      | zero => simp
      | succ i => exact hx i
    · intro hx i
      exact hx i.succ
  rw [hpre, Measure.pi_pi, Fin.prod_univ_succ]
  simp [IsProbabilityMeasure.measure_univ]

private theorem sum_range_sub_seq (g : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (g (j + 1) - g j)) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private def cumulative {n : ℕ} (x : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ j : Fin i.val, x ⟨j.val, by omega⟩

private theorem eval_eq_initial_add_cumulative {T : ℝ} {n : ℕ}
    (v : Fin (n + 1) → Set.Icc (0 : ℝ) T) (f : D T ℝ) (i : Fin (n + 1)) :
    f (v i) = f (v 0) + cumulative (fun j => f (v j.succ) - f (v j.castSucc)) i := by
  have hin : i.val ≤ n := by omega
  let g : ℕ → ℝ := fun j => f (v ⟨min j n, by omega⟩)
  let d : Fin n → ℝ := fun j => f (v j.succ) - f (v j.castSucc)
  have hsum :
      (∑ j ∈ Finset.range i.val, (g (j + 1) - g j)) = cumulative d i := by
    rw [← Fin.sum_univ_eq_sum_range]
    dsimp [cumulative, d]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j.val < n := by omega
    have hj1n : j.val + 1 ≤ n := by omega
    simp only [g, min_eq_left hjn.le, min_eq_left hj1n]
  have htel := sum_range_sub_seq g i.val
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

private theorem map_eval_finset_eq {θ T : ℝ} {P Q : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) (hQ : IsStableLevyLaw θ T Q) (hT : 0 ≤ T)
    (s : Finset (Set.Icc (0 : ℝ) T)) :
    Measure.map (fun f : D T ℝ => fun q : s => f q) (P : Measure (D T ℝ)) =
      Measure.map (fun f : D T ℝ => fun q : s => f q) (Q : Measure (D T ℝ)) := by
  classical
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  let r := insert z s
  have hrpos : 0 < r.card := Finset.card_pos.mpr ⟨z, Finset.mem_insert_self _ _⟩
  let n := r.card - 1
  have hn : n + 1 = r.card := by dsimp [n]; omega
  let e : Fin (n + 1) ≃o r := (Fin.castOrderIso hn).trans (r.orderIsoOfFin rfl)
  let v : Fin (n + 1) → Set.Icc (0 : ℝ) T := fun i => (e i).val
  let zr : r := ⟨z, Finset.mem_insert_self _ _⟩
  have hmin : e 0 ≤ zr := by
    have hle := e.monotone (Fin.zero_le (e.symm zr))
    simpa using hle
  have hv0 : v 0 = z := by
    apply Subtype.ext
    apply le_antisymm
    · change ((e 0).val : ℝ) ≤ (z : ℝ)
      exact_mod_cast hmin
    · exact (e 0).val.property.1
  have hv : StrictMono v := by
    intro i j hij
    change e i < e j
    exact e.strictMono hij
  have hv0' : (v 0 : ℝ) = 0 := by simpa [z] using congrArg Subtype.val hv0
  let inc : D T ℝ → (Fin n → ℝ) := fun f i => f (v i.succ) - f (v i.castSucc)
  let μ : Fin n → Measure ℝ := fun i =>
    stableLawAt θ ((v i.succ : ℝ) - v i.castSucc)
  let evalR : D T ℝ → (r → ℝ) := fun f q => f q.val
  let recon : (Fin n → ℝ) → (r → ℝ) := fun x q => cumulative x (e.symm q)
  have hinc : Measurable inc := Measurable.of_eval fun i =>
    (measurable_eval (v i.succ)).sub (measurable_eval (v i.castSucc))
  have hev : Measurable evalR := Measurable.of_eval fun q => measurable_eval q.val
  have hrec : Measurable recon := Measurable.of_eval fun q => by
    dsimp [recon, cumulative]
    fun_prop
  have hsourceP : Measure.map inc (P : Measure (D T ℝ)) = Measure.pi μ :=
    hP.increments n v hv hv0'
  have hsourceQ : Measure.map inc (Q : Measure (D T ℝ)) = Measure.pi μ :=
    hQ.increments n v hv hv0'
  have hEvalP : Measure.map evalR (P : Measure (D T ℝ)) =
      Measure.map recon (Measure.pi μ) := by
    have hstart : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), f z = 0 := by
      simpa [z] using hP.start hT
    have hae : evalR =ᵐ[(P : Measure (D T ℝ))] recon ∘ inc := by
      filter_upwards [hstart] with f hf
      funext q
      have htime : v (e.symm q) = q.val := by
        change (e (e.symm q)).val = q.val
        rw [e.apply_symm_apply]
      have heval := eval_eq_initial_add_cumulative v f (e.symm q)
      have hzero : f (v 0) = 0 := by rw [hv0]; exact hf
      rw [htime, hzero, zero_add] at heval
      simpa [evalR, recon, inc] using heval
    calc
      Measure.map evalR (P : Measure (D T ℝ)) = Measure.map (recon ∘ inc) P :=
        Measure.map_congr hae
      _ = Measure.map recon (Measure.map inc (P : Measure (D T ℝ)) ) :=
        (Measure.map_map hrec hinc).symm
      _ = Measure.map recon (Measure.pi μ) := by rw [hsourceP]
  have hEvalQ : Measure.map evalR (Q : Measure (D T ℝ)) =
      Measure.map recon (Measure.pi μ) := by
    have hstart : ∀ᵐ f : D T ℝ ∂(Q : Measure (D T ℝ)), f z = 0 := by
      simpa [z] using hQ.start hT
    have hae : evalR =ᵐ[(Q : Measure (D T ℝ))] recon ∘ inc := by
      filter_upwards [hstart] with f hf
      funext q
      have htime : v (e.symm q) = q.val := by
        change (e (e.symm q)).val = q.val
        rw [e.apply_symm_apply]
      have heval := eval_eq_initial_add_cumulative v f (e.symm q)
      have hzero : f (v 0) = 0 := by rw [hv0]; exact hf
      rw [htime, hzero, zero_add] at heval
      simpa [evalR, recon, inc] using heval
    calc
      Measure.map evalR (Q : Measure (D T ℝ)) = Measure.map (recon ∘ inc) Q :=
        Measure.map_congr hae
      _ = Measure.map recon (Measure.map inc (Q : Measure (D T ℝ))) :=
        (Measure.map_map hrec hinc).symm
      _ = Measure.map recon (Measure.pi μ) := by rw [hsourceQ]
  have hEval : Measure.map evalR (P : Measure (D T ℝ)) =
      Measure.map evalR (Q : Measure (D T ℝ)) := hEvalP.trans hEvalQ.symm
  let proj : (r → ℝ) → (s → ℝ) := fun g q => g ⟨q.val, Finset.mem_insert_of_mem q.property⟩
  let evalS : D T ℝ → (s → ℝ) := fun f q => f q.val
  have hproj : Measurable proj := Measurable.of_eval fun q =>
    measurable_pi_apply
      (⟨q.val, Finset.mem_insert_of_mem q.property⟩ : r)
  have hcompP : Measure.map evalS (P : Measure (D T ℝ)) =
      Measure.map proj (Measure.map evalR (P : Measure (D T ℝ))) := by
    rw [show evalS = proj ∘ evalR by funext f q; rfl,
      ← Measure.map_map hproj hev]
  have hcompQ : Measure.map evalS (Q : Measure (D T ℝ)) =
      Measure.map proj (Measure.map evalR (Q : Measure (D T ℝ))) := by
    rw [show evalS = proj ∘ evalR by funext f q; rfl,
      ← Measure.map_map hproj hev]
  rw [hcompP, hcompQ, hEval]

/-- Uniqueness of the stable Lévy law on a positive horizon. -/
theorem IsStableLevyLaw.unique {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P Q : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P)
    (hQ : IsStableLevyLaw θ T Q) : P = Q := by
  -- The index-range binder is retained from the source-facing statement; finite-dimensional
  -- uniqueness itself applies to the laws specified by the same increment family.
  have _hθ := hθ
  apply BGW.Skorokhod.ext_of_finiteDimensional (S := Set.univ) dense_univ hT.le (by simp)
  intro s hs
  apply ProbabilityMeasure.toMeasure_injective
  exact map_eval_finset_eq hP hQ hT.le s

/-- Increments along any strictly increasing finite family of times are independent with stable
laws, whether or not the first time is zero. -/
theorem IsStableLevyLaw.map_increments {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T)
    (ht : StrictMono t) :
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ)) := by
  classical
  by_cases hzero : (t 0 : ℝ) = 0
  · exact hP.increments k t ht hzero
  · have hpos0 : 0 < (t 0 : ℝ) := by
      exact lt_of_le_of_ne (t 0).property.1 (Ne.symm hzero)
    have hpos (i : Fin (k + 1)) : 0 < (t i : ℝ) := by
      have hle : t 0 ≤ t i := ht.monotone (Fin.zero_le i)
      exact lt_of_lt_of_le hpos0 (by simpa using hle)
    let u : Fin (k + 2) → Set.Icc (0 : ℝ) T :=
      Fin.cases ⟨0, le_rfl, (t 0).property.1.trans (t 0).property.2⟩ t
    have hu : StrictMono u := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (lt_irrefl _ hij).elim
        | succ j =>
          change (0 : ℝ) < (t j : ℝ)
          exact hpos j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
        | succ j =>
          have hij' : i < j := Fin.succ_lt_succ_iff.mp hij
          exact_mod_cast ht hij'
    have hu0 : (u 0 : ℝ) = 0 := by simp [u]
    let inc : D T ℝ → (Fin (k + 1) → ℝ) := fun f i =>
      f (u i.succ) - f (u i.castSucc)
    let tail : (Fin (k + 1) → ℝ) → (Fin k → ℝ) := fun x i => x i.succ
    let μ : Fin (k + 1) → Measure ℝ := fun i =>
      stableLawAt θ ((u i.succ : ℝ) - u i.castSucc)
    have hinc : Measurable inc := Measurable.of_eval fun i =>
      (measurable_eval (u i.succ)).sub (measurable_eval (u i.castSucc))
    have htail : Measurable tail := Measurable.of_eval fun i => measurable_pi_apply i.succ
    have hsource : Measure.map inc (P : Measure (D T ℝ)) = Measure.pi μ := by
      exact hP.increments (k + 1) u hu hu0
    have htailLaw : Measure.map tail (Measure.pi μ) = Measure.pi (fun i => μ i.succ) :=
      map_pi_succ μ
    have htarget :
        (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc)) = tail ∘ inc := by
      funext f i
      simp [tail, inc, u, Fin.cases]
    rw [htarget, ← Measure.map_map htail hinc, hsource, htailLaw]
    congr 1

private theorem map_increment_pair {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) (a b : Set.Icc (0 : ℝ) T) (hab : a < b) :
    Measure.map (fun f : D T ℝ => f b - f a) (P : Measure (D T ℝ)) =
      (stableLawAt θ ((b : ℝ) - a) : Measure ℝ) := by
  classical
  let v : Fin 2 → Set.Icc (0 : ℝ) T := fun i => if i.val = 0 then a else b
  have hv : StrictMono v := by
    intro i j hij
    have hij' : i.val < j.val := Fin.lt_def.mp hij
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · omega
    · have hi0 : i = 0 := Fin.ext hi
      have hj1 : j = 1 := Fin.ext hj
      simpa [v, hi0, hj1] using hab
    · omega
    · omega
  let inc : D T ℝ → (Fin 1 → ℝ) := fun f i => f (v i.succ) - f (v i.castSucc)
  let coord : (Fin 1 → ℝ) → ℝ := fun x => x ⟨0, by omega⟩
  have hinc : Measurable inc := Measurable.of_eval fun i =>
    (measurable_eval (v i.succ)).sub (measurable_eval (v i.castSucc))
  have hcoord : Measurable coord := measurable_pi_apply _
  have hlaw := hP.map_increments 1 v hv
  have hcoordlaw : Measure.map coord (Measure.pi fun i : Fin 1 =>
      (stableLawAt θ ((v i.succ : ℝ) - v i.castSucc) : Measure ℝ)) =
      (stableLawAt θ ((b : ℝ) - a) : Measure ℝ) := by
    rw [show coord = Function.eval (⟨0, by omega⟩ : Fin 1) from rfl,
      Measure.pi_map_eval]
    simp [v]
  have hcomp : (fun f : D T ℝ => f b - f a) = coord ∘ inc := by
    funext f
    simp [coord, inc, v]
  rw [hcomp, ← Measure.map_map hcoord hinc, hlaw, hcoordlaw]

private theorem scaledStableLaw_tendstoInMeasure {θ : ℝ} (hθ : 0 < θ)
    {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0)) :
    TendstoInMeasure (stableLaw θ : Measure ℝ)
      (fun n x => d n ^ (1 / θ) * x) atTop (fun _ => 0) := by
  have hscale : Tendsto (fun n => d n ^ (1 / θ)) atTop (𝓝 0) :=
    hd.rpow_const_nhds_zero (by positivity)
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (measurable_const.mul measurable_id).aestronglyMeasurable
  · filter_upwards [] with x
    simpa using hscale.mul_const x

private theorem continuousAt_of_leftLim_eq {T : ℝ} (f : D T ℝ)
    (t : Set.Icc (0 : ℝ) T) (hleft : Function.leftLim f t = f t) : ContinuousAt f t := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · change Tendsto f (𝓝[<] t) (𝓝 (f t))
    simpa [hleft] using (isCadlag f).tendsto_nhdsLT_leftLim t
  · exact (isCadlag f).isRightContinuous t

/-- P3: the stable Lévy law is almost surely continuous at each fixed time, including `T`.
The quantifier over the time is outside `∀ᵐ`. -/
theorem IsStableLevyLaw.ae_continuousAt {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) (t : Set.Icc (0 : ℝ) T) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ContinuousAt f t := by
  have _hT := hT
  by_cases ht0 : (t : ℝ) = 0
  · have htbot : IsBot t := by
      intro s
      change (t : ℝ) ≤ (s : ℝ)
      simpa [ht0] using s.property.1
    have hleft (f : D T ℝ) : Function.leftLim f t = f t :=
      leftLim_eq_of_isBot htbot
    exact Eventually.of_forall fun f => continuousAt_of_leftLim_eq f t (hleft f)
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
    let d : ℕ → ℝ := fun n => (t : ℝ) / (n + 1)
    have hdpos (n : ℕ) : 0 < d n := by
      dsimp [d]
      positivity
    let s : ℕ → Set.Icc (0 : ℝ) T := fun n =>
      ⟨(t : ℝ) - d n, by
        constructor
        · have hden : 1 ≤ (n + 1 : ℝ) := by norm_cast; omega
          have hdle : d n ≤ (t : ℝ) := by
            dsimp [d]
            exact div_le_self t.property.1 hden
          linarith
        · exact (sub_le_self _ (hdpos n).le).trans t.property.2⟩
    have hd : Tendsto d atTop (𝓝 0) := by
      simpa [d, div_eq_mul_inv, mul_comm] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (t : ℝ)
    have hslt (n : ℕ) : s n < t := by
      apply Subtype.coe_lt_coe.mpr
      change (t : ℝ) - d n < (t : ℝ)
      exact sub_lt_self _ (hdpos n)
    have hsval : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (t : ℝ)) := by
      have hconst : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (𝓝 (t : ℝ)) := tendsto_const_nhds
      have h : Tendsto (fun n => (t : ℝ) - d n) atTop (𝓝 ((t : ℝ) - 0)) := hconst.sub hd
      simpa [s, d] using h
    have hsLim : Tendsto s atTop (𝓝 t) := tendsto_subtype_rng.mpr hsval
    have hsWithin : Tendsto s atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hsLim, Eventually.of_forall hslt⟩
    have hleftSeq (f : D T ℝ) :
        Tendsto (fun n => f (s n)) atTop (𝓝 (Function.leftLim f t)) :=
      ((isCadlag f).tendsto_nhdsLT_leftLim t).comp hsWithin
    let X : ℕ → D T ℝ → ℝ := fun n f => f t - f (s n)
    have hXmeas (n : ℕ) : Measurable (X n) :=
      (measurable_eval t).sub (measurable_eval (s n))
    have hXjump : ∀ f : D T ℝ, Tendsto (fun n => X n f) atTop
        (𝓝 (f t - Function.leftLim f t)) := by
      intro f
      exact tendsto_const_nhds.sub (hleftSeq f)
    have hbase := scaledStableLaw_tendstoInMeasure (θ := θ) (by linarith [hθ.1]) hd
    have hmap (n : ℕ) : Measure.map (X n) (P : Measure (D T ℝ)) =
        Measure.map (fun x : ℝ => d n ^ (1 / θ) * x) (stableLaw θ : Measure ℝ) := by
      have hgap : (t : ℝ) - s n = d n := by
        simp [s, d]
      simpa [X, hgap, stableLawAt, ProbabilityMeasure.toMeasure_map] using
        (map_increment_pair hP (s n) t (hslt n))
    have hXzero : TendstoInMeasure (P : Measure (D T ℝ)) X atTop (fun _ => 0) := by
      intro ε hε
      have hA : MeasurableSet {x : ℝ | ε ≤ edist x 0} :=
        measurableSet_Ici.preimage (measurable_id.edist measurable_const)
      have hEq (n : ℕ) :
          (P : Measure (D T ℝ)) {f | ε ≤ edist (X n f) 0} =
            (stableLaw θ : Measure ℝ) {x | ε ≤ edist (d n ^ (1 / θ) * x) 0} := by
        calc
          (P : Measure (D T ℝ)) {f | ε ≤ edist (X n f) 0} =
              (Measure.map (X n) (P : Measure (D T ℝ))) {x | ε ≤ edist x 0} := by
                rw [Measure.map_apply (hXmeas n) hA]
                rfl
          _ = (Measure.map (fun x : ℝ => d n ^ (1 / θ) * x)
                (stableLaw θ : Measure ℝ)) {x | ε ≤ edist x 0} := by rw [hmap n]
          _ = (stableLaw θ : Measure ℝ) {x | ε ≤ edist (d n ^ (1 / θ) * x) 0} := by
                rw [Measure.map_apply (by fun_prop) hA]
                rfl
      refine (hbase ε hε).congr' ?_
      exact Eventually.of_forall fun n => (hEq n).symm
    have hXlim : TendstoInMeasure (P : Measure (D T ℝ)) X atTop
        (fun f => f t - Function.leftLim f t) :=
      tendstoInMeasure_of_tendsto_ae (fun n => (hXmeas n).aestronglyMeasurable)
        (Eventually.of_forall hXjump)
    have hjump : (fun _ : D T ℝ => (0 : ℝ)) =ᵐ[(P : Measure (D T ℝ))]
        fun f => f t - Function.leftLim f t := tendstoInMeasure_ae_unique hXzero hXlim
    have hleft : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
        Function.leftLim f t = f t := by
      filter_upwards [hjump] with f hf
      linarith
    filter_upwards [hleft] with f hf
    exact continuousAt_of_leftLim_eq f t hf

/-- Restriction to a shorter horizon is measurable for the Borel structures. -/
theorem measurable_restrict {T a : ℝ} (haT : a ≤ T) :
    Measurable (restrict (E := ℝ) haT) :=
  BGW.Skorokhod.measurable_restrict haT

/-- The restriction of a stable Lévy law to a positive subhorizon is a stable Lévy law. -/
theorem IsStableLevyLaw.map_restrict {θ T a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (haT : a ≤ T) {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) :
    IsStableLevyLaw θ a (P.map (restrict haT)) := by
  -- The parameter range is retained from the source-facing P1 statement; restriction needs no
  -- additional index-specific estimate.
  have _hθ := hθ
  refine ⟨?_, ?_⟩
  · intro hT
    let z : Set.Icc (0 : ℝ) a := ⟨0, le_rfl, ha.le⟩
    have heval : Measurable (fun f : D a ℝ => f z) := measurable_eval z
    have hs : MeasurableSet {f : D a ℝ | f z = 0} :=
      heval (measurableSet_singleton 0)
    change ∀ᵐ f : D a ℝ ∂((P : Measure (D T ℝ)).map (restrict haT)), f z = 0
    rw [ae_map_iff (measurable_restrict haT).aemeasurable hs]
    simpa only [BGW.Skorokhod.restrict, coe_mk, z] using hP.start (le_trans hT haT)
  · intro k t ht ht0
    let u : Fin (k + 1) → Set.Icc (0 : ℝ) T := fun i =>
      ⟨(t i : ℝ), (t i).property.1, (t i).property.2.trans haT⟩
    have hu : StrictMono u := by
      intro i j hij
      exact_mod_cast ht hij
    have hu0 : (u 0 : ℝ) = 0 := ht0
    have hinc := hP.increments k u hu hu0
    have hmeas : Measurable (fun f : D a ℝ =>
        fun i : Fin k => f (t i.succ) - f (t i.castSucc)) :=
      Measurable.of_eval fun i =>
        (measurable_eval (t i.succ)).sub (measurable_eval (t i.castSucc))
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hmeas (measurable_restrict haT)]
    have hcomp :
        (fun f : D a ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc)) ∘
          BGW.Skorokhod.restrict haT =
        (fun f : D T ℝ => fun i : Fin k => f (u i.succ) - f (u i.castSucc)) := by
      funext f i
      rfl
    rw [hcomp]
    simpa only [u] using hinc

/-- For fixed positive horizons, time–space scaling is Borel measurable. -/
theorem measurable_timeSpaceScale_fixed {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (k : ℝ) :
    Measurable (fun f : D (c * T) ℝ =>
      timeSpaceScale T (mul_pos hc hT).le
        (f, k, (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ)))) :=
  BGW.Skorokhod.measurable_timeSpaceScale_fixed hT hc k

private theorem stableLawAt_timeScale {θ c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Measure.map (fun x : ℝ => c ^ (-(1 / θ)) * x) (stableLawAt θ (c * d) : Measure ℝ) =
      (stableLawAt θ d : Measure ℝ) := by
  let r : ℝ := 1 / θ
  have hpow : c ^ (-r) * (c * d) ^ r = d ^ r := by
    rw [Real.mul_rpow hc.le hd.le, Real.rpow_neg hc.le]
    have hcPow : c ^ r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hc r)
    rw [← mul_assoc, inv_mul_cancel₀ hcPow, one_mul]
  simp only [stableLawAt, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  have hcoeff : c ^ (-(1 / θ)) * (c * d) ^ (1 / θ) = d ^ (1 / θ) := by
    simpa [r] using hpow
  rw [← mul_assoc, hcoeff]

/-- The stable Lévy law rescales to the original horizon after inverse stable space scaling. -/
theorem IsStableLevyLaw.map_timeSpaceScale {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {c : ℝ} (hc : 0 < c) {P : ProbabilityMeasure (D (c * T) ℝ)}
    (hP : IsStableLevyLaw θ (c * T) P) :
    IsStableLevyLaw θ T
      (P.map (fun f : D (c * T) ℝ =>
        timeSpaceScale T (mul_pos hc hT).le
          (f, c ^ (-(1 / θ)), (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ))))) := by
  -- The index range is retained from the source-facing P2 statement; scaling itself only uses
  -- the time-stability identity, which holds for every real θ in this representation.
  have _hθ := hθ
  let scaleFactor : ℝ := c ^ (-(1 / θ))
  let scale : D (c * T) ℝ → D T ℝ := fun f =>
    timeSpaceScale T (mul_pos hc hT).le
      (f, scaleFactor, (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ)))
  refine ⟨?_, ?_⟩
  · intro hT0
    let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT0⟩
    have heval : Measurable (fun f : D T ℝ => f z) := measurable_eval z
    have hs : MeasurableSet {f : D T ℝ | f z = 0} := heval (measurableSet_singleton 0)
    change ∀ᵐ f : D T ℝ ∂((P : Measure (D (c * T) ℝ)).map scale), f z = 0
    rw [ae_map_iff (measurable_timeSpaceScale_fixed hT hc scaleFactor).aemeasurable hs]
    have hstart := hP.start (mul_pos hc hT).le
    filter_upwards [hstart] with f hf
    have hz : (⟨min (c * (0 : ℝ)) (c * T),
        le_min (mul_nonneg hc.le (by norm_num)) (mul_nonneg hc.le hT.le),
        min_le_right _ _⟩ : Set.Icc (0 : ℝ) (c * T)) =
        ⟨0, le_rfl, mul_nonneg hc.le hT.le⟩ := by
      apply Subtype.ext
      simp [min_eq_left (mul_nonneg hc.le hT.le)]
    change scaleFactor * f ⟨min (c * (0 : ℝ)) (c * T),
      le_min (mul_nonneg hc.le (by norm_num)) (mul_nonneg hc.le hT.le),
      min_le_right _ _⟩ = 0
    rw [hz, hf, mul_zero]
  · intro k t ht ht0
    let u : Fin (k + 1) → Set.Icc (0 : ℝ) (c * T) := fun i =>
      ⟨c * (t i : ℝ), mul_nonneg hc.le (t i).property.1,
        mul_le_mul_of_nonneg_left (t i).property.2 hc.le⟩
    have hu : StrictMono u := by
      intro i j hij
      change c * (t i : ℝ) < c * (t j : ℝ)
      exact mul_lt_mul_of_pos_left (by exact_mod_cast ht hij) hc
    have hu0 : (u 0 : ℝ) = 0 := by simp [u, ht0]
    have hsource := hP.map_increments k u hu
    have hscale := measurable_timeSpaceScale_fixed hT hc scaleFactor
    have hinc : Measurable (fun f : D T ℝ =>
        fun i : Fin k => f (t i.succ) - f (t i.castSucc)) :=
      Measurable.of_eval fun i =>
        (measurable_eval (t i.succ)).sub (measurable_eval (t i.castSucc))
    let incSource : D (c * T) ℝ → (Fin k → ℝ) := fun f i =>
      f (u i.succ) - f (u i.castSucc)
    let scaleCoords : (Fin k → ℝ) → (Fin k → ℝ) := fun x i => scaleFactor * x i
    have hincSource : Measurable incSource := Measurable.of_eval fun i =>
      (measurable_eval (u i.succ)).sub (measurable_eval (u i.castSucc))
    have hcoords : Measurable scaleCoords := Measurable.of_eval fun i =>
      measurable_const.mul (measurable_pi_apply i)
    have hcomp :
        (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc)) ∘ scale =
          scaleCoords ∘ incSource := by
      funext f i
      have hs₁ : c * (t i.succ : ℝ) ≤ c * T :=
        mul_le_mul_of_nonneg_left (t i.succ).property.2 hc.le
      have hs₀ : c * (t i.castSucc : ℝ) ≤ c * T :=
        mul_le_mul_of_nonneg_left (t i.castSucc).property.2 hc.le
      simp [scaleCoords, incSource, scale, scaleFactor, timeSpaceScale, u,
        min_eq_left hs₁, min_eq_left hs₀]
      ring
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hinc hscale, hcomp,
      ← Measure.map_map hcoords hincSource, hsource,
      Measure.pi_map_pi (fun i => (measurable_const_mul scaleFactor).aemeasurable)]
    apply congrArg Measure.pi
    funext i
    have htime : (u i.succ : ℝ) - u i.castSucc =
        c * ((t i.succ : ℝ) - t i.castSucc) := by
      simp [u]
      ring
    have hd : 0 < (t i.succ : ℝ) - t i.castSucc :=
      sub_pos.mpr (by exact_mod_cast ht Fin.castSucc_lt_succ)
    rw [htime]
    simpa [scaleFactor] using stableLawAt_timeScale (θ := θ) hc hd

end BGW.StableTrees
