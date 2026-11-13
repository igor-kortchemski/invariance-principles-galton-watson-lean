module

public import BGWLeaves.StableAnalysis.Defs
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis.SizeTail

open BGW.StableTrees
open BGW.LocallyFinite (bienaymeLaw sizeEvent FiniteVertices Present)

private theorem powerBlock_integral_bounds {ρ : ℝ} (hρ : 0 < ρ)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) ≤
        ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ∧
      ∑ q ∈ Finset.Ico n (2 * n), ((q + 1 : ℕ) : ℝ) ^ (-1 - ρ) ≤
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : n ≤ 2 * n := by omega
  have hant : AntitoneOn (fun x : ℝ => x ^ (-1 - ρ)) (Set.Icc (n : ℝ) (2 * n : ℕ)) := by
    intro x hx y hy hxy
    apply Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hnR hx.1) hxy
    linarith
  have hint : IntegrableOn (fun x : ℝ => x ^ (-1 - ρ)) (Set.Icc (n : ℝ) (2 * n : ℕ)) :=
    hant.integrableOn_isCompact isCompact_Icc
  constructor
  · exact hant.integral_le_sum_Ico h2n
  · exact hant.sum_le_integral_Ico h2n

private theorem powerBlock_sum_bounds {ρ : ℝ} (hρ : 0 < ρ)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) ≤
        ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ∧
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ≤
        (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) + (n : ℝ) ^ (-1 - ρ) := by
  have h2n : n ≤ 2 * n := by omega
  obtain ⟨hleft, hright⟩ := powerBlock_integral_bounds hρ hn
  let g : ℕ → ℝ := fun q => (q : ℝ) ^ (-1 - ρ)
  have htel : (∑ q ∈ Finset.Ico n (2 * n), (g (q + 1) - g q)) =
      g (2 * n) - g n := by
    rw [Finset.sum_Ico_eq_sub _ h2n, Finset.sum_range_sub, Finset.sum_range_sub]
    simp [g]
  have hshift : (∑ q ∈ Finset.Ico n (2 * n), g (q + 1)) -
      (∑ q ∈ Finset.Ico n (2 * n), g q) = g (2 * n) - g n := by
    calc _ = ∑ q ∈ Finset.Ico n (2 * n), (g (q + 1) - g q) := by rw [Finset.sum_sub_distrib]
      _ = _ := htel
  have hsum : (∑ q ∈ Finset.Ico n (2 * n), g q) =
      (∑ q ∈ Finset.Ico n (2 * n), g (q + 1)) + g n - g (2 * n) := by
    linarith
  have hnonneg : 0 ≤ g (2 * n) := by positivity
  constructor
  · simpa [g] using hleft
  · have hr : (∑ q ∈ Finset.Ico n (2 * n), g (q + 1)) ≤
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by
      simpa [g] using hright
    rw [hsum]
    linarith

private theorem powerBlock_sum_tendsto {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ)) atTop
      (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
  let c : ℝ := (1 - (2 : ℝ) ^ (-ρ)) / ρ
  have hlo : ∀ n : ℕ, 1 ≤ n → c ≤ (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn2n : (n : ℝ) ≤ 2 * n := by nlinarith
    have hnot0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (2 * n : ℝ) := by
      rw [Set.uIcc_of_le hn2n]
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inl (by linarith)
    have hInt := integral_rpow (a := (n : ℝ)) (b := (2 * n : ℝ))
      (r := -1 - ρ) (Or.inr ⟨by linarith, hnot0⟩)
    have hInt' : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        (n : ℝ) ^ (-ρ) * c := by
      rw [hInt, show -1 - ρ + 1 = -ρ by ring,
        Real.mul_rpow (by norm_num) hnR.le]
      dsimp [c]
      ring
    have hmul : (n : ℝ) ^ ρ * (n : ℝ) ^ (-ρ) = 1 := by
      rw [← Real.rpow_add hnR, show ρ + -ρ = 0 by ring, Real.rpow_zero]
    have hScaled : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) = c := by
      rw [hInt', ← mul_assoc, hmul, one_mul]
    have hEndpoints : ((2 * n : ℕ) : ℝ) = (2 : ℝ) * n := by norm_cast
    have hIntEq : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by rw [hEndpoints]
    have hScaledNat : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) = c := by
      rw [← hIntEq, hScaled]
    have hB := powerBlock_sum_bounds hρ hn
    have hmulnonneg : 0 ≤ (n : ℝ) ^ ρ := Real.rpow_nonneg (by positivity) _
    calc c = (n : ℝ) ^ ρ *
          (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) := hScaledNat.symm
      _ ≤ (n : ℝ) ^ ρ * ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) :=
        mul_le_mul_of_nonneg_left hB.1 hmulnonneg
  have hup : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ≤ c + 1 / n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn2n : (n : ℝ) ≤ 2 * n := by nlinarith
    have hnot0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (2 * n : ℝ) := by
      rw [Set.uIcc_of_le hn2n]
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inl (by linarith)
    have hInt := integral_rpow (a := (n : ℝ)) (b := (2 * n : ℝ))
      (r := -1 - ρ) (Or.inr ⟨by linarith, hnot0⟩)
    have hInt' : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        (n : ℝ) ^ (-ρ) * c := by
      rw [hInt, show -1 - ρ + 1 = -ρ by ring,
        Real.mul_rpow (by norm_num) hnR.le]
      dsimp [c]
      ring
    have hmul : (n : ℝ) ^ ρ * (n : ℝ) ^ (-ρ) = 1 := by
      rw [← Real.rpow_add hnR, show ρ + -ρ = 0 by ring, Real.rpow_zero]
    have herr : (n : ℝ) ^ ρ * (n : ℝ) ^ (-1 - ρ) = 1 / n := by
      rw [← Real.rpow_add hnR, show ρ + (-1 - ρ) = -1 by ring,
        Real.rpow_neg hnR.le, Real.rpow_one]
      simp
    have hScaled : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) = c := by
      rw [hInt', ← mul_assoc, hmul, one_mul]
    have hEndpoints : ((2 * n : ℕ) : ℝ) = (2 : ℝ) * n := by norm_cast
    have hIntEq : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by rw [hEndpoints]
    have hScaledNat : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) = c := by
      rw [← hIntEq, hScaled]
    have hB := powerBlock_sum_bounds hρ hn
    have hmulnonneg : 0 ≤ (n : ℝ) ^ ρ := Real.rpow_nonneg (by positivity) _
    calc (n : ℝ) ^ ρ * ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ)
        ≤ (n : ℝ) ^ ρ *
          ((∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) + (n : ℝ) ^ (-1 - ρ)) :=
          mul_le_mul_of_nonneg_left hB.2 hmulnonneg
      _ = c + 1 / n := by rw [mul_add, hScaledNat, herr]
  have hlow : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hlo n hn
  have hhigh : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ≤ c + 1 / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hup n hn
  have hupper : Tendsto (fun n : ℕ => c + 1 / (n : ℝ)) atTop (𝓝 c) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have h := hconst.add hzero
    simpa using h
  simpa [c] using
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hlow hhigh)

private theorem powerTerm_cancel {ρ : ℝ} {n q : ℕ} (hn : 0 < n) (hq : 0 < q) :
    (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) *
      ((q : ℝ) * ((q : ℝ) / n) ^ ρ) = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.div_rpow hqR.le hnR.le, show -1 - ρ = -1 + -ρ by ring,
    Real.rpow_add hqR, Real.rpow_neg hqR.le, Real.rpow_one]
  field_simp
  rw [← Real.rpow_add hqR, show -ρ + ρ = 0 by ring, Real.rpow_zero]

private theorem inverseBlock_tendsto {ρ : ℝ} {a : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    Tendsto (fun n : ℕ => a n *
      ∑ q ∈ Finset.Ico n (2 * n), 1 / ((q : ℝ) * a q)) atTop
      (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
  let P : ℕ → ℝ := fun n =>
    ∑ q ∈ Finset.Ico n (2 * n), (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)
  let B : ℕ → ℝ := fun n =>
    a n * ∑ q ∈ Finset.Ico n (2 * n), 1 / ((q : ℝ) * a q)
  let R : ℕ → ℝ := fun n => B n / P n
  have hP : Tendsto P atTop (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
    have h := powerBlock_sum_tendsto hρ
    simpa [P, Finset.mul_sum] using h
  have hPpos : ∀ n : ℕ, 1 ≤ n → 0 < P n := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hsum : 0 < ∑ q ∈ Finset.Ico n (2 * n),
        (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) := by
      apply Finset.sum_pos'
      · intro q hq
        have hqmem := Finset.mem_Ico.mp hq
        have hqpos : 0 < q := by omega
        positivity
      · refine ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩
        have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
        have hpow : 0 < (n : ℝ) ^ ρ := Real.rpow_pos_of_pos hnR _
        have hterm : 0 < (n : ℝ) ^ (-1 - ρ) := Real.rpow_pos_of_pos hnR _
        exact mul_pos hpow hterm
    dsimp [P]
    exact hsum
  have hR : Tendsto R atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := min (ε / 4) (1 / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ1 : δ < 1 := by dsimp [δ]; have := min_le_right (ε / 4) (1 / 2); linarith
    have hδsmall : 2 * δ < ε := by
      dsimp [δ]
      have := min_le_left (ε / 4) (1 / 2)
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hrv.eventually_ratio_bounds hmono hpos hρ.le hδ)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have haN : 0 < a n := hpos n hn1
    have hpN : 0 < P n := hPpos n hn1
    have hloc := hN n hnN
    have hlowBlock : (1 / (1 + δ)) * P n ≤ B n := by
      dsimp [P, B]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hqn : n ≤ q := (Finset.mem_Ico.mp hq).1
      have hq2 : q ≤ 2 * n := (Finset.mem_Ico.mp hq).2.le
      have hqpos : 0 < q := by omega
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
      have haq : 0 < a q := hpos q (by omega)
      have hx : 0 < ((q : ℝ) / n) ^ ρ := by positivity
      obtain ⟨hUpper, _⟩ := hloc q hqn hq2
      have hcancel := powerTerm_cancel (ρ := ρ) hnpos hqpos
      have hden : 0 < 1 + δ := by linarith
      have hkernel : 0 < (q : ℝ) * a q := mul_pos hqR haq
      have hdiv : ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) / (1 + δ) ≤
          a n / ((q : ℝ) * a q) := by
        rw [div_le_div_iff₀ hden hkernel]
        calc (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * ((q : ℝ) * a q)
            = ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) * (q * a q) := by ring
        _ ≤ ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) *
            (q * ((1 + δ) * ((q : ℝ) / n) ^ ρ * a n)) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUpper hqR.le)
                (by positivity)
        _ = a n * (1 + δ) := by
              calc _ = (1 + δ) * a n * ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) *
                  (q * ((q : ℝ) / n) ^ ρ)) := by ring
                _ = (1 + δ) * a n := by rw [hcancel]; ring
                _ = a n * (1 + δ) := by ring
      simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv
    have hhighBlock : B n ≤ (1 / (1 - δ)) * P n := by
      dsimp [P, B]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hqn : n ≤ q := (Finset.mem_Ico.mp hq).1
      have hq2 : q ≤ 2 * n := (Finset.mem_Ico.mp hq).2.le
      have hqpos : 0 < q := by omega
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
      have haq : 0 < a q := hpos q (by omega)
      have hx : 0 < ((q : ℝ) / n) ^ ρ := by positivity
      obtain ⟨_, hLower⟩ := hloc q hqn hq2
      have hcancel := powerTerm_cancel (ρ := ρ) hnpos hqpos
      have hden : 0 < 1 - δ := by linarith
      have hkernel : 0 < (q : ℝ) * a q := mul_pos hqR haq
      have hdiv : a n / ((q : ℝ) * a q) ≤
          ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) / (1 - δ) := by
        rw [div_le_div_iff₀ hkernel hden]
        calc a n * (1 - δ) = (1 - δ) * a n *
              ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) *
                ((q : ℝ) * ((q : ℝ) / n) ^ ρ)) := by
                  rw [hcancel]
                  ring
          _ = ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * q) *
                ((1 - δ) * ((q : ℝ) / n) ^ ρ * a n) := by ring
          _ ≤ ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * q) * a q :=
                mul_le_mul_of_nonneg_left hLower (by positivity)
          _ = (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * ((q : ℝ) * a q) := by ring
      simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv
    have hRlo : 1 - δ ≤ R n := by
      have hcoeff : 1 - δ ≤ 1 / (1 + δ) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [sq_nonneg δ]
      dsimp [R]
      exact le_trans hcoeff ((le_div_iff₀ hpN).2 hlowBlock)
    have hRhi : R n ≤ 1 + 2 * δ := by
      have hcoeff : 1 / (1 - δ) ≤ 1 + 2 * δ := by
        rw [div_le_iff₀ (by linarith)]
        have hδhalf : δ ≤ 1 / 2 := by dsimp [δ]; exact min_le_right _ _
        have hmul : 0 ≤ δ * (1 - 2 * δ) := mul_nonneg (le_of_lt hδ) (by linarith)
        nlinarith
      dsimp [R]
      exact le_trans ((div_le_iff₀ hpN).2 hhighBlock) hcoeff
    rw [Real.dist_eq]
    have habs : |R n - 1| ≤ 2 * δ := by
      rw [abs_le]
      constructor <;> linarith
    exact lt_of_le_of_lt habs hδsmall
  have hmul := hR.mul hP
  have hcongr : (fun n : ℕ => R n * P n) =ᶠ[atTop] B := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos := hPpos n hn
    dsimp [R]
    field_simp [hnpos.ne']
  have hB : Tendsto B atTop
      (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
    have hmul' : Tendsto (fun n : ℕ => R n * P n) atTop
        (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by simpa using hmul
    exact hmul'.congr' hcongr
  simpa [B] using hB

private noncomputable def inverseKernel {a : ℕ → ℝ} (q : ℕ) : ℝ :=
  1 / ((q : ℝ) * a q)

private noncomputable def inverseKernelTail {a : ℕ → ℝ} (n : ℕ) : ℝ :=
  ∑' k : ℕ, inverseKernel (a := a) (n + k)

private theorem inverseKernelTail_split {a : ℕ → ℝ}
    (hs : Summable (inverseKernel (a := a))) (n : ℕ) :
    inverseKernelTail (a := a) n =
      (∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q) +
        inverseKernelTail (a := a) (2 * n) := by
  have hshift : Summable (fun k : ℕ => inverseKernel (a := a) (n + k)) :=
    by simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hs
  have hsplit := hshift.sum_add_tsum_nat_add n
  have hfinite : (∑ k ∈ Finset.range n, inverseKernel (a := a) (n + k)) =
      ∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q := by
    rw [Finset.range_eq_Ico]
    conv_lhs => arg 2; ext k; rw [Nat.add_comm n k]
    rw [Finset.sum_Ico_add' (inverseKernel (a := a)) 0 n (c := n)]
    simp [two_mul]
  have htail : (∑' k : ℕ, inverseKernel (a := a) (n + (k + n))) =
      inverseKernelTail (a := a) (2 * n) := by
    congr 1
    funext k
    congr 1
    omega
  calc
    inverseKernelTail (a := a) n =
        (∑ k ∈ Finset.range n, inverseKernel (a := a) (n + k)) +
          (∑' k : ℕ, inverseKernel (a := a) (n + (k + n))) := hsplit.symm
    _ = (∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q) +
          inverseKernelTail (a := a) (2 * n) := by rw [hfinite, htail]

private theorem inverseKernelTail_shift_eq {a : ℕ → ℝ} (n : ℕ) :
    inverseKernelTail (a := a) (n + 1) =
      ∑' q : ℕ, (Set.Ioi n).indicator (inverseKernel (a := a)) q := by
  let e : ℕ ≃ {q : ℕ // q ∈ Set.Ioi n} :=
    { toFun := fun k => ⟨n + 1 + k, by simp; omega⟩
      invFun := fun q => q.1 - (n + 1)
      left_inv := by intro k; simp
      right_inv := by
        intro q
        apply Subtype.ext
        have hqmem : n < q.1 := q.2
        have hq : n + 1 ≤ q.1 := by omega
        change n + 1 + (q.1 - (n + 1)) = q.1
        exact Nat.add_sub_of_le hq }
  calc
    inverseKernelTail (a := a) (n + 1) =
        ∑' k : ℕ, inverseKernel (a := a) ((n + 1) + k) := rfl
    _ = ∑' q : {q : ℕ // q ∈ Set.Ioi n}, inverseKernel (a := a) q.1 := by
      simpa [e, Nat.add_assoc] using (e.tsum_eq (fun q : {q : ℕ // q ∈ Set.Ioi n} =>
        inverseKernel (a := a) q.1))
    _ = ∑' q : ℕ, (Set.Ioi n).indicator (inverseKernel (a := a)) q :=
      tsum_subtype (Set.Ioi n) (inverseKernel (a := a))

private theorem inverseKernelTail_bound {ρ : ℝ} {a : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      a n * inverseKernelTail (a := a) n ≤ C + 1 := by
  obtain ⟨C, hC, hbound⟩ := hrv.karamata_tail_tsum hmono hpos hρ
  refine ⟨C, hC, fun n hn => ?_⟩
  have hshift := inverseKernelTail_shift_eq (a := a) n
  have htail : inverseKernelTail (a := a) (n + 1) ≤ C / a n := by
    calc inverseKernelTail (a := a) (n + 1) =
          ∑' q : ℕ, (Set.Ioi n).indicator (inverseKernel (a := a)) q := hshift
      _ = ∑' q : ℕ, (Set.Ioi n).indicator (fun q => 1 / ((q : ℝ) * a q)) q := by
          congr 1
      _ ≤ C / a n := hbound n hn
  have hsum := hrv.summable_inv_mul hmono hpos hρ
  have hshiftSum : Summable (fun k : ℕ => inverseKernel (a := a) (n + k)) :=
    by simpa [inverseKernel, Nat.add_comm] using (summable_nat_add_iff n).2 hsum
  have hdecomp : inverseKernelTail (a := a) n =
      inverseKernel (a := a) n + inverseKernelTail (a := a) (n + 1) := by
    dsimp [inverseKernelTail]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hshiftSum.sum_add_tsum_nat_add 1 |>.symm
  have han : 0 < a n := hpos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfirst : a n * inverseKernel (a := a) n = 1 / n := by
    dsimp [inverseKernel]
    field_simp
  have hmulTail : a n * inverseKernelTail (a := a) (n + 1) ≤ C := by
    calc a n * inverseKernelTail (a := a) (n + 1)
        ≤ a n * (C / a n) := mul_le_mul_of_nonneg_left htail han.le
      _ = C := by field_simp
  have hle : a n * inverseKernelTail (a := a) n ≤ 1 / n + C := by
    rw [hdecomp, mul_add, hfirst]
    exact add_le_add_right hmulTail _
  have hone : (1 : ℝ) / n ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hn1
  calc a n * inverseKernelTail (a := a) n
      ≤ 1 / n + C := hle
    _ ≤ C + 1 := by linarith

-- A bounded affine recurrence with a strict contraction determines its limit.
private theorem limsup_le_of_dyadic_recursion
    {F B R : ℕ → ℝ} {c r : ℝ}
    (hb : atTop.IsBoundedUnder (· ≤ ·) F)
    (hl : atTop.IsBoundedUnder (· ≥ ·) F)
    (hB : Tendsto B atTop (𝓝 c)) (hR : Tendsto R atTop (𝓝 r))
    (hr : r < 1) (hRpos : ∀ᶠ n in atTop, 0 ≤ R n)
    (heq : ∀ᶠ n in atTop, F n = B n + R n * F (2 * n)) :
    limsup F atTop ≤ c / (1 - r) := by
  let U := limsup F atTop
  have hdouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show id n ≤ 2 * n by dsimp; omega) tendsto_id
  have hbound (δ : ℝ) (hδ : 0 < δ) : U ≤ c + r * (U + δ) := by
    have hupper : ∀ᶠ n in atTop, F (2 * n) ≤ U + δ :=
      (hdouble.eventually (eventually_lt_of_limsup_lt (by dsimp [U]; linarith) hb)).mono
        (fun _ h => h.le)
    have hcomp : ∀ᶠ n in atTop, F n ≤ B n + R n * (U + δ) := by
      filter_upwards [heq, hupper, hRpos] with n hn hu hp
      rw [hn]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hu hp) _
    have ht := hB.add (hR.mul_const (U + δ))
    exact (limsup_le_limsup hcomp hl.isCoboundedUnder_le ht.isBoundedUnder_le).trans_eq
      ht.limsup_eq
  have hU : U ≤ c + r * U := by
    have ht : Tendsto (fun n : ℕ => c + r * (U + 1 / (n : ℝ))) atTop
        (𝓝 (c + r * U)) := by
      simpa using (tendsto_const_nhds.add
        ((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).const_mul r))
    apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact hbound _ (by positivity)
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).2
  dsimp [U] at hU ⊢
  nlinarith

private theorem tendsto_of_dyadic_recursion
    {F B R : ℕ → ℝ} {L r : ℝ}
    (hb : atTop.IsBoundedUnder (· ≤ ·) F)
    (hl : atTop.IsBoundedUnder (· ≥ ·) F)
    (hB : Tendsto B atTop (𝓝 ((1 - r) * L))) (hR : Tendsto R atTop (𝓝 r))
    (hr : r < 1) (hRpos : ∀ᶠ n in atTop, 0 ≤ R n)
    (heq : ∀ᶠ n in atTop, F n = B n + R n * F (2 * n)) :
    Tendsto F atTop (𝓝 L) := by
  have hu : limsup F atTop ≤ L := by
    have := limsup_le_of_dyadic_recursion hb hl hB hR hr hRpos heq
    rwa [mul_div_cancel_left₀ _ (by linarith : 1 - r ≠ 0)] at this
  have hnegB : Tendsto (fun n => -B n) atTop (𝓝 ((1 - r) * (-L))) := by
    simpa using hB.neg
  obtain ⟨u, hu'⟩ := hb
  obtain ⟨l, hl'⟩ := hl
  have hnb : atTop.IsBoundedUnder (· ≤ ·) (fun n => -F n) :=
    ⟨-l, hl'.mono (fun _ h => neg_le_neg h)⟩
  have hnl : atTop.IsBoundedUnder (· ≥ ·) (fun n => -F n) :=
    ⟨-u, hu'.mono (fun _ h => neg_le_neg h)⟩
  have hnrec : ∀ᶠ n in atTop, -F n = -B n + R n * (-F (2 * n)) := by
    filter_upwards [heq] with n hn
    rw [hn]; ring
  have hn := limsup_le_of_dyadic_recursion hnb hnl hnegB hR hr hRpos hnrec
  rw [mul_div_cancel_left₀ _ (by linarith : 1 - r ≠ 0)] at hn
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (show L < L + ε by linarith))
        ⟨u, hu'⟩).and
      (eventually_lt_of_limsup_lt (lt_of_le_of_lt hn (show -L < -L + ε by linarith)) hnb))
  refine ⟨N, fun n h => ?_⟩
  obtain ⟨h1, h2⟩ := hN n h
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

-- Sharp Karamata: the dyadic block tends to (1 - r) / ρ, the tail is bounded,
-- and its recurrence has multiplier a n / a (2 * n) → r = 2 ^ (-ρ) < 1.
private theorem inverseKernelTail_tendsto {ρ : ℝ} {a : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    Tendsto (fun n : ℕ => a n * inverseKernelTail (a := a) n) atTop (𝓝 (1 / ρ)) := by
  let F : ℕ → ℝ := fun n => a n * inverseKernelTail (a := a) n
  let B : ℕ → ℝ := fun n => a n *
    ∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q
  let R : ℕ → ℝ := fun n => a n / a (2 * n)
  let r : ℝ := (2 : ℝ) ^ (-ρ)
  have hr : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hR : Tendsto R atTop (𝓝 r) := by
    have ht := (hrv 2 (by norm_num)).inv₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) ρ))
    have hf (n : ℕ) : ⌊(2 : ℝ) * n⌋₊ = 2 * n := by
      rw [show (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
    simpa [R, r, Real.rpow_neg, hf] using ht
  obtain ⟨C, hC, hbound⟩ := inverseKernelTail_bound hρ hrv hmono hpos
  have hb : atTop.IsBoundedUnder (· ≤ ·) F := by
    refine ⟨C + 1, ?_⟩
    change ∀ᶠ n in atTop, F n ≤ C + 1
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n hn
  have hl : atTop.IsBoundedUnder (· ≥ ·) F := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ F n
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply mul_nonneg (hpos n hn).le
    apply tsum_nonneg
    intro k
    dsimp [inverseKernel]
    exact one_div_nonneg.mpr (mul_nonneg (by positivity) (hpos _ (by omega)).le)
  apply tendsto_of_dyadic_recursion hb hl (r := r)
  · simpa [B, inverseKernel, r, div_eq_mul_inv] using inverseBlock_tendsto hρ hrv hmono hpos
  · exact hR
  · exact hr
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (hpos n hn).le (hpos _ (by omega)).le
  · have hs : Summable (inverseKernel (a := a)) := hrv.summable_inv_mul hmono hpos hρ
    filter_upwards [eventually_ge_atTop 1] with n hn
    have ha : a (2 * n) ≠ 0 := (hpos _ (by omega)).ne'
    dsimp [F, B, R]
    rw [inverseKernelTail_split hs n, mul_add]
    have hc : a n / a (2 * n) * (a (2 * n) * inverseKernelTail (a := a) (2 * n)) =
        a n * inverseKernelTail (a := a) (2 * n) := by field_simp
    rw [hc]
    simp only [inverseKernel, one_div, mul_inv_rev]

private theorem sizeEvents_disjoint (n : ℕ) :
    Pairwise (fun i j : ℕ => Disjoint (sizeEvent (n + i)) (sizeEvent (n + j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro T hi hj
  have hi' := hi.2
  have hj' := hj.2
  apply hij
  omega

private theorem sizeGe_real_eq_tsum {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ α a) (n : ℕ) :
    (bienaymeLaw μ.toMeasure).real (sizeGeEvent n) =
      ∑' k : ℕ, (bienaymeLaw μ.toMeasure).real (sizeEvent (n + k)) := by
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure ≤ 1 := by
    rw [lintegral_countable']
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using h.critical.le
  have hne : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using h.nondegenerate
  have hae := BGW.LocallyFinite.ae_finiteVertices_bienaymeLaw μ.toMeasure hm hne
  have hevent : sizeGeEvent n =ᵐ[bienaymeLaw μ.toMeasure] ⋃ k : ℕ, sizeEvent (n + k) := by
    filter_upwards [hae] with T hT
    apply propext
    simp only [Set.mem_iUnion, sizeGeEvent, Set.mem_ofPred_eq, sizeEvent, hT,
      not_true_eq_false, false_or, true_and]
    constructor
    · intro hn
      exact ⟨{u | Present T u}.ncard - n, by omega⟩
    · rintro ⟨k, hk⟩
      omega
  rw [measureReal_congr hevent, measureReal_def,
    measure_iUnion (sizeEvents_disjoint n) (fun k => BGW.LocallyFinite.measurableSet_sizeEvent _),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  rfl

private theorem weighted_tail_tendsto {ρ c : ℝ} {a p : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hp : Summable p)
    (hpoint : Tendsto (fun n : ℕ => (n : ℝ) * a n * p n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => a n * ∑' k : ℕ, p (n + k)) atTop (𝓝 (c * (1 / ρ))) := by
  have hk : Summable (inverseKernel (a := a)) := hrv.summable_inv_mul hmono hpos hρ
  have ht := (inverseKernelTail_tendsto hρ hrv hmono hpos).const_mul c
  obtain ⟨C, hC, hbound⟩ := inverseKernelTail_bound hρ hrv hmono hpos
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδmul : δ * (C + 1) = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hpoint δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 ht (ε / 2) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have han : 0 < a n := hpos _ hn1
  have hks : Summable (fun k => inverseKernel (a := a) (n + k)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hk
  have hps : Summable (fun k => p (n + k)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hp
  have hterm (k : ℕ) : ‖p (n + k) - c * inverseKernel (a := a) (n + k)‖ ≤
      δ * inverseKernel (a := a) (n + k) := by
    let q := n + k
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have haq : 0 < a q := hpos q hq
    have hkp : 0 ≤ inverseKernel (a := a) q := by dsimp [inverseKernel]; positivity
    have hid : p q - c * inverseKernel (a := a) q =
        ((q : ℝ) * a q * p q - c) * inverseKernel (a := a) q := by
      dsimp [inverseKernel]
      field_simp
    have hclose : |(q : ℝ) * a q * p q - c| ≤ δ := by
      exact (show dist ((q : ℝ) * a q * p q) c < δ from hN₁ q (by dsimp [q]; omega)).le
    rw [Real.norm_eq_abs, hid, abs_mul, abs_of_nonneg hkp]
    exact mul_le_mul_of_nonneg_right hclose hkp
  have he := (hps.hasSum.sub (hks.hasSum.mul_left c)).norm_le_of_bounded
    (hks.hasSum.mul_left δ) hterm
  have he' : |(∑' k : ℕ, p (n + k)) - c * inverseKernelTail (a := a) n| ≤
      δ * inverseKernelTail (a := a) n := by
    simpa only [Real.norm_eq_abs, inverseKernelTail] using he
  have hscaled : |a n * (∑' k : ℕ, p (n + k)) -
      c * (a n * inverseKernelTail (a := a) n)| ≤ ε / 2 := by
    calc _ = |a n * ((∑' k : ℕ, p (n + k)) - c * inverseKernelTail (a := a) n)| := by
            congr 1
            ring
      _ = a n * |(∑' k : ℕ, p (n + k)) - c * inverseKernelTail (a := a) n| := by
            rw [abs_mul, abs_of_pos han]
      _ ≤ a n * (δ * inverseKernelTail (a := a) n) := mul_le_mul_of_nonneg_left he' han.le
      _ = δ * (a n * inverseKernelTail (a := a) n) := by ring
      _ ≤ δ * (C + 1) := mul_le_mul_of_nonneg_left (hbound n hn1) hδ.le
      _ = ε / 2 := hδmul
  have hclose := hN₂ n hnN₂
  rw [Real.dist_eq] at hclose ⊢
  calc _ ≤ |a n * (∑' k : ℕ, p (n + k)) - c * (a n * inverseKernelTail (a := a) n)| +
        |c * (a n * inverseKernelTail (a := a) n) - c * (1 / ρ)| := abs_sub_le _ _ _
    _ < ε := by linarith

/-- The sharp tail asymptotic of the total progeny law (Lemma 1.11). -/
theorem sizeTail_asymp {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (h : StableDomain μ α a)
    (hap : Aperiodic μ) :
    Tendsto (fun n : ℕ => a n * (bienaymeLaw μ.toMeasure).real (sizeGeEvent n)) atTop
      (𝓝 (α * Scalar.stableDensity α 0)) := by
  have hp : Summable (fun q => (bienaymeLaw μ.toMeasure).real (sizeEvent q)) := by
    apply summable_measure_toReal BGW.LocallyFinite.measurableSet_sizeEvent
    simpa only [zero_add, Function.onFun] using sizeEvents_disjoint 0
  have hρ : 0 < 1 / α := by have := h.alpha_mem.1; positivity
  have ht := weighted_tail_tendsto hρ (Scalar.regularlyVaryingSeq h) h.monotone h.pos hp
    (BGWLeaves.StableAnalysis.sizeProb_asymp h hap)
  simpa only [sizeGe_real_eq_tsum h, one_div_one_div, mul_comm (Scalar.stableDensity α 0) α] using ht

end BGWLeaves.StableAnalysis.SizeTail
