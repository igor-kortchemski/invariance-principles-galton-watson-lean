module

public import BGWLeaves.GeneralAFunctional.TreeConcentration
public import BGWLeaves.ClassicalLimits.Perturbation
public import BGW.StableTrees.RealAttractionBounds

/-! Elementary probability perturbations for the random total-size clock.
Adapted from the leaf-conditioned contour/height module `BGWLeaves.LeafLimits.ContourHeight`. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeProbability

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

theorem probability_continuous_pair {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {X Y : ∀ n, Ω n → ℝ} {c d : ℝ}
    (hX : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (X n ω) c}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (Y n ω) d}) atTop (𝓝 0))
    {G : ℝ × ℝ → ℝ} (hG : ContinuousAt G (c, d)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (G (X n ω, Y n ω)) (G (c, d))}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hG ε hε
  have hlim := (hX (δ / 2) (half_pos hδ)).add (hY (δ / 2) (half_pos hδ))
  simp only [zero_add] at hlim
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hlim
  apply (measureReal_mono (s₂ := {ω | δ / 2 < dist (X n ω) c} ∪
    {ω | δ / 2 < dist (Y n ω) d}) ?_).trans (measureReal_union_le _ _)
  intro ω hω
  by_contra hout
  have hx : dist (X n ω) c ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inl h))
  have hy : dist (Y n ω) d ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inr h))
  have hp : dist (X n ω, Y n ω) (c, d) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (hx.trans_lt (half_lt_self hδ)) (hy.trans_lt (half_lt_self hδ))
  exact (not_lt_of_ge (hclose hp).le) hω

theorem probability_const {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {x : ℕ → ℝ} {c : ℝ}
    (hx : Tendsto x atTop (𝓝 c)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {_ω | ε < dist (x n) c})
      atTop (𝓝 0) := by
  intro ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_iff_dist_tendsto_zero.mp hx).eventually (gt_mem_nhds hε)] with n hn
  simp [not_lt_of_gt hn]

theorem probability_continuous {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {X : ∀ n, Ω n → ℝ} {c : ℝ}
    (hX : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (X n ω) c}) atTop (𝓝 0))
    {G : ℝ → ℝ} (hG : ContinuousAt G c) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (G (X n ω)) (G c)}) atTop (𝓝 0) :=
  probability_continuous_pair P (X := X) (Y := fun _ _ => (0 : ℝ))
    (c := c) (d := 0) (G := fun p : ℝ × ℝ => G p.1) hX
    (probability_const P (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    (hG.comp continuous_fst.continuousAt)

theorem probability_max_index {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {m : ∀ n, Ω n → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / q n) c}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((max (m n ω) 1 : ℕ) / (q n : ℝ)) c}) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n => 1 / (q n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hqtop
  have ht := probability_continuous_pair P hm (probability_const P hsmall)
    (continuous_fst.max continuous_snd).continuousAt
  simp only [max_eq_left hc.le] at ht
  intro ε hε
  apply (ht ε hε).congr'
  filter_upwards [hqtop.eventually_ge_atTop 1] with n hn
  congr 1
  ext ω
  have hnR : (0 : ℝ) < q n := by exact_mod_cast hn
  have heq : (max (m n ω) 1 : ℕ) / (q n : ℝ) =
      max ((m n ω : ℝ) / q n) (1 / (q n : ℝ)) := by
    by_cases hm0 : m n ω = 0
    · simp [hm0]
    · have hm1 : 1 ≤ m n ω := by omega
      rw [max_eq_left hm1, max_eq_left]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hm1) hnR.le
  change (ε < dist (max ((m n ω : ℝ) / q n) (1 / (q n : ℝ))) c) ↔
    (ε < dist ((max (m n ω) 1 : ℕ) / (q n : ℝ)) c)
  rw [heq]


theorem probability_index_ratio {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {q r : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    {m : ∀ n, Ω n → ℕ} {c : ℝ} (hc : 0 < c)
    (hr : Tendsto (fun n => (r n : ℝ) / q n) atTop (𝓝 c))
    (hm : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / q n) c}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / r n) 1}) atTop (𝓝 0) := by
  have ht := probability_continuous_pair P (G := fun p : ℝ × ℝ => p.1 / p.2) hm (probability_const P hr)
    (continuous_fst.continuousAt.div continuous_snd.continuousAt hc.ne')
  simp only [div_self hc.ne'] at ht
  intro ε hε
  apply (ht ε hε).congr'
  filter_upwards [hqtop.eventually (eventually_ne_atTop (0 : ℕ))] with n hn
  congr 1
  ext ω
  change (ε < dist (((m n ω : ℝ) / q n) / ((r n : ℝ) / q n)) 1) ↔
    (ε < dist ((m n ω : ℝ) / r n) 1)
  rw [div_div_div_cancel_right₀ (show (q n : ℝ) ≠ 0 by exact_mod_cast hn)]

theorem probability_norming_ratio {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) {r : ℕ → ℕ} (hrtop : Tendsto r atTop atTop)
    {m : ∀ n, Ω n → ℕ}
    (hm : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist ((m n ω : ℝ) / r n) 1}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (B (m n ω) / B (r n)) 1}) atTop (𝓝 0) := by
  intro ε hε
  have hp : ContinuousAt (fun x : ℝ => x ^ (1 / θ)) 1 :=
    Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
  obtain ⟨η, hη, hpη⟩ := Metric.continuousAt_iff.mp hp (ε / 2) (half_pos hε)
  let δ := min (η / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (half_pos hη) (by norm_num)
  have hδη : δ < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨N, hN⟩ := hB.uniform_ratio (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 2) (ε / 2) (half_pos hε)
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ (hm δ hδ)
  filter_upwards [hrtop.eventually_ge_atTop N, hrtop.eventually_ge_atTop 1] with n hn hn1
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  by_contra hnot
  have hrat : |(m n ω : ℝ) / r n - 1| ≤ δ := by
    simpa only [Real.dist_eq] using le_of_not_gt hnot
  have hrpos : (0 : ℝ) < r n := by exact_mod_cast hn1
  have hbds := abs_le.mp hrat
  have hlo : (1 / 2 : ℝ) * r n ≤ m n ω :=
    (le_div_iff₀ hrpos).mp (by linarith [hbds.1])
  have hhi : (m n ω : ℝ) ≤ 2 * r n :=
    (div_le_iff₀ hrpos).mp (by linarith [hbds.2])
  have happrox := hN (r n) hn (m n ω) hlo hhi
  have hpclose : |((m n ω : ℝ) / r n) ^ (1 / θ) - 1| < ε / 2 := by
    have hdist : dist ((m n ω : ℝ) / r n) 1 < η := by
      rw [Real.dist_eq]
      exact hrat.trans_lt hδη
    simpa only [Real.dist_eq, Real.one_rpow] using hpη hdist
  have htri := abs_sub_le (B (m n ω) / B (r n))
    (((m n ω : ℝ) / r n) ^ (1 / θ)) 1
  change ε < dist (B (m n ω) / B (r n)) 1 at hω
  rw [Real.dist_eq] at hω
  linarith



end BGWLeaves.GeneralAFunctional.TreeProbability
