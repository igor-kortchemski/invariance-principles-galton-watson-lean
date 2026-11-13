/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeConvergence
public import BGW.StableTrees.DiscreteBridgeTerminal
import BGW.Skorokhod.Prefix
import BGW.StableTrees.StableBridgeClosed

/-!
# The walk bridge invariance principle

Strict-prefix convergence and terminal-window smallness give full weak convergence
on `D[0,1]` by the prefix-extension criterion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod

/-- **Walk bridge invariance principle (K06 main theorem).**  Along an unbounded sequence of
admissible sizes, the walk conditioned to end at `-1` at time `q k`, scaled by `B (q k)`,
converges weakly in `D[0,1]` to the stable bridge `stableBridgeLaw θ`. -/
theorem tendsto_walkBridgeLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => walkBridgeLaw μ B (q k) (hq k)) atTop (𝓝 (stableBridgeLaw θ)) := by
  let P := fun n => walkBridgeLaw μ B (q n) (hq n)
  let c : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 2)
  have hcPos (k : ℕ) : 0 < c k := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hd : 0 < (k : ℝ) + 2 := by positivity
    exact sub_pos.mpr ((div_lt_one hd).mpr (by linarith))
  let b : ℕ → ℝ≥0 := fun k => ⟨c k, (hcPos k).le⟩
  let a : ℕ → ℝ := fun k => (b k : ℝ)
  have haPos (k : ℕ) : 0 < a k := hcPos k
  have haT (k : ℕ) : a k < 1 := by
    change c k < 1
    exact sub_lt_self _ (by positivity)
  have ha0 (k : ℕ) : 0 ≤ a k := (haPos k).le
  have halim : Tendsto a atTop (𝓝 1) := by
    change Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 2)) atTop (𝓝 1)
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop).const_div_atTop (1 : ℝ))
    simpa only [sub_zero] using ht
  have hpre (k : ℕ) : Tendsto (fun n => (P n).map (BGW.Skorokhod.restrict (haT k).le ∘ id))
      atTop (𝓝 ((stableBridgeLaw θ).map (BGW.Skorokhod.restrict (haT k).le))) := by
    have hak : b k ∈ Ioo (0 : ℝ≥0) 1 :=
      ⟨by exact_mod_cast haPos k, by exact_mod_cast haT k⟩
    simpa only [restrictLaw, Function.comp_id] using
      tendsto_restrictLaw_walkBridgeLaw h hqtop hq (b k) hak
  have hosc : ∀ η > 0, Tendsto (fun k => limsup (fun n => (P n : Measure (D 1 ℝ)).real
      {x | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a k ≤ (s : ℝ)},
        dist (x s) (x ⟨a k, ha0 k, (haT k).le⟩)}) atTop) atTop (𝓝 0) := by
    intro η hη
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, _, hterminal⟩ := walkBridgeLaw_terminal_small h hqtop hq
      (ε := η / 4) (η := ε / 2) (by positivity) (by positivity)
    have hacut : ∀ᶠ k in atTop, 1 - δ < a k :=
      halim.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith))
    rw [← eventually_atTop]
    filter_upwards [hacut] with k hk
    let A : Set (D 1 ℝ) := {x | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a k ≤ (s : ℝ)},
      dist (x s) (x ⟨a k, ha0 k, (haT k).le⟩)}
    have hsub :
        A ⊆ {x | ∃ t : Set.Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ η / 4 ≤ |x t|} := by
      intro x hx
      by_contra hnot
      have hs (t : Set.Icc (0 : ℝ) 1) (ht : 1 - δ ≤ (t : ℝ)) : |x t| < η / 4 :=
        lt_of_not_ge (fun hh => hnot ⟨t, ht, hh⟩)
      let t₀ : Set.Icc (0 : ℝ) 1 := ⟨a k, ha0 k, (haT k).le⟩
      let _ : Nonempty {s : Set.Icc (0 : ℝ) 1 // a k ≤ (s : ℝ)} := ⟨⟨t₀, le_rfl⟩⟩
      have hb :
          (⨆ s : {s : Set.Icc (0 : ℝ) 1 // a k ≤ (s : ℝ)},
            dist (x s) (x t₀)) ≤ η / 2 := by
        apply ciSup_le
        intro s
        calc
          dist (x s) (x t₀) = |x s - x t₀| := Real.dist_eq _ _
          _ ≤ |x s| + |x t₀| := by simpa using abs_sub_le (x s) 0 (x t₀)
          _ ≤ η / 2 := by linarith [hs s (hk.le.trans s.2), hs t₀ hk.le]
      change η < _ at hx
      linarith
    have hnn : 0 ≤ limsup (fun n => (P n : Measure (D 1 ℝ)).real A) atTop :=
      le_limsup_of_frequently_le (Frequently.of_forall fun _ => measureReal_nonneg)
        (isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩)
    have hle : limsup (fun n => (P n : Measure (D 1 ℝ)).real A) atTop ≤ ε / 2 := by
      apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
      filter_upwards [hterminal] with n hn
      have htoreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hn
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ ε / 2)] at htoreal
      exact (measureReal_mono hsub).trans htoreal
    change dist (limsup (fun n => (P n : Measure (D 1 ℝ)).real A) atTop) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    exact hle.trans_lt (half_lt_self hε)
  have ht := tendsto_of_tendsto_restrict_of_oscillation P
    (Y := fun _ => id) (fun _ => measurable_id) zero_lt_one ha0 haT halim hpre
    (stableBridgeLaw_ae_continuousAt h.alpha_mem ⟨1, zero_le_one, le_rfl⟩) hosc
  have hmapid (n : ℕ) : (P n).map id = P n := by
    apply Subtype.ext
    exact Measure.map_id
  simpa only [hmapid] using ht

end BGW.StableTrees.DiscreteBridge
