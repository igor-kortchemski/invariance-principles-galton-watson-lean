/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionInfimum

/-!
# Moving-time convergence of running infima

When the limiting running infimum is continuous, prefix infima converge at moving times.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- J1 convergence and a continuous limiting infimum permit moving evaluation times.
Reference: Billingsley (1999), Chapter 3. -/
theorem tendsto_extractionPrefixInf {M : ℝ≥0} {p : ℕ → D (M : ℝ) ℝ} {f : DLoc}
    (hI : Continuous (runningInfLoc f))
    (hp : Tendsto p atTop (𝓝 (DLoc.restrict M f)))
    {t : ℕ → Set.Icc (0 : ℝ) (M : ℝ)} {a : ℝ≥0}
    (ht : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 (a : ℝ))) :
    Tendsto (fun n => extractionPrefixInf (p n) (t n)) atTop (𝓝 (runningInfLoc f a)) := by
  obtain ⟨σ, hσ, he⟩ := tendsto_iff_exists_timeChange.mp hp
  let z (n : ℕ) := (σ n).symm (t n)
  let zNN (n : ℕ) : ℝ≥0 := ⟨(z n : ℝ), (z n).2.1⟩
  have hmove (n : ℕ) : |(z n : ℝ) - (t n : ℝ)| ≤
      ⨆ s, |(σ n s : ℝ) - s| := by
    have hb : BddAbove (Set.range fun s => |(σ n s : ℝ) - s|) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact TimeChange.abs_sub_le (σ n) M.2 s
    have h := le_ciSup hb (z n)
    simpa only [z, OrderIso.apply_symm_apply, abs_sub_comm] using h
  have hdiff : Tendsto (fun n => (z n : ℝ) - (t n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hσ
    exact Filter.Eventually.of_forall fun n => by simpa only [Real.norm_eq_abs] using hmove n
  have hz : Tendsto (fun n => (z n : ℝ)) atTop (𝓝 (a : ℝ)) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add ht
  have hzNN : Tendsto zNN atTop (𝓝 a) := NNReal.tendsto_coe.mp hz
  have hIz : Tendsto (fun n => runningInfLoc f (zNN n)) atTop (𝓝 (runningInfLoc f a)) :=
    hI.continuousAt.tendsto.comp hzNN
  have herror (n : ℕ) :
      |extractionPrefixInf (p n) (t n) - runningInfLoc f (zNN n)| ≤
        ⨆ s, dist (p n (σ n s)) ((DLoc.restrict M f) s) := by
    have hb : BddAbove (Set.range fun s =>
        dist (p n (σ n s)) ((DLoc.restrict M f) s)) := by
      simpa only [dist_comm] using bddAbove_range_dist (DLoc.restrict M f) (p n) (σ n)
    have h := extractionPrefixInf_aligned_le (p n) (DLoc.restrict M f) (σ n)
      (fun s => le_ciSup hb s) (z n)
    simpa only [z, OrderIso.apply_symm_apply, extractionPrefixInf_restrict] using h
  have hdiff' : Tendsto (fun n => extractionPrefixInf (p n) (t n) -
      runningInfLoc f (zNN n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ he
    exact Filter.Eventually.of_forall fun n => by simpa only [Real.norm_eq_abs] using herror n
  simpa only [sub_add_cancel, zero_add] using hdiff'.add hIz

end BGW.StableTrees
