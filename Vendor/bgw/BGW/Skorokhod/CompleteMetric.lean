/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricCompleteness

/-!
# Billingsley's complete metric on the Skorokhod space

This entry point exports logarithmic time-change slope, Billingsley's distance `d°`, its metric
space `DComplete`, and the identity homeomorphism `toDComplete`. The distance is complete whenever
the state space is complete, so the original J1 space is completely metrizable.

The comparison on `[0,T]` is `dist f g ≤ max 1 T * (exp (j1CompleteDist f g) - 1)`.
No sign assumption on the horizon is needed: the interval is empty when `T < 0`.

References: Billingsley, *Convergence of Probability Measures*, 2nd ed., §12,
(12.13), (12.16), (12.17), Theorems 12.1 and 12.2; Ethier–Kurtz, ch. 3, §5.
-/

@[expose] public section
