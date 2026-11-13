/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureCounts
public import BGW.StableTrees.ExcursionMeasureCompensation
public import BGW.StableTrees.ExcursionMeasureLaplace
public import BGW.StableTrees.ExcursionMeasureSupport
public import BGW.StableTrees.ExcursionMeasurePredictable

/-! The excursion measure, product intensity, Poisson box counts and stopped-past step compensation.

The imported modules prove the Laplace functional, general and left-continuous predictable
compensation, and full support identification. Support transfers through measurable compact-window
lower bounds; the general predictable identity follows from finite-measure uniqueness.

## References

K. Itô, Poisson point processes attached to Markov processes, Proc. Sixth Berkeley Symp. 3 (1972),
225–239; J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV;
O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002, Chapters 12 and 22.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

end BGW.StableTrees
