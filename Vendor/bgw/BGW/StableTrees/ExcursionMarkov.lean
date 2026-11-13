/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMarkovConsequences

/-!
# Killed stable kernels and the Markov property of the excursion measure

Main results:

* `killedStableKernel`: the stable kernel killed at its first strict passage below zero.
* `excursion_markov_lintegral`, `excursion_markov_integral`: the Markov property of the
  excursion measure at a positive age, for nonnegative and for integrable test functions.
* `excursion_remainingLifetime_lintegral`: the remaining lifetime is a stable passage time.
* `N_noFixedJump`: the excursion measure has no fixed jump times.
* `exists_excursionAge_stoppingTimes`: strict age-window clocks that are stopping times.
* `lastPositiveTime` bridges: the lifetime of an excursion future is its last positive time.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
* T. Duquesne and J.-F. Le Gall, *Random Trees, Lévy Processes and Spatial Branching
  Processes*, Astérisque 281 (2002), Chapter 1.
-/

@[expose] public section
