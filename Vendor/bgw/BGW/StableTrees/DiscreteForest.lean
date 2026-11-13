/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestRestart
public import BGW.StableTrees.DiscreteForestMeasurable
public import BGW.StableTrees.DiscreteForestLadder
public import BGW.StableTrees.DiscreteForestTreeLaws
public import BGW.StableTrees.DiscreteForestPrefixDensity

/-!
# Discrete forest coding

The iid offspring walk, its record-count height and interpolated pair law,
stopped restart, almost sure ladder finiteness, deterministic block decoding,
and tree-conditioning carriers.

Finite degree-word cylinders identify the blocks as iid BGW trees. The first
long block has the size-tail conditioned law. Surviving prefix completions give
the exact and tail prefix masses, their Radon–Nikodym identity and mass one;
fixed-time splitting also gives the bridge-prefix identities.
-/

@[expose] public section
