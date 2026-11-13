/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionPassage
public import BGW.StableTrees.LongExtractionBlocks
public import BGW.StableTrees.LongExtractionPlateaus
public import BGW.StableTrees.LongExtractionInterior
public import BGW.StableTrees.LongExtractionEndpoints
public import BGW.StableTrees.LongExtractionCutClocks
public import BGW.StableTrees.LongExtractionCut

/-!
# Deterministic first-long-block extraction

Ladder times at non-jump levels, the first long block's endpoints, and its stopped translated
path converge under J1 convergence of skip-free walks to a good extraction path. The proof uses
joint continuity of moving stopped cuts and an exact one-mesh terminal-step comparison.

## References

* T. Duquesne and J.-F. Le Gall, *Random Trees, Lévy Processes and Spatial Branching
  Processes*, Astérisque 281 (2002), Chapter 2.
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Chapter 3
  (the Skorokhod topology).
-/

@[expose] public section
