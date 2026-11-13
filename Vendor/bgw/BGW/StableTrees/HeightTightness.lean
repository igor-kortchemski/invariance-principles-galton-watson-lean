/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessBasic
public import BGW.StableTrees.HeightTightnessMaximum
public import BGW.StableTrees.HeightTightnessRise
public import BGW.StableTrees.HeightTightnessGridLaw
public import BGW.StableTrees.HeightTightnessGridEnclosure
public import BGW.StableTrees.HeightTightnessModulus
public import BGW.StableTrees.HeightTightnessLaw
public import BGW.StableTrees.HeightTightnessJoint

/-!
# Discrete forest height oscillations and regeneration

The public interface collects the measurable height modulus, vanishing adjacent
jumps, running-maximum and path-law tightness, and the joint walk/height limit.
The proofs use discrete regenerated crossings, survival and passage estimates,
finite-grid convergence, Arzelà-Ascoli, and subsequential identification.
-/

@[expose] public section
