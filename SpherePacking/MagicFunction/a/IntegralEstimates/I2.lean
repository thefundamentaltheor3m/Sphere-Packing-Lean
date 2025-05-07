/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic

/-! # Constructing Upper-Bounds for I₂

The purpose of this file is to construct bounds on the integral `I₂` that is part of the definition
of the function `a`. We do something similar to what we did for `I₁` in
`SpherePacking.MagicFunction.a.IntegralEstimates.I1`.
-/

open MagicFunction.a.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Function

-- Need to copy and paste from I₁ file
