module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Kernel lemmas for `perm_J5`

The Fourier permutation argument for the `J₅/J₆` pieces uses a common complex kernel depending
on an exponent `k`. This file collects small, dimension-agnostic lemmas about that kernel; the
main result computes its norm where the purely oscillatory factors have norm `1`.
-/

open scoped RealInnerProductSpace

namespace SpherePacking.Contour

noncomputable section

end

end SpherePacking.Contour
