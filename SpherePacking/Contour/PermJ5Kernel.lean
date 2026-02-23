module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Kernel lemmas for `perm_J5`

The Fourier permutation argument for the `J₅/J₆` pieces uses a common complex kernel depending on
an exponent `k`.

This file collects small, dimension-agnostic lemmas about that kernel; the main result is a
formula for its norm where the purely oscillatory factors have norm `1`.
-/

open scoped RealInnerProductSpace

namespace SpherePacking.Contour

noncomputable section

/-- Compute the norm of the `perm_J5` kernel, extracting the unit-modulus factors. -/
public lemma permJ5_kernel_norm_eq_of
    {k : ℕ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ψS' : ℂ → ℂ)
    (w x : V) (s : ℝ) :
    ‖Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
        ((-Complex.I : ℂ) *
              ψS' ((Complex.I : ℂ) * (s : ℂ)) *
              (s ^ (-(k : ℤ)) : ℂ) *
              Complex.exp ((-Real.pi * (‖x‖ ^ 2) / s : ℝ) : ℂ))‖ =
      (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-(k : ℤ)) : ℂ)‖) *
        Real.exp (-Real.pi * (‖x‖ ^ 2) / s) := by
  have hphase : ‖Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I)‖ = (1 : ℝ) := by
    simpa using Complex.norm_exp_ofReal_mul_I (-2 * (Real.pi * ⟪x, w⟫))
  have hexp :
      ‖Complex.exp ((-Real.pi * (‖x‖ ^ 2) / s : ℝ) : ℂ)‖ =
        Real.exp (-Real.pi * (‖x‖ ^ 2) / s) :=
    Complex.norm_exp_ofReal (-Real.pi * (‖x‖ ^ 2) / s)
  simp only [norm_mul, hphase, hexp, norm_neg, Complex.norm_I, one_mul]

end

end SpherePacking.Contour
