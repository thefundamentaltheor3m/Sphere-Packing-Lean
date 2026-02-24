module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Real.Basic

/-!
# Inversion change of variables on `Ioc (0, 1]`

This file collects change-of-variables lemmas for the substitution `t ↦ 1 / t` on `Ioc (0, 1]`.
They rewrite integrals over `Ioc (0, 1]` into integrals over `Ici 1` using the one-dimensional
Jacobian formula.
-/

namespace SpherePacking.Integration

noncomputable section

open Set MeasureTheory

namespace InvChangeOfVariables

open Complex Real

/-!
## Algebraic normalizations for the substitution `t ↦ 1 / t`

Several contour/Fourier developments use the change of variables `t ↦ 1/t`.
We record the recurring pure algebra simplifications here so call sites stay uniform.
-/

/-- Simplify the Jacobian factor and an inverse power after substituting `t ↦ 1 / t`.

This is the identity
`(1 / t ^ 2) * (1 / t) ^ (-k) = t ^ (k - 2)` for `2 ≤ k` and `t ≠ 0`.
-/
public lemma one_div_pow_two_mul_one_div_zpow (k : ℕ) (t : ℝ) (hk : 2 ≤ k) (ht : t ≠ 0) :
    (1 / t ^ 2) * ((1 / t : ℝ) ^ (-(k : ℤ))) = t ^ (k - 2) := by
  have hzpow : (1 / t : ℝ) ^ (-(k : ℤ)) = t ^ k := by
    rw [one_div]
    simp [zpow_natCast]
  simpa [one_div, hzpow, mul_assoc, mul_left_comm, mul_comm] using (pow_sub₀ t ht hk).symm

/-- The image of `t ↦ 1 / t` on `Ioc (0, 1]` is `Ici 1`. -/
public lemma Ici_one_eq_image_inv_Ioc :
    Ici (1 : ℝ) = (fun t : ℝ => 1 / t) '' (Ioc (0 : ℝ) (1 : ℝ)) := by
  ext x
  constructor
  · intro hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    refine ⟨x⁻¹, ⟨?_, ?_⟩, by simp⟩
    · simpa [one_div] using inv_pos.2 hx0
    · simpa [one_div] using (inv_le_one₀ hx0).2 hx
  · rintro ⟨y, hy, rfl⟩
    simpa [one_div, mem_Ici] using (one_le_inv_iff₀.2 hy)

/-- Rewrite an integral over `Ici 1` as an integral over the corresponding image set. -/
public lemma integral_Ici_one_eq_integral_image_inv (g : ℝ → ℂ) :
    ∫ s in Ici (1 : ℝ), g s = ∫ s in (fun t : ℝ => 1 / t) '' (Ioc (0 : ℝ) (1 : ℝ)), g s :=
  by simp [Ici_one_eq_image_inv_Ioc]

/-- Change-of-variables formula for `t ↦ 1 / t` on `Ioc (0, 1]`, written on the image set. -/
public lemma integral_image_inv_eq_integral_abs_deriv_smul (g : ℝ → ℂ) :
    ∫ s in (fun t : ℝ => 1 / t) '' (Ioc (0 : ℝ) (1 : ℝ)), g s =
      ∫ t in Ioc (0 : ℝ) 1, |(-1 / t ^ 2)| • g (1 / t) :=
  integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun x hx => by
      simpa [one_div, div_eq_mul_inv] using
        (hasDerivWithinAt_inv (x := x) (ne_of_gt hx.1) (Ioc 0 1)))
    (by
      change InjOn (fun t : ℝ => 1 / t) (Ioc 0 1)
      intro x _ y _ hxy
      exact inv_inj.1 (by simpa [one_div] using hxy))
    g

/-- Change-of-variables formula for `t ↦ 1 / t` from `Ici 1` back to `Ioc (0, 1]`. -/
public lemma integral_Ici_one_eq_integral_abs_deriv_smul (g : ℝ → ℂ) :
    ∫ s in Ici (1 : ℝ), g s = ∫ t in Ioc (0 : ℝ) 1, |(-1 / t ^ 2)| • g (1 / t) := by
  simpa using (integral_Ici_one_eq_integral_image_inv (g := g)).trans
    (integral_image_inv_eq_integral_abs_deriv_smul (g := g))

end InvChangeOfVariables

end

end SpherePacking.Integration
