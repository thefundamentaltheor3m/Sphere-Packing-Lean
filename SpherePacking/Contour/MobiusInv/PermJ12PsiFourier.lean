module

public import Mathlib.Analysis.Complex.Exponential
public import SpherePacking.Contour.MobiusInv.Basic

/-! Shared algebraic lemma for the Möbius-change step in the `perm_J12` contour arguments.
Dimension-agnostic; the exponent `q` in the modular transformation law `ψ(-1/z) = -ψ(z)/z^q`
is the dimension-specific input. -/

namespace SpherePacking.Contour

/-- Algebraic identity used in the Mobius-change step of the `perm_J12` contour argument:
rewrites the Fourier-side factor `ψ z * ((I / z)^(q+2))` as a `-(deriv mobiusInv z)` term
using the modular transformation law for `ψ`. -/
public lemma permJ12_Ψ₁_fourier_eq_neg_deriv_mul
    {ψ : ℂ → ℂ} (A : ℂ) (q : ℕ) (r : ℝ) (z : ℂ) (hz : 0 < z.im)
    (hψ : ψ (mobiusInv z) = -(ψ z) / z ^ q)
    (hI : (Complex.I : ℂ) ^ (q + 2) = (1 : ℂ)) :
    ψ z * (((Complex.I : ℂ) / z) ^ (q + 2)) * Complex.exp (A * (r : ℂ) * ((-1 : ℂ) / z)) =
      -(deriv mobiusInv z) * (ψ (mobiusInv z) * Complex.exp (A * (r : ℂ) * mobiusInv z)) := by
  have hz0 : z ≠ 0 := fun hz0 => (ne_of_gt hz) (by simp [hz0])
  have hmob : mobiusInv z = (-1 : ℂ) / z := by simp [mobiusInv, div_eq_mul_inv]
  by_cases hψz : ψ z = 0
  · simp [hψz, show ψ (mobiusInv z) = 0 by simpa [hψz] using hψ, mul_assoc]
  simp [hmob, deriv_mobiusInv, show ψ ((-1 : ℂ) / z) = -(ψ z) / z ^ q by simpa [hmob] using hψ,
    div_pow, hI, mul_assoc, mul_comm, mul_left_comm]
  field_simp [hz0, hψz]; ring_nf

end SpherePacking.Contour
