module

public import Mathlib.Analysis.Complex.Exponential
public import SpherePacking.Contour.MobiusInv.Basic

/-!
Shared algebraic lemma for the Möbius-change step in the `perm_J12` contour arguments.

This is dimension-agnostic: the dimension-specific input is the exponent `q` in the modular
transformation law for `ψ` under `z ↦ -1/z`.
-/

namespace SpherePacking.Contour

/--
Algebraic identity used in the Mobius-change step of the `perm_J12` contour argument.

This rewrites the Fourier-side factor `ψ z * ((I / z)^(q+2))` as a `-(deriv mobiusInv z)` term,
using the modular transformation law for `ψ`.
-/
public lemma permJ12_Ψ₁_fourier_eq_neg_deriv_mul
    {ψ : ℂ → ℂ} (A : ℂ) (q : ℕ) (r : ℝ) (z : ℂ) (hz : 0 < z.im)
    (hψ : ψ (mobiusInv z) = -(ψ z) / z ^ q)
    (hI : (Complex.I : ℂ) ^ (q + 2) = (1 : ℂ)) :
    ψ z * (((Complex.I : ℂ) / z) ^ (q + 2)) * Complex.exp (A * (r : ℂ) * ((-1 : ℂ) / z)) =
      -(deriv mobiusInv z) * (ψ (mobiusInv z) * Complex.exp (A * (r : ℂ) * mobiusInv z)) := by
  have hmob : mobiusInv z = (-1 : ℂ) / z := by simp [mobiusInv, div_eq_mul_inv]
  have hz0 : z ≠ 0 := by
    intro hz0
    exact (ne_of_gt hz) (by simp [hz0])
  have hIz : ((Complex.I : ℂ) / z) ^ (q + 2) = (1 : ℂ) / z ^ (q + 2) := by
    simpa [hI] using (div_pow (Complex.I : ℂ) z (q + 2))
  have hden : (1 : ℂ) / z ^ (2 : ℕ) * ((1 : ℂ) / z ^ q) = (1 : ℂ) / z ^ (q + 2) := by
    simp [div_eq_mul_inv, pow_add, mul_left_comm, mul_comm]
  have hcore :
      ψ z * (((Complex.I : ℂ) / z) ^ (q + 2)) = -(deriv mobiusInv z) * ψ (mobiusInv z) := by
    calc
      ψ z * (((Complex.I : ℂ) / z) ^ (q + 2)) = ψ z * ((1 : ℂ) / z ^ (q + 2)) := by
        simp [hIz]
      _ = ψ z * ((1 : ℂ) / z ^ (2 : ℕ) * ((1 : ℂ) / z ^ q)) := by
        rw [← hden]
      _ = (1 : ℂ) / z ^ (2 : ℕ) * (ψ z * ((1 : ℂ) / z ^ q)) := by
        ac_rfl
      _ = (1 : ℂ) / z ^ (2 : ℕ) * (ψ z / z ^ q) := by
        simp [div_eq_mul_inv]
      _ = -(deriv mobiusInv z) * ψ (mobiusInv z) := by
        simp [deriv_mobiusInv, hψ, div_eq_mul_inv, mul_assoc, mul_comm]
  -- finish by matching the exponential factors
  calc
    ψ z * (((Complex.I : ℂ) / z) ^ (q + 2)) * Complex.exp (A * (r : ℂ) * ((-1 : ℂ) / z)) =
        (-(deriv mobiusInv z) * ψ (mobiusInv z)) * Complex.exp (A * (r : ℂ) * ((-1 : ℂ) / z)) := by
      simp [hcore, mul_assoc]
    _ = -(deriv mobiusInv z) * (ψ (mobiusInv z) * Complex.exp (A * (r : ℂ) * mobiusInv z)) := by
      simp [hmob, mul_assoc]

end SpherePacking.Contour
