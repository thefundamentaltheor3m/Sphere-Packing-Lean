module
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Exponential
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.ForMathlib.ExpPiIMulMulI


/-!
# Finite-difference identities for `a'`

This file isolates the imaginary-axis specializations used by `StripBounds` and
`TailDeformation`. The heavy modular-form input is the finite-difference identity for `φ₀`
proved in `SpherePacking.MagicFunction.a.SpecialValues`.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped UpperHalfPlane
open UpperHalfPlane ModularGroup

open MagicFunction.a.ComplexIntegrands

/-- Shift `Φ₁'` by `-1` and rewrite it in terms of `Φ₅'` at the point `it`. -/
public lemma Φ₁'_shift_left (u t : ℝ) :
    Φ₁' u ((-1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₁', Φ₅', mul_add, div_eq_mul_inv, Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]

/-- Shift `Φ₃'` by `+1` and rewrite it in terms of `Φ₅'` at the point `it`. -/
public lemma Φ₃'_shift_right (u t : ℝ) :
    Φ₃' u ((1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₃', Φ₅', mul_add, add_assoc, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg,
    div_eq_mul_inv, Complex.exp_add]

/-- Identify `Φ₅'` on the imaginary axis with `-aLaplaceIntegrand`. -/
public lemma Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u t : ℝ) :
    Φ₅' u ((t : ℂ) * Complex.I) = -aLaplaceIntegrand u t := by
  have harg : (-1 : ℂ) / ((t : ℂ) * Complex.I) = (Complex.I : ℂ) / (t : ℂ) := by
    simp [div_eq_mul_inv]
  have hpow : ((t : ℂ) * Complex.I) ^ (2 : ℕ) = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [mul_pow]; simp [pow_two, Complex.I_mul_I]
  dsimp [MagicFunction.a.ComplexIntegrands.Φ₅', aLaplaceIntegrand]
  rw [harg, hpow, show Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
    (Real.exp (-Real.pi * u * t) : ℂ) by
    simp [show (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) = (-Real.pi * u * t : ℂ)
      from by ring_nf; simp [Complex.I_sq]]]
  ring_nf

/-- Imaginary-axis specialization of the finite-difference identity for `φ₀`. -/
public lemma Φ_finite_difference_imag_axis {u t : ℝ} (ht : 0 < t) :
    Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) + Φ₄' u ((t : ℂ) * Complex.I) =
      2 * Φ₆' u ((t : ℂ) * Complex.I) := by
  let zH : ℍ := UpperHalfPlane.mk (Complex.I * t) (by simp [ht])
  have hfd := MagicFunction.a.SpecialValues.φ₀_finite_difference (z := zH)
  have hcore :
      φ₀'' ((-1 : ℂ) / (((1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
          - 2 * (φ₀'' ((-1 : ℂ) / (zH : ℂ)) * ((zH : ℂ) ^ (2 : ℕ)))
          + φ₀'' ((-1 : ℂ) / (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
        = (2 : ℂ) * φ₀'' (zH : ℂ) := by
    have hS (w : ℍ) : φ₀ (ModularGroup.S • w) = φ₀'' ((-1 : ℂ) / (w : ℂ)) := by
      have hcoe : ((ModularGroup.S • w : ℍ) : ℂ) = (-1 : ℂ) / (w : ℂ) := by
        simpa using ModularGroup.coe_S_smul (z := w)
      calc φ₀ (ModularGroup.S • w) = φ₀'' ((ModularGroup.S • w : ℍ) : ℂ) :=
            (φ₀''_coe_upperHalfPlane (z := ModularGroup.S • w)).symm
        _ = φ₀'' ((-1 : ℂ) / (w : ℂ)) := by rw [hcoe]
    rw [hS ((1 : ℝ) +ᵥ zH), hS zH, hS ((-1 : ℝ) +ᵥ zH),
      show φ₀ zH = φ₀'' (zH : ℂ) from (φ₀''_coe_upperHalfPlane (z := zH)).symm] at hfd
    simpa [mul_assoc] using hfd
  have hzH : (zH : ℂ) = (t : ℂ) * Complex.I := by simp [zH, mul_comm]
  set e : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ) * (zH : ℂ))
  set core : ℂ :=
      φ₀'' ((-1 : ℂ) / (((1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
          - 2 * (φ₀'' ((-1 : ℂ) / (zH : ℂ)) * ((zH : ℂ) ^ (2 : ℕ)))
          + φ₀'' ((-1 : ℂ) / (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
    with hcore_def
  have hcore_eq : core = (2 : ℂ) * φ₀'' (zH : ℂ) := by simpa [core, hcore_def] using hcore
  have hL :
      Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) + Φ₄' u ((t : ℂ) * Complex.I) =
        core * e := by
    rw [hcore_def]
    simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
      MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃',
      MagicFunction.a.ComplexIntegrands.Φ₅', hzH, e, sub_eq_add_neg]
    ring_nf
  have hR : 2 * Φ₆' u ((t : ℂ) * Complex.I) = ((2 : ℂ) * φ₀'' (zH : ℂ)) * e := by
    simp [MagicFunction.a.ComplexIntegrands.Φ₆', hzH, e, mul_assoc, mul_left_comm, mul_comm]
  simpa [hL, hR] using congrArg (fun w : ℂ => w * e) hcore_eq

end MagicFunction.g.CohnElkies.IntegralReps
