module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FunProp

/-!
# Complex square root

This file defines `csqrt z = exp (log z / 2)` and proves basic calculus and power identities used
in modular-form computations.
-/

open UpperHalfPlane Complex

/-- The complex square root defined as `exp (log z / 2)`.

This is a convenient explicit choice of a square root on the slit plane.
-/
@[expose] public noncomputable def csqrt : ℂ → ℂ := fun a ↦ cexp ((1 / (2 : ℂ)) * log a)

private lemma coe_mem_slitPlane (z : ℍ) : (z : ℂ) ∈ slitPlane := by
  simpa [mem_slitPlane_iff] using
    (Or.inr (Ne.symm (ne_of_lt z.2)) : (0 < (z : ℂ).re) ∨ (z : ℂ).im ≠ 0)

/-- The derivative of the map `a ↦ exp (log a / 2)` on the upper half-plane. -/
public lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z := by
  have : (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ fun a ↦ (1 / 2 * Complex.log a) := rfl
  have hzz : (z : ℂ) ∈ slitPlane := coe_mem_slitPlane z
  rw [this, deriv_comp]
  · simp only [one_div, Complex.deriv_exp, deriv_const_mul_field', neg_mul, smul_eq_mul]
    rw [Complex.exp_neg]
    field_simp
    have hsq : cexp (Complex.log (z : ℂ) / 2) ^ 2 = cexp (Complex.log (z : ℂ)) := by
      rw [← Complex.exp_nat_mul]; grind
    simpa [hsq, (Complex.hasDerivAt_log hzz).deriv, Complex.exp_log <| ne_zero z]
      using Complex.mul_inv_cancel <| ne_zero z
  · fun_prop
  · apply DifferentiableAt.const_mul
    refine Complex.differentiableAt_log hzz

/-- The function `csqrt` is complex differentiable at points of the upper half-plane. -/
public lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z := by
  unfold csqrt
  simpa using
    ((Complex.differentiableAt_log (coe_mem_slitPlane z)).const_mul (1 / (2 : ℂ))).cexp

/-- The identity `(csqrt z)^24 = z^12` for `z ≠ 0`. -/
public lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have hmul : (24 : ℂ) * ((1 / (2 : ℂ)) * Complex.log z) = (12 : ℂ) * Complex.log z := by
    ring
  rw [hmul]
  simpa [Complex.exp_log hz] using (Complex.exp_nat_mul (Complex.log z) 12)

/-- The special value `(csqrt I)^24 = 1`. -/
public lemma csqrt_I : (csqrt (Complex.I)) ^ 24 = 1 := by
  have hI12 : (Complex.I : ℂ) ^ 12 = 1 := by
    simpa [Complex.I_pow_four] using (pow_mul (Complex.I : ℂ) 4 3)
  simpa [hI12] using csqrt_pow_24 (z := Complex.I) I_ne_zero
