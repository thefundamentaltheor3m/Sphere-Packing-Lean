import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction


noncomputable def csqrt : ℂ → ℂ :=  (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a)))

lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z:= by
  have :  (fun a ↦ cexp (1 / 2 * Complex.log a)) =  cexp ∘ (fun a ↦ (1 / 2 * Complex.log a)) := by
    ext z
    simp
  have hzz : ↑z ∈ slitPlane := by
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp only [UpperHalfPlane.coe] at hz
    exact Ne.symm (ne_of_lt hz)
  rw [this, deriv_comp]
  simp
  rw [Complex.exp_neg]
  field_simp
  rw [show cexp (Complex.log ↑z / 2) * deriv Complex.log ↑z * (2 * cexp (Complex.log ↑z / 2)) =
    cexp (Complex.log ↑z / 2) * (cexp (Complex.log ↑z / 2)) * 2 * deriv Complex.log ↑z by ring]
  rw [← Complex.exp_add]
  ring_nf
  rw [Complex.exp_log]
  have hl := (Complex.hasDerivAt_log (z := z) hzz).deriv
  rw [hl]
  field_simp [ne_zero z]
  · apply ne_zero z
  · fun_prop
  · apply DifferentiableAt.const_mul
    refine Complex.differentiableAt_log hzz

lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z := by
  unfold csqrt
  apply DifferentiableAt.cexp
  apply DifferentiableAt.const_mul
  apply Complex.differentiableAt_log
  rw [@mem_slitPlane_iff]
  right
  have hz := z.2
  simp only [UpperHalfPlane.coe] at hz
  exact Ne.symm (ne_of_lt hz)


lemma csqrt_I : (csqrt (Complex.I)) ^ 24  = 1 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_log]
  have hi4 := Complex.I_pow_four
  have : Complex.I ^ 12 = (Complex.I ^ 4) ^ 3 :=by
    rw [← @npow_mul]
  rw [this, hi4]
  simp
  exact I_ne_zero

lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul, Complex.exp_log hz]
