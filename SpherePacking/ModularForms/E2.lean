module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import SpherePacking.ModularForms.SlashActionAuxil

/-!
# The Eisenstein Series `E₂`

Properties of the quasi-modular Eisenstein series `E₂`. The series itself is Mathlib's
`EisensteinSeries.E2`; this file introduces the notation `E₂` for it and records the pointwise
transformation laws used by the project.
-/

@[expose] public section

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups
open ArithmeticFunction

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
open scoped ArithmeticFunction.sigma

noncomputable section

/-- Notation for Mathlib's normalised weight `2` Eisenstein series `EisensteinSeries.E2`. -/
notation "E₂" => EisensteinSeries.E2

/-- E₂ is 1-periodic: E₂(z + 1) = E₂(z). -/
lemma E₂_periodic (z : ℍ) : E₂ ((1 : ℝ) +ᵥ z) = E₂ z := by
  rw [← modular_T_smul, EisensteinSeries.E2_T_smul]

lemma E₂_transform (z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
    E₂ z + 6 / (π * Complex.I * z) := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) z
  have h' : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
      E₂ z - (1 / (2 * riemannZeta 2)) * (2 * π * Complex.I / z) := by
    simpa [EisensteinSeries.D2_S, smul_eq_mul] using h
  rw [riemannZeta_two] at h'
  have hpi : (π : ℂ) ≠ 0 := by simp
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  calc
    (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
        E₂ z - 1 / (2 * (π ^ 2 / (6 : ℂ))) * (2 * π * Complex.I / z) := h'
    _ = E₂ z + 6 / (π * Complex.I * z) := by
      field_simp [hpi, hI, hz]
      ring_nf
      simp [Complex.I_sq, add_comm]

/-- E₂ transforms under S as: E₂(-1/z) = z² · (E₂(z) + 6/(πIz)). -/
lemma E₂_S_transform (z : ℍ) :
    E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) := by
  have h := E₂_transform z
  rw [SL_slash_apply, ModularGroup.denom_S, zpow_neg, zpow_two] at h
  have hz2 : (z : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero (ne_zero z) (ne_zero z)
  rw [sq, mul_comm]
  -- `only` is required here; without it simp rewrites the congrArg term structure
  simpa only [mul_assoc, inv_mul_cancel₀ hz2, mul_one] using congrArg (· * ((z : ℂ) * (z : ℂ))) h

lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * n * z) /
                        (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [EisensteinSeries.E2]
  simp [smul_eq_mul]
  rw [EisensteinSeries.G2_eq_tsum_cexp]
  rw [mul_sub]
  congr 1
  · rw [riemannZeta_two]
    have hpi : (π : ℂ) ≠ 0 := by simp
    field_simp
  · rw [← mul_assoc]
    congr 1
    · rw [riemannZeta_two]
      have hpi : (π : ℂ) ≠ 0 := by simp
      grind
    · calc
        ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * z) ^ (n : ℕ)
            = ∑' n : ℕ+, (n : ℂ) ^ 1 * cexp (2 * π * Complex.I * z) ^ (n : ℕ) /
                (1 - cexp (2 * π * Complex.I * z) ^ (n : ℕ)) := by
                  simpa [pow_one] using
                    (tsum_pow_div_one_sub_eq_tsum_sigma
                      (r := cexp (2 * π * Complex.I * z))
                        (UpperHalfPlane.norm_exp_two_pi_I_lt_one z) 1).symm
        _ = ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * n * z) /
            (1 - cexp (2 * π * Complex.I * n * z)) := by
              apply tsum_congr
              intro n
              have hpow : cexp (2 * π * Complex.I * n * z) =
                  cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
                rw [← Complex.exp_nat_mul]
                congr 1
                ring
              simp [pow_one, hpow]
