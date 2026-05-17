module
public import SpherePacking.ModularForms.Derivative.SerreD

@[expose] public section

/-!
# Slash formulas for `D` and `E₂`

This file records the non-modular anomaly of the derivative operator `D` under the slash action
(`D_slash`) together with the companion transformation law for the quasi-modular Eisenstein
series `E₂` (`E₂_slash`). A small `DSlashHelpers` section computes the derivatives of numerator,
denominator and powers of the denominator that feed into these formulas.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function
open scoped Derivative

section DSlashHelpers

open ModularGroup

variable (γ : SL(2, ℤ))

/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Differentiability of denom. -/
public lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by simp only [denom]; fun_prop

/-- Differentiability of num. -/
public lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by simp only [num]; fun_prop

/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
Uses det(γ) = 1: a(cz+d) - c(az+b) = ad - bc = 1. -/
public lemma deriv_moebius (z : ℍ) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet :
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ 1 1) -
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ 1 0) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at this ⊢
    exact_mod_cast this
  rw [deriv_fun_div (differentiableAt_num γ z) (differentiableAt_denom γ z) hz,
      deriv_num, deriv_denom]
  have hnum_eq :
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * denom γ z -
          num γ z * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
    simp [num, denom, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, hdet]
  simp [hnum_eq, one_div]

/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
public lemma deriv_denom_zpow (k : ℤ) (z : ℍ) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hderiv_denom :
      HasDerivAt (fun w => denom γ w) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) (z : ℂ) := by
    simpa [deriv_denom (γ := γ)] using (differentiableAt_denom γ (z : ℂ)).hasDerivAt
  have hcomp := (hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)).comp (z : ℂ) hderiv_denom
  simpa [Function.comp, Int.cast_neg, mul_assoc, mul_left_comm, mul_comm] using hcomp.deriv

end DSlashHelpers

section DSlashAux

variable (γ : SL(2, ℤ))

/-- Local rewriting of `(F ∣[k] γ) ∘ ofComplex` as the product of `F ∘ ofComplex ∘ moebius` and
`denom γ ^ (-k)` on the open upper-half-plane set. -/
private lemma slash_comp_ofComplex_eventuallyEq (k : ℤ) (F : ℍ → ℂ) (z : ℍ) :
    ((F ∣[k] γ) ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k) := by
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
  rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
  let gz : ℍ := γ • ⟨w, hw⟩
  have hsmul_coe : (gz : ℂ) = num γ w / denom γ w := by
    simpa [gz] using UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
  have hmob_im : 0 < (num γ w / denom γ w).im := by
    have : 0 < (gz : ℂ).im := by simpa using gz.im_pos
    simpa [hsmul_coe] using this
  congr 2
  ext
  · simpa [ofComplex_apply_of_im_pos hmob_im] using hsmul_coe

/-- Power consolidations for the denominator: combine `1/d^2 * d^(-k)` and split `d^(-k-1)`. -/
private lemma denom_pow_combine (k : ℤ) (z : ℍ) :
    1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) ∧
    (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  refine ⟨?_, ?_⟩
  · rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg, ← zpow_add₀ hz]; congr 1; ring
  · rw [← zpow_add₀ hz]; congr 1; ring

/-- Product rule + chain rule for `(F ∘ ofComplex)(num/denom) * denom^(-k)` at `z : ℍ`. -/
private lemma deriv_F_moebius_mul_denom_zpow (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (z : ℍ) :
    deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z =
      deriv (F ∘ ofComplex) (num γ z / denom γ z) * (1 / (denom γ z) ^ 2) *
          (denom γ z) ^ (-k) +
        (F ∘ ofComplex) (num γ z / denom γ z) *
          ((-k : ℂ) * (γ 1 0 : ℂ) * (denom γ z) ^ (-k - 1)) := by
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  have hz_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdiff_denom_zpow : DifferentiableAt ℂ (fun w => (denom γ w) ^ (-k)) z :=
    DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl hz_ne)
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z :=
    (differentiableAt_num γ z).div (differentiableAt_denom γ z) hz_ne
  have hmobius_in_H : (num γ z / denom γ z).im > 0 := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos z]; exact (γ • z).im_pos
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    MDifferentiableAt_DifferentiableAt (hF ⟨num γ z / denom γ z, hmobius_in_H⟩)
  have hcomp_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
      (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
  rw [show (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * fun w => (denom γ w) ^ (-k)) by rfl,
      deriv_mul (hcomp_eq ▸ DifferentiableAt.comp (z : ℂ) hdiff_F_comp hdiff_mobius)
        hdiff_denom_zpow, hcomp_eq,
      (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv,
      deriv_moebius γ z, deriv_denom_zpow γ k z]

end DSlashAux

/-- Derivative anomaly: `D` and the slash action. -/
public lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) =
      (D F ∣[k + 2] γ) -
        fun z : ℍ =>
          (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z := by
  ext z
  unfold Derivative.normalizedDerivOfComplex
  simp only [Pi.sub_apply]
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  rw [(slash_comp_ofComplex_eventuallyEq γ k F z).deriv_eq,
      deriv_F_moebius_mul_denom_zpow γ k F hF z]
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  simp only [ModularForm.SL_slash_apply, hF_mob, hmob_eq]
  obtain ⟨hpow_combine, hpow_m1⟩ := denom_pow_combine γ k z
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ ofComplex) (num γ z / denom γ z)) (1 / denom γ z ^ 2) _]
    rw [hpow_combine, hpow_m1]
  simp only [zpow_neg_one]; ring

/-- Transformation law for `E₂` under the weight-2 slash action. -/
public lemma E₂_slash (γ : SL(2, ℤ)) :
    (E₂ ∣[(2 : ℤ)] γ) =
      E₂ + fun z : ℍ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
  ext z
  let a : ℂ := (1 / (2 * riemannZeta 2) : ℂ)
  have hG : (G₂ ∣[(2 : ℤ)] γ) z = G₂ z - D₂ γ z := by
    simpa using congrFun (G₂_transform γ) z
  have hcoeff : (-(a) * (2 * π * I)) = (12 : ℂ) * (2 * π * I)⁻¹ := by
    apply (mul_right_inj' two_pi_I_ne_zero).1
    dsimp [a]
    rw [riemannZeta_two]
    ring_nf
    have hpi : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp [hpi]
    ring_nf
    simp
  have hcorr : a * (-D₂ γ z) = (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
    have hcoeff' : a * (-(2 * π * I)) = (12 : ℂ) * (2 * π * I)⁻¹ := by
      simpa [a, mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg] using hcoeff
    rw [← hcoeff']
    simp [D₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, a, EisensteinSeries.D2]
  unfold G₂ at hG
  calc
    (E₂ ∣[(2 : ℤ)] γ) z = a * (G₂ z - D₂ γ z) := by
      simp [E₂, EisensteinSeries.E2, G₂, a, hG, Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = a * G₂ z + (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
      simpa [sub_eq_add_neg, mul_add, add_assoc, add_left_comm, add_comm] using
        congrArg (fun t => a * G₂ z + t) hcorr
    _ = E₂ z + (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) := by
      simp [E₂, EisensteinSeries.E2, G₂, Pi.smul_apply, smul_eq_mul, mul_assoc, a]
