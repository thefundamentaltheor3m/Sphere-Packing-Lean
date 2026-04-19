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

/-! ### Helper lemmas for D_slash

These micro-lemmas compute derivatives of the components in the slash action formula.-/

section DSlashHelpers

open ModularGroup

variable (γ : SL(2, ℤ))

/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  simp

/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  simp

/-- Differentiability of denom. -/
public lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]
  fun_prop

/-- Differentiability of num. -/
public lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]
  fun_prop

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
  -- The numerator collapses to `ad - bc = 1` by the determinant condition.
  have hnum_eq :
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * denom γ z -
          num γ z * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
    -- expand `num/denom` and cancel the `z` terms
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

/-- Derivative anomaly: `D` and the slash action. -/
public lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) =
      (D F ∣[k + 2] γ) -
        fun z : ℍ =>
          (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z := by
  ext z
  unfold D
  simp only [Pi.sub_apply]
  -- Key facts about denom and determinant (used multiple times below)
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  -- The derivative computation on ℂ using Filter.EventuallyEq.deriv_eq
  -- (F ∣[k] γ) ∘ ofComplex agrees with F(num/denom) * denom^(-k) on ℍ
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    -- Key: (γ • ⟨w, hw⟩ : ℂ) = num γ w / denom γ w
    congr 1
    · let gz : ℍ := γ • ⟨w, hw⟩
      have hsmul_coe : (gz : ℂ) = num γ w / denom γ w := by
        simpa [gz] using UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
      have hmob_im : 0 < (num γ w / denom γ w).im := by
        have : 0 < (gz : ℂ).im := by simpa using gz.im_pos
        simpa [hsmul_coe] using this
      congr 1
      ext
      · simpa [ofComplex_apply_of_im_pos hmob_im] using hsmul_coe
  rw [hcomp]
  -- Now apply product rule: deriv[f * g] = f * deriv[g] + deriv[f] * g
  -- where f(w) = (F ∘ ofComplex)(num w / denom w) and g(w) = denom(w)^(-k)
  --
  -- Setup differentiability for product rule
  have hdenom_ne : ∀ w : ℂ, w.im > 0 → denom γ w ≠ 0 := fun w hw =>
    UpperHalfPlane.denom_ne_zero γ ⟨w, hw⟩
  have hdiff_denom_zpow : DifferentiableAt ℂ (fun w => (denom γ w) ^ (-k)) z :=
    DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl (hdenom_ne z z.im_pos))
  -- For the F ∘ (num/denom) term, we need differentiability of the Möbius and F
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z :=
    (differentiableAt_num γ z).div (differentiableAt_denom γ z) (hdenom_ne z z.im_pos)
  -- The composition (F ∘ ofComplex) ∘ mobius is differentiable at z
  -- because mobius(z) is in ℍ and F is MDifferentiable
  have hmobius_in_H : (num γ z / denom γ z).im > 0 := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos z]
    exact (γ • z).im_pos
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    MDifferentiableAt_DifferentiableAt (hF ⟨num γ z / denom γ z, hmobius_in_H⟩)
  have hcomp_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
      (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
  have hdiff_F_mobius :
      DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    rw [hcomp_eq]
    exact DifferentiableAt.comp (z : ℂ) hdiff_F_comp hdiff_mobius
  rw [show (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * fun w => (denom γ w) ^ (-k)) by rfl]
  rw [deriv_mul hdiff_F_mobius hdiff_denom_zpow]
  -- Apply chain rule to (F ∘ ofComplex) ∘ mobius
  have hchain :
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z =
        deriv (F ∘ ofComplex) (num γ z / denom γ z) *
          deriv (fun w => num γ w / denom γ w) z := by
    rw [hcomp_eq, (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv]
  -- Substitute the micro-lemmas
  have hderiv_mob := deriv_moebius γ z
  have hderiv_zpow := deriv_denom_zpow γ k z
  rw [hchain, hderiv_mob, hderiv_zpow]
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  -- Relate (F ∘ ofComplex)(mob z) to F(γ • z)
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  simp only [ModularForm.SL_slash_apply, hF_mob, hmob_eq]
  have hpow_combine : 1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg, ← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  have hpow_m1 : (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  -- Rewrite powers on LHS
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ ofComplex) (num γ z / denom γ z)) (1 / denom γ z ^ 2) _]
    rw [hpow_combine, hpow_m1]
  -- Now the goal should be cleaner - distribute and simplify
  simp only [zpow_neg_one]
  ring

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
