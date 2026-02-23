module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.ModularForms.SlashActions

public import SpherePacking.ModularForms.Derivative
public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.ModularForms.QExpansion
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.ModularForms.Lv1Lv2Identities
public import SpherePacking.ModularForms.ThetaDerivIdentities
import SpherePacking.Tactic.NormNumI
import SpherePacking.Tactic.FunPropExt

/-!
# The modular forms `F` and `G`

This file defines the key modular forms `F` and `G` (and related auxiliary functions) used in the
`SpherePacking.ModularForms.FG` development, together with basic facts and the modular linear
differential equations they satisfy.

## Main declarations
* `F`, `G`
* `L₁₀`, `SerreDer_22_L₁₀`
* `FReal`, `GReal`, `FmodGReal`
* `MLDE_F`, `MLDE_G`
-/


open scoped Real Manifold Topology ArithmeticFunction.sigma ModularForm MatrixGroups
open Filter Complex UpperHalfPlane ModularForm

-- Ensure the `SL(2,ℤ)` Möbius action on `ℍ` is available for the local computations below.
noncomputable local instance : MulAction SL(2, ℤ) ℍ := UpperHalfPlane.SLAction (R := ℤ)

/-- The function `F = (E₂ * E₄ - E₆)^2` on the upper half-plane. -/
@[expose] public noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

/-- The function `G`, a polynomial expression in the theta combinations `H₂` and `H₄`. -/
@[expose] public noncomputable def G := H₂ ^ 3 * (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2)

/-- A convenient abbreviation for `-D E₂`. -/
@[expose] public noncomputable def negDE₂ := - (D E₂)

/-- The discriminant modular form `Delta`, viewed as a function `ℍ → ℂ`. -/
@[expose] public noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

/-- The combination `(D F) * G - F * (D G)` used in the monotonicity argument. -/
@[expose] public noncomputable def L₁₀ := (D F) * G - F * (D G)

/-- The Serre derivative `serre_D 22` applied to `L₁₀`. -/
@[expose] public noncomputable def SerreDer_22_L₁₀ := serre_D 22 L₁₀

/-- The restriction of `F` to the imaginary axis, viewed as a real-valued function. -/
@[expose] public noncomputable def FReal (t : ℝ) : ℝ := (F.resToImagAxis t).re

/-- The restriction of `G` to the imaginary axis, viewed as a real-valued function. -/
@[expose] public noncomputable def GReal (t : ℝ) : ℝ := (G.resToImagAxis t).re

/-- The ratio `FReal / GReal` on the imaginary axis. -/
@[expose] public noncomputable def FmodGReal (t : ℝ) : ℝ := (FReal t) / (GReal t)

private theorem resToImagAxis_eq_of_real (F : ℍ → ℂ) (hF : ResToImagAxis.Real F) {t : ℝ}
    (ht : 0 < t) : F.resToImagAxis t = ((F.resToImagAxis t).re : ℂ) := by
  have him : (ResToImagAxis F t).im = 0 := by
    simpa [Function.resToImagAxis_apply] using hF t ht
  apply Complex.ext <;> simp [Function.resToImagAxis_apply, him]

/-- On the imaginary axis, `F` takes real values (so it agrees with `FReal`). -/
public theorem F_eq_FReal {t : ℝ} (ht : 0 < t) : F.resToImagAxis t = FReal t := by
  have hbase : ResToImagAxis.Real (E₂ * E₄.toFun - E₆.toFun) :=
    ResToImagAxis.Real.sub (ResToImagAxis.Real.mul E₂_imag_axis_real E₄_imag_axis_real)
      E₆_imag_axis_real
  have hF : ResToImagAxis.Real F := by
    simpa [F, pow_two] using ResToImagAxis.Real.mul hbase hbase
  simpa [FReal] using resToImagAxis_eq_of_real (F := F) hF ht

/-- On the imaginary axis, `G` takes real values (so it agrees with `GReal`). -/
public theorem G_eq_GReal {t : ℝ} (ht : 0 < t) : G.resToImagAxis t = GReal t := by
  have hconst (c : ℝ) : ResToImagAxis.Real (fun _ : ℍ => (c : ℂ)) := by
    intro u hu
    simp [Function.resToImagAxis, ResToImagAxis, hu]
  have hH2_sq : ResToImagAxis.Real (H₂ ^ 2) := by
    simpa [pow_two] using ResToImagAxis.Real.mul H₂_imag_axis_real H₂_imag_axis_real
  have hH2_cube : ResToImagAxis.Real (H₂ ^ 3) := by
    simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc] using
      ResToImagAxis.Real.mul hH2_sq H₂_imag_axis_real
  have hH4_sq : ResToImagAxis.Real (H₄ ^ 2) := by
    simpa [pow_two] using ResToImagAxis.Real.mul H₄_imag_axis_real H₄_imag_axis_real
  have hpoly : ResToImagAxis.Real (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2) := by
    refine ResToImagAxis.Real.add
      (ResToImagAxis.Real.add ?_ ?_) ?_
    · exact ResToImagAxis.Real.mul (hconst 2) hH2_sq
    · -- `5 * H₂ * H₄ = 5 * (H₂ * H₄)`
      simpa [mul_assoc] using
        ResToImagAxis.Real.mul (hconst 5)
          (ResToImagAxis.Real.mul H₂_imag_axis_real H₄_imag_axis_real)
    · exact ResToImagAxis.Real.mul (hconst 5) hH4_sq
  have hG : ResToImagAxis.Real G := by
    simpa [G, mul_assoc] using ResToImagAxis.Real.mul hH2_cube hpoly
  simpa [GReal] using resToImagAxis_eq_of_real (F := G) hG ht

/-- Relate `FmodGReal` to the complex quotient `F/G` on the imaginary axis. -/
public theorem FmodG_eq_FmodGReal {t : ℝ} (ht : 0 < t) :
    FmodGReal t = (F.resToImagAxis t) / (G.resToImagAxis t) := by
  have hF := F_eq_FReal (t := t) ht
  have hG := G_eq_GReal (t := t) ht
  change (FmodGReal t : ℂ) = (F.resToImagAxis t) / (G.resToImagAxis t)
  rw [hF, hG]
  simp [FmodGReal, FReal, GReal, Complex.ofReal_div]

/-- The function `F` is holomorphic on the upper half-plane. -/
public theorem F_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  have h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun - E₆.toFun) :=
    MDifferentiable.sub (MDifferentiable.mul E₂_holo' E₄.holo') E₆.holo'
  simpa [F, pow_two] using MDifferentiable.mul h h

/-- The function `G` is holomorphic on the upper half-plane. -/
public theorem G_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
  have : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  simpa [G] using
    (by fun_prop : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 3 * (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2)))

/-- The function `L₁₀` is holomorphic on the upper half-plane. -/
public theorem L₁₀_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) L₁₀ := by
  simpa [L₁₀] using
    (MDifferentiable.mul (D_differentiable F_holo) G_holo).sub
      (MDifferentiable.mul F_holo (D_differentiable G_holo))

/-- The restriction `FReal` is differentiable on the positive imaginary axis. -/
public theorem FReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ FReal t := by
  simpa [FReal] using
    (Complex.reCLM.differentiableAt.comp t (ResToImagAxis.Differentiable F F_holo t ht))

/-- The restriction `GReal` is differentiable on the positive imaginary axis. -/
public theorem GReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ GReal t := by
  simpa [GReal] using
    (Complex.reCLM.differentiableAt.comp t (ResToImagAxis.Differentiable G G_holo t ht))

/-! Auxiliary Serre-derivative computations used for the MLDEs below. -/

lemma serre_D_smulC (k c : ℂ) (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    serre_D k (c • F) = c • (serre_D k F) := by
  ext z
  simp [serre_D, D_smul c F hF, smul_eq_mul, mul_assoc]
  ring

lemma serre_D_addC (k : ℂ) (F G : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp [serre_D, D_add F G hF hG, Pi.add_apply]
  ring

lemma serre_D_E₂_mul_E₄_sub_E₆ :
    serre_D 5 (E₂ * E₄.toFun - E₆.toFun) =
      ((-5 : ℂ) * 12⁻¹) • (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  ext z
  have hDE₄ : D (E₄ : ℍ → ℂ) = 3⁻¹ * (E₂ * (E₄ : ℍ → ℂ) - (E₆ : ℍ → ℂ)) := by
    simpa [SlashInvariantForm.toFun_eq_coe] using (ramanujan_E₄ : D E₄.toFun = _)
  have hDE₆ : D (E₆ : ℍ → ℂ) = 2⁻¹ * (E₂ * (E₆ : ℍ → ℂ) - (E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ)) := by
    simpa [SlashInvariantForm.toFun_eq_coe] using (ramanujan_E₆ : D E₆.toFun = _)
  have hDsub :
      D (E₂ * (E₄ : ℍ → ℂ) - (E₆ : ℍ → ℂ)) z =
        D (E₂ * (E₄ : ℍ → ℂ)) z - D (E₆ : ℍ → ℂ) z := by
    simpa [Pi.sub_apply] using congrArg (fun f : ℍ → ℂ => f z)
      (D_sub (E₂ * (E₄ : ℍ → ℂ)) (E₆ : ℍ → ℂ) (MDifferentiable.mul E₂_holo' E₄.holo') E₆.holo')
  have hDmul :
      D (E₂ * (E₄ : ℍ → ℂ)) z =
        (D E₂ * (E₄ : ℍ → ℂ) + E₂ * D (E₄ : ℍ → ℂ)) z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) (D_mul E₂ (E₄ : ℍ → ℂ) E₂_holo' E₄.holo')
  simp [serre_D, hDsub, hDmul, hDE₄, hDE₆, ramanujan_E₂, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm]
  ring_nf

lemma serre_D_E₂_mul_E₆_sub_E₄_sq :
    serre_D 7 (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) =
      ((-7 : ℂ) * 12⁻¹) • (E₄.toFun * (E₂ * E₄.toFun - E₆.toFun)) := by
  ext z
  have hDE₄ : D (E₄ : ℍ → ℂ) = 3⁻¹ * (E₂ * (E₄ : ℍ → ℂ) - (E₆ : ℍ → ℂ)) := by
    simpa [SlashInvariantForm.toFun_eq_coe] using (ramanujan_E₄ : D E₄.toFun = _)
  have hDE₆ : D (E₆ : ℍ → ℂ) = 2⁻¹ * (E₂ * (E₆ : ℍ → ℂ) - (E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ)) := by
    simpa [SlashInvariantForm.toFun_eq_coe] using (ramanujan_E₆ : D E₆.toFun = _)
  have hDsub :
      D (E₂ * (E₆ : ℍ → ℂ) - (E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ)) z =
        D (E₂ * (E₆ : ℍ → ℂ)) z - D ((E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ)) z := by
    simpa [Pi.sub_apply] using congrArg (fun f : ℍ → ℂ => f z)
      (D_sub (E₂ * (E₆ : ℍ → ℂ)) ((E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ))
        (MDifferentiable.mul E₂_holo' E₆.holo') (MDifferentiable.mul E₄.holo' E₄.holo'))
  have hDmul₁ :
      D (E₂ * (E₆ : ℍ → ℂ)) z =
        (D E₂ * (E₆ : ℍ → ℂ) + E₂ * D (E₆ : ℍ → ℂ)) z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) (D_mul E₂ (E₆ : ℍ → ℂ) E₂_holo' E₆.holo')
  have hDmul₂ :
      D ((E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ)) z =
        (D (E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ) + (E₄ : ℍ → ℂ) * D (E₄ : ℍ → ℂ)) z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z)
      (D_mul (E₄ : ℍ → ℂ) (E₄ : ℍ → ℂ) E₄.holo' E₄.holo')
  simp [serre_D, hDsub, hDmul₁, hDmul₂, hDE₄, hDE₆, ramanujan_E₂, smul_eq_mul, mul_assoc,
    mul_left_comm, mul_comm]
  ring_nf

/-!
## Modular linear differential equations
-/

/-- Modular linear differential equation satisfied by `F`. -/
public theorem MLDE_F :
    serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * E₄.toFun * F + 7200 * Δ_fun * negDE₂ := by
  -- Use the shorthand from the blueprint: `A = E₂E₄ - E₆` and `B = E₂E₆ - E₄²`.
  set A := E₂ * E₄.toFun - E₆.toFun with hA
  set B := E₂ * E₆.toFun - E₄.toFun * E₄.toFun with hB
  have hA_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) A := by
    simpa [hA] using (MDifferentiable.mul E₂_holo' E₄.holo').sub E₆.holo'
  have hB_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := by
    simpa [hB] using (
      MDifferentiable.mul E₂_holo' E₆.holo').sub (MDifferentiable.mul E₄.holo' E₄.holo')
  have hF : F = A ^ 2 := by simp [F, hA]
  -- First compute `∂₁₀ F = - (5/6) A B`.
  have hS5 : serre_D 5 A = ((-5 : ℂ) * 12⁻¹) • B := by simpa [hA, hB] using serre_D_E₂_mul_E₄_sub_E₆
  have hSerre10 : serre_D 10 F = ((-5 : ℂ) * 6⁻¹) • (A * B) := by
    have hmul : serre_D 10 (A * A) = (serre_D 5 A) * A + A * (serre_D 5 A) := by
      simpa [show (5 : ℂ) + 5 = 10 by norm_num] using
        (serre_D_mul (k₁ := (5 : ℤ)) (k₂ := (5 : ℤ)) A A hA_holo hA_holo)
    rw [hF, pow_two, hmul]
    simp only [hS5, neg_mul, _root_.neg_smul]
    -- Clear the remaining scalar arithmetic pointwise.
    ext z
    simp [smul_eq_mul]
    ring_nf
  -- Now compute `∂₁₂ ∂₁₀ F` using the product rule and the two auxiliary identities.
  have hAB_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (A * B) := MDifferentiable.mul hA_holo hB_holo
  have hS7 : serre_D 7 B = ((-7 : ℂ) * 12⁻¹) • (E₄.toFun * A) := by
    simpa [hA, hB, mul_assoc] using serre_D_E₂_mul_E₆_sub_E₄_sq
  have hAB : serre_D 12 (A * B) = (serre_D 5 A) * B + A * (serre_D 7 B) := by
    simpa [show (5 : ℂ) + 7 = 12 by norm_num] using
      (serre_D_mul (k₁ := (5 : ℤ)) (k₂ := (7 : ℤ)) A B hA_holo hB_holo)
  -- Rewrite `-D E₂` in the form used in the blueprint.
  have hnegDE₂' : negDE₂ = 12⁻¹ * (E₄.toFun - E₂ * E₂) := by
    ext w
    simp [negDE₂, ramanujan_E₂, sub_eq_add_neg]
    ring_nf
  -- Compute `∂₁₂(∂₁₀F)` and reduce to a pointwise polynomial identity.
  rw [hSerre10]
  -- Pull the scalar out.
  rw [serre_D_smulC (k := (12 : ℂ)) (c := ((-5 : ℂ) * 6⁻¹)) (A * B) hAB_holo]
  -- Expand `serre_D 12 (A * B)` via the product rule.
  rw [hAB]
  -- Rewrite `serre_D 5 A` and `serre_D 7 B` using the auxiliary identities.
  rw [hS5, hS7]
  -- Substitute the two auxiliary identities.
  -- From here on, it is just algebra in the commutative ring of pointwise functions.
  ext z
  simp [hF, hA, hB, Δ_fun, hnegDE₂', smul_eq_mul]
  ring_nf

/-- Modular linear differential equation satisfied by `G`. -/
public theorem MLDE_G :
    serre_D 12 (serre_D 10 G) = 5 * 6⁻¹ * E₄.toFun * G - 640 * Δ_fun * H₂ := by
  -- The blueprint statement is `∂₁₂∂₁₀ G - (5/6)E₄·G = -640·Δ·H₂`.
  -- We compute both sides using the product rule for `serre_D` and the theta-derivative identities.
  have hH2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  have hH2_sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 2) := by fun_prop
  have hH2_cube : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 3) := by fun_prop
  have hH2_pow4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 4) := by fun_prop
  have hH2_pow5 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 5) := by fun_prop
  have hH4_sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 2) := by fun_prop
  have hH4_cube : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 3) := by fun_prop
  have hS4_H2_sq :
      serre_D 4 (H₂ ^ 2) = (1 / 3 : ℂ) • (H₂ ^ 3) + (2 / 3 : ℂ) • (H₂ ^ 2 * H₄) := by
    have hmul' : serre_D 4 (H₂ ^ 2) = (serre_D 2 H₂) * H₂ + H₂ * (serre_D 2 H₂) := by
      simpa [pow_two, show (2 : ℂ) + 2 = 4 by norm_num] using
        (serre_D_mul (k₁ := (2 : ℤ)) (k₂ := (2 : ℤ)) H₂ H₂ hH2 hH2)
    rw [hmul', serre_D_two_H₂]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS6_H2_cube : serre_D 6 (H₂ ^ 3) = (1 / 2 : ℂ) • (H₂ ^ 4) + H₂ ^ 3 * H₄ := by
    have hmul' : serre_D 6 (H₂ ^ 3) = (serre_D 4 (H₂ ^ 2)) * H₂ + (H₂ ^ 2) * (serre_D 2 H₂) := by
      simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc,
        show (4 : ℂ) + 2 = 6 by norm_num] using
        (serre_D_mul (k₁ := (4 : ℤ)) (k₂ := (2 : ℤ)) (H₂ ^ 2) H₂ hH2_sq hH2)
    rw [hmul', hS4_H2_sq, serre_D_two_H₂]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS8_H2_pow4 : serre_D 8 (H₂ ^ 4) = (2 / 3 : ℂ) • (H₂ ^ 5) + (4 / 3 : ℂ) • (H₂ ^ 4 * H₄) := by
    have hmul' : serre_D 8 (H₂ ^ 4) = (serre_D 6 (H₂ ^ 3)) * H₂ + (H₂ ^ 3) * (serre_D 2 H₂) := by
      simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc,
        show (6 : ℂ) + 2 = 8 by norm_num] using
        (serre_D_mul (k₁ := (6 : ℤ)) (k₂ := (2 : ℤ)) (H₂ ^ 3) H₂ hH2_cube hH2)
    rw [hmul', hS6_H2_cube, serre_D_two_H₂]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS10_H2_pow5 :
      serre_D 10 (H₂ ^ 5) = (5 / 6 : ℂ) • (H₂ ^ 6) + (5 / 3 : ℂ) • (H₂ ^ 5 * H₄) := by
    have hmul' : serre_D 10 (H₂ ^ 5) = (serre_D 8 (H₂ ^ 4)) * H₂ + (H₂ ^ 4) * (serre_D 2 H₂) := by
      simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc,
        show (8 : ℂ) + 2 = 10 by norm_num] using
        (serre_D_mul (k₁ := (8 : ℤ)) (k₂ := (2 : ℤ)) (H₂ ^ 4) H₂ hH2_pow4 hH2)
    rw [hmul', hS8_H2_pow4, serre_D_two_H₂]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS4_H4_sq :
      serre_D 4 (H₄ ^ 2) = (-2 / 3 : ℂ) • (H₂ * H₄ ^ 2) + (-1 / 3 : ℂ) • (H₄ ^ 3) := by
    have hmul' : serre_D 4 (H₄ ^ 2) = (serre_D 2 H₄) * H₄ + H₄ * (serre_D 2 H₄) := by
      simpa [pow_two, show (2 : ℂ) + 2 = 4 by norm_num] using
        (serre_D_mul (k₁ := (2 : ℤ)) (k₂ := (2 : ℤ)) H₄ H₄ hH4 hH4)
    rw [hmul', serre_D_two_H₄]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS6_H4_cube :
      serre_D 6 (H₄ ^ 3) = (-1 : ℂ) • (H₂ * H₄ ^ 3) + (-1 / 2 : ℂ) • (H₄ ^ 4) := by
    have hmul' : serre_D 6 (H₄ ^ 3) = (serre_D 4 (H₄ ^ 2)) * H₄ + (H₄ ^ 2) * (serre_D 2 H₄) := by
      simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc,
        show (4 : ℂ) + 2 = 6 by norm_num] using
        (serre_D_mul (k₁ := (4 : ℤ)) (k₂ := (2 : ℤ)) (H₄ ^ 2) H₄ hH4_sq hH4)
    rw [hmul', hS4_H4_sq, serre_D_two_H₄]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hH2_mul_H4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ * H₄) := hH2.mul hH4
  set hP : UpperHalfPlane → ℂ :=
      2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2 with hP_def
  have hP_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) hP := by
    simpa [hP_def] using (by
      fun_prop : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (2 * H₂ ^ 2 + 5 * H₂ * H₄ + 5 * H₄ ^ 2))
  have hS4_H2_mul_H4 : serre_D 4 (H₂ * H₄) = (1 / 6 : ℂ) • (H₂ * H₄ ^ 2 - H₂ ^ 2 * H₄) := by
    have hmul' : serre_D 4 (H₂ * H₄) = (serre_D 2 H₂) * H₄ + H₂ * (serre_D 2 H₄) := by
      simpa [show (2 : ℂ) + 2 = 4 by norm_num] using
        (serre_D_mul (k₁ := (2 : ℤ)) (k₂ := (2 : ℤ)) H₂ H₄ hH2 hH4)
    rw [hmul', serre_D_two_H₂, serre_D_two_H₄]
    ext z
    simp [smul_eq_mul, pow_two, mul_assoc, mul_left_comm, mul_comm, Pi.mul_apply, Pi.add_apply,
      Pi.sub_apply]
    ring_nf
  have hS4_P :
      serre_D 4 hP =
        (2 / 3 : ℂ) • (H₂ ^ 3) + (1 / 2 : ℂ) • (H₂ ^ 2 * H₄) +
          (-5 / 2 : ℂ) • (H₂ * H₄ ^ 2) + (-5 / 3 : ℂ) • (H₄ ^ 3) := by
    -- Rewrite `hP` as a sum and use linearity + the auxiliary identities above.
    set T1 : UpperHalfPlane → ℂ := (2 : ℂ) • (H₂ ^ 2)
    set T2 : UpperHalfPlane → ℂ := (5 : ℂ) • (H₂ * H₄)
    set T3 : UpperHalfPlane → ℂ := (5 : ℂ) • (H₄ ^ 2)
    have hT1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T1 := hH2_sq.const_smul _
    have hT2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T2 := hH2_mul_H4.const_smul _
    have hT3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T3 := hH4_sq.const_smul _
    have hT12 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (T1 + T2) := hT1.add hT2
    have hP_eq : hP = T1 + T2 + T3 := by
      ext z
      simp [hP_def, T1, T2, T3, smul_eq_mul, Pi.add_apply, Pi.mul_apply, mul_assoc, add_assoc]
    -- Expand `serre_D 4` over the sum.
    rw [hP_eq]
    rw [serre_D_addC (k := (4 : ℂ)) (T1 + T2) T3 hT12 hT3]
    rw [serre_D_addC (k := (4 : ℂ)) T1 T2 hT1 hT2]
    -- Reassociate for convenience.
    simp only [one_div]
    -- Pull scalars out of `serre_D` and substitute the computed monomial identities.
    rw [serre_D_smulC (k := (4 : ℂ)) (c := (2 : ℂ)) (H₂ ^ 2) hH2_sq]
    rw [serre_D_smulC (k := (4 : ℂ)) (c := (5 : ℂ)) (H₂ * H₄) hH2_mul_H4]
    rw [serre_D_smulC (k := (4 : ℂ)) (c := (5 : ℂ)) (H₄ ^ 2) hH4_sq]
    rw [hS4_H2_sq, hS4_H2_mul_H4, hS4_H4_sq]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    ring_nf
  -- Now compute `serre_D 10 G` and then apply `serre_D 12` one more time.
  have hS10_G :
      serre_D 10 G =
        (5 / 3 : ℂ) • (H₂ ^ 6) + (5 : ℂ) • (H₂ ^ 5 * H₄) + (5 : ℂ) • (H₂ ^ 4 * H₄ ^ 2) +
          (10 / 3 : ℂ) • (H₂ ^ 3 * H₄ ^ 3) := by
    have hmul' :
        serre_D 10 G = (serre_D 6 (H₂ ^ 3)) * hP + (H₂ ^ 3) * (serre_D 4 hP) := by
      simpa [G, hP_def, mul_assoc, show (6 : ℂ) + 4 = 10 by norm_num] using
        (serre_D_mul (k₁ := (6 : ℤ)) (k₂ := (4 : ℤ)) (H₂ ^ 3) hP hH2_cube hP_holo)
    rw [hmul', hS6_H2_cube, hS4_P]
    ext z
    simp [hP_def, smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS12_H2_pow6 : serre_D 12 (H₂ ^ 6) = (H₂ ^ 7) + (2 : ℂ) • (H₂ ^ 6 * H₄) := by
    have hmul' :
        serre_D 12 (H₂ ^ 6) = (serre_D 10 (H₂ ^ 5)) * H₂ + (H₂ ^ 5) * (serre_D 2 H₂) := by
      simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc,
        show (10 : ℂ) + 2 = 12 by norm_num] using
        (serre_D_mul (k₁ := (10 : ℤ)) (k₂ := (2 : ℤ)) (H₂ ^ 5) H₂ hH2_pow5 hH2)
    rw [hmul', hS10_H2_pow5, serre_D_two_H₂]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS12_H2pow5_mul_H4 :
      serre_D 12 (H₂ ^ 5 * H₄) = (1 / 2 : ℂ) • (H₂ ^ 6 * H₄) + (3 / 2 : ℂ) • (H₂ ^ 5 * H₄ ^ 2) := by
    have hmul' :
        serre_D 12 (H₂ ^ 5 * H₄) = (serre_D 10 (H₂ ^ 5)) * H₄ + (H₂ ^ 5) * (serre_D 2 H₄) := by
      simpa [show (10 : ℂ) + 2 = 12 by norm_num] using
        (serre_D_mul (k₁ := (10 : ℤ)) (k₂ := (2 : ℤ)) (H₂ ^ 5) H₄ hH2_pow5 hH4)
    rw [hmul', hS10_H2_pow5, serre_D_two_H₄]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS12_H2pow4_mul_H4sq :
      serre_D 12 (H₂ ^ 4 * H₄ ^ 2) = H₂ ^ 4 * H₄ ^ 3 := by
    have hmul' :
        serre_D 12 (H₂ ^ 4 * H₄ ^ 2) =
          (serre_D 8 (H₂ ^ 4)) * (H₄ ^ 2) + (H₂ ^ 4) * (serre_D 4 (H₄ ^ 2)) := by
      simpa [show (8 : ℂ) + 4 = 12 by norm_num] using
        (serre_D_mul (k₁ := (8 : ℤ)) (k₂ := (4 : ℤ)) (H₂ ^ 4) (H₄ ^ 2) hH2_pow4 hH4_sq)
    rw [hmul', hS8_H2_pow4, hS4_H4_sq]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  have hS12_H2cube_mul_H4cube :
      serre_D 12 (H₂ ^ 3 * H₄ ^ 3) =
        (-1 / 2 : ℂ) • (H₂ ^ 4 * H₄ ^ 3) + (1 / 2 : ℂ) • (H₂ ^ 3 * H₄ ^ 4) := by
    have hmul' :
        serre_D 12 (H₂ ^ 3 * H₄ ^ 3) =
          (serre_D 6 (H₂ ^ 3)) * (H₄ ^ 3) + (H₂ ^ 3) * (serre_D 6 (H₄ ^ 3)) := by
      simpa [show (6 : ℂ) + 6 = 12 by norm_num] using
        (serre_D_mul (k₁ := (6 : ℤ)) (k₂ := (6 : ℤ)) (H₂ ^ 3) (H₄ ^ 3) hH2_cube hH4_cube)
    rw [hmul', hS6_H2_cube, hS6_H4_cube]
    ext z
    simp [smul_eq_mul, pow_succ, mul_assoc, mul_comm, Pi.mul_apply, Pi.add_apply]
    ring_nf
  -- Expand the outer Serre derivative using linearity, then rewrite each monomial Serre derivative.
  have hH2_pow6 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 6) := by fun_prop
  have hH2pow5_mul_H4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 5 * H₄) := hH2_pow5.mul hH4
  have hH2pow4_mul_H4sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 4 * H₄ ^ 2) := hH2_pow4.mul hH4_sq
  have hH2cube_mul_H4cube : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 3 * H₄ ^ 3) := hH2_cube.mul hH4_cube
  set U1 : UpperHalfPlane → ℂ := (5 / 3 : ℂ) • (H₂ ^ 6)
  set U2 : UpperHalfPlane → ℂ := (5 : ℂ) • (H₂ ^ 5 * H₄)
  set U3 : UpperHalfPlane → ℂ := (5 : ℂ) • (H₂ ^ 4 * H₄ ^ 2)
  set U4 : UpperHalfPlane → ℂ := (10 / 3 : ℂ) • (H₂ ^ 3 * H₄ ^ 3)
  have hU1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) U1 := hH2_pow6.const_smul _
  have hU2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) U2 := hH2pow5_mul_H4.const_smul _
  have hU3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) U3 := hH2pow4_mul_H4sq.const_smul _
  have hU4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) U4 := hH2cube_mul_H4cube.const_smul _
  have hU12 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (U1 + U2) := hU1.add hU2
  have hU123 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((U1 + U2) + U3) := hU12.add hU3
  have hS12_S10_G :
      serre_D 12 (serre_D 10 G) =
        (5 / 3 : ℂ) • (serre_D 12 (H₂ ^ 6)) +
          (5 : ℂ) • (serre_D 12 (H₂ ^ 5 * H₄)) +
          (5 : ℂ) • (serre_D 12 (H₂ ^ 4 * H₄ ^ 2)) +
          (10 / 3 : ℂ) • (serre_D 12 (H₂ ^ 3 * H₄ ^ 3)) := by
    -- Start from the explicit formula for `serre_D 10 G` and distribute `serre_D 12` over the sum.
    have hS10G' : serre_D 10 G = ((U1 + U2) + U3) + U4 := by
      simpa [U1, U2, U3, U4, add_assoc] using hS10_G
    rw [hS10G']
    rw [serre_D_addC (k := (12 : ℂ)) ((U1 + U2) + U3) U4 hU123 hU4]
    rw [serre_D_addC (k := (12 : ℂ)) (U1 + U2) U3 hU12 hU3]
    rw [serre_D_addC (k := (12 : ℂ)) U1 U2 hU1 hU2]
    -- Pull the scalar coefficients out.
    rw [serre_D_smulC (k := (12 : ℂ)) (c := (5 / 3 : ℂ)) (H₂ ^ 6) hH2_pow6]
    rw [serre_D_smulC (k := (12 : ℂ)) (c := (5 : ℂ)) (H₂ ^ 5 * H₄) hH2pow5_mul_H4]
    rw [serre_D_smulC (k := (12 : ℂ)) (c := (5 : ℂ)) (H₂ ^ 4 * H₄ ^ 2) hH2pow4_mul_H4sq]
    rw [serre_D_smulC (k := (12 : ℂ)) (c := (10 / 3 : ℂ)) (H₂ ^ 3 * H₄ ^ 3) hH2cube_mul_H4cube]
  -- Substitute the explicit monomial identities.
  rw [hS12_S10_G, hS12_H2_pow6, hS12_H2pow5_mul_H4, hS12_H2pow4_mul_H4sq, hS12_H2cube_mul_H4cube]
  -- Now everything is a polynomial identity in `H₂` and `H₄`, plus the standard level-1 objects.
  ext z
  have hE4 := congrArg (fun f => f z) SpherePacking.ModularForms.E₄_eq_thetaE4
  have hE6 := congrArg (fun f => f z) SpherePacking.ModularForms.E₆_eq_thetaE6
  simp [SpherePacking.ModularForms.thetaE4, SpherePacking.ModularForms.thetaE6,
    smul_eq_mul] at hE4 hE6
  simp [G, Δ_fun, U1, U2, U3, U4, hE4, hE6, smul_eq_mul,
    Pi.mul_apply, Pi.add_apply, Pi.sub_apply] at *
  ring_nf

/- Positivity of (quasi)modular forms. $F, G, H_2$ are all (sum of) squares. -/
