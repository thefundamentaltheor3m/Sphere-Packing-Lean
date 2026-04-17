/-
Copyright (c) 2025 Sphere Packing Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SpherePacking.ModularForms.JacobiTheta.Basic
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ForMathlib.ComplexI

/-!
# Jacobi theta functions: imaginary-axis positivity

This file proves realness and positivity of the theta functions `Θ₂`, `Θ₄` and their fourth
powers `H₂`, `H₄` when restricted to the positive imaginary axis `{i t : t > 0}`.

The positivity of `H₄` on the imaginary axis depends on the functional equation (slash action of
`S`) and is therefore proved later in `SpherePacking.ModularForms.JacobiTheta.SlashActions`.
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

/-! ## Imaginary axis properties: realness on the positive imaginary axis. -/

section ImagAxisProperties

private lemma Θ₂_term_eq_ofReal_exp_imag_axis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    Θ₂_term n (⟨Complex.I * t, by simp [ht]⟩ : ℍ) =
      (Real.exp (-(Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)) : ℂ) := by
  set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
  have hr : (n + (2⁻¹ : ℂ)) = (r : ℂ) := by
    apply Complex.ext <;> simp [r]
  have hsq : (n + (2⁻¹ : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
    simp_all
  have harg :
      (π * Complex.I * (n + (2⁻¹ : ℂ)) ^ 2 * ((Complex.I * t : ℂ)) : ℂ) =
        ((-(Real.pi * (r ^ 2) * t) : ℝ) : ℂ) := by
    calc
      (π * Complex.I * (n + (2⁻¹ : ℂ)) ^ 2 * ((Complex.I * t : ℂ)) : ℂ) =
          π * (Complex.I * ((n + (2⁻¹ : ℂ)) ^ 2 * (Complex.I * t))) := by
            simp [mul_assoc]
      _ = π * (Complex.I * (((r ^ 2 : ℝ) : ℂ) * (Complex.I * t))) := by simp [hsq]
      _ = π * (-(((r ^ 2 : ℝ) : ℂ) * (t : ℂ))) := by simp [I_mul_mul_I]
      _ = ((-(Real.pi * (r ^ 2) * t) : ℝ) : ℂ) := by simp [mul_left_comm, mul_comm]
  have hτ :
      Θ₂_term n (⟨Complex.I * t, by simp [ht]⟩ : ℍ) =
        Complex.exp (-(Real.pi * (r ^ 2) * t) : ℝ) := by
    simp [Θ₂_term, one_div, harg]
  simpa [r, one_div, mul_assoc] using hτ

/-- `Θ₂(it)` is real for all `t > 0`. -/
theorem Θ₂_imag_axis_real : ResToImagAxis.Real Θ₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hsum : Summable (fun n : ℤ => Θ₂_term n τ) := summable_Θ₂_term τ
  have hterm_im (n : ℤ) : (Θ₂_term n τ).im = 0 := by
    have h := congrArg Complex.im (Θ₂_term_eq_ofReal_exp_imag_axis (n := n) (t := t) ht)
    assumption
  rw [Θ₂, im_tsum hsum]
  simp [hterm_im]

lemma Θ₂_term_re_imag_axis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂_term n (⟨Complex.I * t, by simp [ht]⟩ : ℍ)).re =
      Real.exp (-(Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)) := by
  have h := congrArg Complex.re (Θ₂_term_eq_ofReal_exp_imag_axis (n := n) (t := t) ht)
  -- avoid rewriting `(Real.exp _ : ℂ)` into `Complex.exp _`
  -- (whose `re` is definitionally `Real.exp _`)
  simpa only [Complex.ofReal_re] using h

/-- `Θ₂(it)` is real and positive for all `t > 0`. -/
theorem Θ₂_imag_axis_pos : ResToImagAxis.Pos Θ₂ := by
  refine ⟨Θ₂_imag_axis_real, ?_⟩
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hsum : Summable (fun n : ℤ => Θ₂_term n τ) := summable_Θ₂_term τ
  have hsumRe : Summable (fun n : ℤ => (Θ₂_term n τ).re) :=
    hsum.mapL Complex.reCLM
  have hterm_re (n : ℤ) :
      (Θ₂_term n τ).re = Real.exp (-(Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)) := by
    simpa [τ] using Θ₂_term_re_imag_axis n t ht
  have hterm_nonneg (n : ℤ) : 0 ≤ (Θ₂_term n τ).re := by
    simpa [hterm_re n] using (Real.exp_pos _).le
  have hterm_pos0 : 0 < (Θ₂_term 0 τ).re := by
    rw [hterm_re 0]
    exact Real.exp_pos _
  have hre_tsum :
      (Θ₂ τ).re = ∑' n : ℤ, (Θ₂_term n τ).re := by
    -- `re` commutes with `tsum`.
    simpa [Θ₂] using (Complex.reCLM.map_tsum hsum)
  -- Positivity of the sum follows from termwise nonnegativity and one positive term.
  have : 0 < ∑' n : ℤ, (Θ₂_term n τ).re :=
    hsumRe.tsum_pos hterm_nonneg 0 hterm_pos0
  simpa [hre_tsum] using this

/-- `Θ₄(it)` is real for all `t > 0`. -/
theorem Θ₄_imag_axis_real : ResToImagAxis.Real Θ₄ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hsum : Summable (fun n : ℤ => Θ₄_term n τ) := by
    have hs : Summable (fun n : ℤ => jacobiTheta₂_term n (1 / 2 : ℂ) τ) :=
      (summable_jacobiTheta₂_term_iff (z := (1 / 2 : ℂ)) (τ := (τ : ℂ))).2
        (by simpa using τ.im_pos)
    simpa [Θ₄_term_as_jacobiTheta₂_term (τ := τ)] using hs
  have hterm_im (n : ℤ) : (Θ₄_term n τ).im = 0 := by
    have hτ : (τ : ℂ) = Complex.I * t := rfl
    have hsign_im : (((-1 : ℂ) ^ n).im = 0) := by
      by_cases hn : Even n <;> simp [neg_one_zpow_eq_ite, hn]
    have hexp_im : (cexp (π * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))).im = 0 := by
      have harg : (π * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ) : ℂ) =
          (-(Real.pi * ((n : ℝ) ^ 2) * t) : ℝ) := by
        simp [hτ, mul_assoc, mul_left_comm, mul_comm, I_mul_I_mul]
      rw [harg]
      exact (Complex.exp_ofReal_im (-(Real.pi * ((n : ℝ) ^ 2) * t)))
    simp [Θ₄_term, Complex.mul_im, hsign_im, hexp_im]
  rw [Θ₄, im_tsum hsum]
  simp [hterm_im]

/-- `H₂(it)` is real for all `t > 0`. -/
public theorem H₂_imag_axis_real : ResToImagAxis.Real H₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hΘ : (Θ₂ τ).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using Θ₂_imag_axis_real t ht
  simpa [H₂] using Complex.im_pow_eq_zero_of_im_eq_zero hΘ 4

/-- `H₂(it)` is real and positive for all `t > 0`. -/
public theorem H₂_imag_axis_pos : ResToImagAxis.Pos H₂ := by
  refine ⟨H₂_imag_axis_real, ?_⟩
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hΘreal : (Θ₂ τ).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using Θ₂_imag_axis_real t ht
  have hΘpos : 0 < (Θ₂ τ).re := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using (Θ₂_imag_axis_pos).2 t ht
  have hΘeq : Θ₂ τ = ((Θ₂ τ).re : ℂ) := by
    refine Complex.ext (by simp) ?_
    simpa using hΘreal
  have hre : (H₂ τ).re = (Θ₂ τ).re ^ 4 := by
    have hre' : ((Θ₂ τ) ^ 4).re = (Θ₂ τ).re ^ 4 := by
      have hpow : (Θ₂ τ) ^ 4 = ((Θ₂ τ).re : ℂ) ^ 4 := by
        simpa using congrArg (fun z : ℂ => z ^ 4) hΘeq
      calc
        ((Θ₂ τ) ^ 4).re = (((Θ₂ τ).re : ℂ) ^ 4).re := by simp [hpow]
        _ = (Θ₂ τ).re ^ 4 := by
          have h :
              ((Θ₂ τ).re : ℂ) ^ 4 = (↑((Θ₂ τ).re ^ 4) : ℂ) :=
            (Complex.ofReal_pow (Θ₂ τ).re 4).symm
          rw [h]
          exact Complex.ofReal_re ((Θ₂ τ).re ^ 4)
    simpa [H₂] using hre'
  simpa [hre] using pow_pos hΘpos 4

/-- `H₄(it)` is real for all `t > 0`. -/
public theorem H₄_imag_axis_real : ResToImagAxis.Real H₄ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hΘ : (Θ₄ τ).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using Θ₄_imag_axis_real t ht
  simpa [H₄] using Complex.im_pow_eq_zero_of_im_eq_zero hΘ 4

end ImagAxisProperties
