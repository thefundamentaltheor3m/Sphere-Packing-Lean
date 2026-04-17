/-
Copyright (c) 2025 Sphere Packing Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Field.Power
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Order.CompletePartialOrder

public import SpherePacking.ModularForms.JacobiTheta.Basic
public import SpherePacking.ModularForms.JacobiTheta.Positivity
public import SpherePacking.ForMathlib.AtImInfty
public import SpherePacking.ForMathlib.ComplexI
public import SpherePacking.ForMathlib.Cusps
public import SpherePacking.ForMathlib.FunctionsBoundedAtInfty
public import SpherePacking.ForMathlib.SlashActions
public import SpherePacking.ForMathlib.UpperHalfPlane
public import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.Tactic.NormNumI

/-!
# Jacobi theta functions: slash actions, modular form structure, boundedness at `i∞`

This file develops the slash-action calculus for the functions `H₂`, `H₃`, `H₄`:
transformation laws under generators `T`, `S`, `α`, `β`, `negI`, and (their inverses), the
`SlashInvariantForm` structures `H_SIF`, holomorphy on the upper half-plane, boundedness of all
`SL(2, ℤ)` slash translates at `Im z → ∞`, and the final `ModularForm` structures `H_MF` of level
`Γ(2)` and weight `2`.

As a consequence of the `S`-transformation we also deduce that `H₄` is real and positive on the
positive imaginary axis.
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

section H_SlashInvariant

/-- Slash action of various elements on H₂, H₃, H₄ -/
public lemma H₂_negI_action : (H₂ ∣[(2 : ℤ)] negI.1) = H₂ :=
  modular_slash_negI_of_even H₂ (2: ℤ) even_two
/-- `H₃` is invariant under the `negI` slash action. -/
public lemma H₃_negI_action : (H₃ ∣[(2 : ℤ)] negI.1) = H₃ :=
  modular_slash_negI_of_even H₃ (2: ℤ) even_two
/-- `H₄` is invariant under the `negI` slash action. -/
public lemma H₄_negI_action : (H₄ ∣[(2:ℤ)] negI.1) = H₄ := modular_slash_negI_of_even H₄ 2 even_two

/-- These three transformation laws follow directly from tsum definition. -/
@[grind =] public lemma H₂_T_action : (H₂ ∣[(2 : ℤ)] T) = -H₂ := by
  ext x
  suffices hΘ₂ : Θ₂ ((1 : ℝ) +ᵥ x) = cexp (π * I / 4) * Θ₂ x by
    simp_rw [modular_slash_T_apply, Pi.neg_apply, H₂, hΘ₂, mul_pow, ← Complex.exp_nat_mul,
      mul_comm ((4 : ℕ) : ℂ), Nat.cast_ofNat, div_mul_cancel₀ (b := (4 : ℂ)) _ (by simp),
      Complex.exp_pi_mul_I, neg_one_mul]
  calc
  _ = ∑' (n : ℤ), cexp (π * I * (n + 1 / 2) ^ 2 * ((1 : ℝ) +ᵥ x)) := by
    simp_rw [Θ₂, Θ₂_term]
  _ = ∑' (n : ℤ), cexp (π * I / 4) * cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    apply tsum_congr fun b ↦ ?_
    rw [coe_vadd, ofReal_one]
    repeat rw [← Complex.exp_add]
    congr
    ring_nf
  _ = cexp (π * I / 4) * ∑' (n : ℤ), cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    rw [tsum_mul_left]
  _ = _ := by
    simp_rw [Θ₂, Θ₂_term]
    congr 1
    apply tsum_congr fun b ↦ ?_
    have : Even (b ^ 2 + b) := by
      convert Int.even_mul_succ_self b using 1
      ring_nf
    norm_cast
    rw [Complex.exp_add]
    rw [mul_comm (π * I), Complex.exp_int_mul, Complex.exp_pi_mul_I, this.neg_one_zpow, one_mul]

/-- The slash action of `T` sends `H₃` to `H₄`. -/
@[grind =]
public lemma H₃_T_action : (H₃ ∣[(2 : ℤ)] T) = H₄ := by
  ext x
  simp_rw [modular_slash_T_apply, H₃, H₄, Θ₃, Θ₄, Θ₃_term, Θ₄_term]
  congr 1
  apply tsum_congr fun b ↦ ?_
  rw [coe_vadd, ofReal_one, mul_add, Complex.exp_add, mul_one, mul_comm (π * I), ← Int.cast_pow,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]
  congr 1
  rcases Int.even_or_odd b with (hb | hb)
  · rw [hb.neg_one_zpow, Even.neg_one_zpow]
    simp [sq, hb]
  · rw [hb.neg_one_zpow, Odd.neg_one_zpow]
    simp [sq, hb]

/-- The slash action of `T` sends `H₄` to `H₃`. -/
@[grind =]
public lemma H₄_T_action : (H₄ ∣[(2 : ℤ)] T) = H₃ := by
  -- H₄|T = H₃|T^2 = Θ₂(0, z + 2) = Θ₂(0, z) = H₃
  ext x
  simp_rw [← H₃_T_action, modular_slash_T_apply, H₃, Θ₃_as_jacobiTheta₂, coe_vadd, ← add_assoc]
  norm_num
  rw [add_comm, jacobiTheta₂_add_right]

private lemma slash_inv_eq_of_slash_eq {k : ℤ} {F G : ℍ → ℂ} {γ : SL(2, ℤ)}
    (h : (F ∣[k] γ) = G) : (G ∣[k] γ⁻¹) = F := by
  simpa [← slash_mul, mul_inv_cancel, slash_one] using (congrArg (fun H => H ∣[k] γ⁻¹) h).symm

lemma H₂_T_inv_action : (H₂ ∣[(2 : ℤ)] T⁻¹) = -H₂ := by
  nth_rw 1 [← neg_eq_iff_eq_neg.mpr H₂_T_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₃_T_inv_action : (H₃ ∣[(2 : ℤ)] T⁻¹) = H₄ := by
  nth_rw 1 [← H₄_T_action, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₄_T_inv_action : (H₄ ∣[(2 : ℤ)] T⁻¹) = H₃ := by
  nth_rw 1 [← H₃_T_action, ← slash_mul, mul_inv_cancel, slash_one]

/-- Use α = T * T -/
public lemma H₂_α_action : (H₂ ∣[(2 : ℤ)] α.1) = H₂ := by
  simp [α_eq_T_sq, sq, slash_mul, H₂_T_action]

/-- The slash action of `α` fixes `H₃`. -/
public lemma H₃_α_action : (H₃ ∣[(2 : ℤ)] α.1) = H₃ := by
  simp [α_eq_T_sq, sq, slash_mul, H₃_T_action, H₄_T_action]

/-- The slash action of `α` fixes `H₄`. -/
public lemma H₄_α_action : (H₄ ∣[(2 : ℤ)] α.1) = H₄ := by
  simp [α_eq_T_sq, sq, slash_mul, H₃_T_action, H₄_T_action]

/-- Use jacobiTheta₂_functional_equation -/
@[grind =]
public lemma H₂_S_action : (H₂ ∣[(2 : ℤ)] S) = -H₄ := by
  ext ⟨x, hx⟩
  have hx' : x ≠ 0 := by simp [Complex.ext_iff, hx.ne.symm]
  calc
  _ = cexp (-π * I / x) * jacobiTheta₂ (-1 / (2 * x)) (-1 / x) ^ 4 * x ^ (-2 : ℤ) := by
    rw [modular_slash_S_apply, H₂, Θ₂_as_jacobiTheta₂]
    simp only [inv_neg, mul_neg, mul_pow, ←
      Complex.exp_nat_mul, Nat.cast_ofNat, Int.reduceNeg, zpow_neg, neg_mul, mul_eq_mul_right_iff,
      inv_eq_zero]
    rw [mul_comm 4, div_mul_cancel₀ _ (by norm_num)]
    left
    congr 3
    · rw [← div_eq_mul_inv, neg_div]
    · rw [← one_div, neg_div, div_div, mul_comm, neg_div]
    · rw [← one_div, neg_div]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * (1 / (I / x) ^ ((1 : ℂ) / 2) * cexp (π * I / (4 * x)) * jacobiTheta₂ (1 / 2) x) ^ 4 := by
    rw [mul_right_comm, jacobiTheta₂_functional_equation]
    congr 4
    · ring_nf
    · congr 1
      grind only
    · ring_nf; simp [hx']
    · ring_nf; simp [inv_inv]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * ((1 / (I / x) ^ ((1 : ℂ) / 2)) ^ 4 * cexp (π * I / (4 * x)) ^ 4
          * jacobiTheta₂ (1 / 2) x ^ 4) := by
    simp [mul_pow]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * ((1 / (I / x) ^ (2 : ℂ)) * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4) := by
    congr 3
    simp only [div_pow, one_pow, ← cpow_mul_nat]
    ring_nf
  _ = cexp (-π * I / x) * (x ^ (-2 : ℤ) * (-x ^ (2 : ℤ)))
        * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4 := by
    repeat rw [← mul_assoc]
    congr 4
    rw [cpow_ofNat, div_pow, one_div_div, I_sq, div_neg, div_one]
    rfl
  _ = -cexp (-π * I / x) * cexp (π * I / x) * jacobiTheta₂ (1 / 2) x ^ 4 := by
    rw [mul_neg, ← zpow_add₀ hx', neg_add_cancel, mul_neg, zpow_zero, mul_one]
    congr 2
    rw [← Complex.exp_nat_mul]
    ring_nf
  _ = -jacobiTheta₂ (1 / 2) x ^ 4 := by
    rw [neg_mul, ← Complex.exp_add, neg_mul (π : ℂ), neg_div, neg_add_cancel, Complex.exp_zero,
      neg_one_mul]
  _ = -H₄ ⟨x, hx⟩ := by
    simp [H₄, Θ₄_as_jacobiTheta₂]

/-- The slash action of `S` sends `H₃` to `-H₃`. -/
@[grind =]
public lemma H₃_S_action : (H₃ ∣[(2 : ℤ)] S) = -H₃ := by
  ext x
  have hx' : (x : ℂ) ≠ 0 := by obtain ⟨x, hx⟩ := x; change x ≠ 0; simp [Complex.ext_iff, hx.ne.symm]
  have := jacobiTheta₂_functional_equation 0
  simp only [neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at this
  simp only [modular_slash_S_apply, H₃, inv_neg, Θ₃_as_jacobiTheta₂, Int.reduceNeg, zpow_neg,
    Pi.neg_apply]
  rw [this, mul_pow, neg_div, div_neg, neg_neg, one_div (x : ℂ)⁻¹, inv_inv,
    mul_right_comm, ← neg_one_mul (_ ^ 4)]
  congr
  rw [div_pow, ← cpow_mul_nat, mul_neg, neg_neg]
  ring_nf!
  rw [← mul_inv, cpow_ofNat, sq, ← mul_assoc, zpow_two]
  ring_nf!
  rw [inv_pow, inv_I, even_two.neg_pow, I_sq, mul_neg_one, inv_inv, neg_mul, inv_mul_cancel₀]
  exact pow_ne_zero _ hx'

/-- The slash action of `S` sends `H₄` to `-H₂`. -/
@[grind =]
public lemma H₄_S_action : (H₄ ∣[(2 : ℤ)] S) = - H₂ := by
  rw [← neg_eq_iff_eq_neg.mpr H₂_S_action, neg_slash, ← slash_mul, modular_S_sq,
    ModularForm.slash_neg' _ _ even_two, slash_one]

/-- `H₄(it)` is real and positive for all `t > 0`. -/
public theorem H₄_imag_axis_pos : ResToImagAxis.Pos H₄ := by
  refine ⟨H₄_imag_axis_real, ?_⟩
  intro t ht
  set a : ℝ := t ^ (-(2 : ℤ)) with ha
  have hrel : H₄.resToImagAxis t = (a : ℂ) * H₂.resToImagAxis (1 / t) := by
    have hS := (ResToImagAxis.SlashActionS (F := H₂) (k := (2 : ℤ)) (t := t) ht)
    have hIz : (Complex.I : ℂ) ^ (-(2 : ℤ)) = (-1 : ℂ) := by norm_num1
    apply neg_injective
    simpa [H₂_S_action, hIz, ha, Function.resToImagAxis, ResToImagAxis, ht, mul_assoc,
      mul_left_comm, mul_comm] using hS
  have ht2 : 0 < a := by simpa [ha] using zpow_pos ht (-(2 : ℤ))
  have hH2pos : 0 < (H₂.resToImagAxis (1 / t)).re :=
    (H₂_imag_axis_pos).2 (1 / t) (one_div_pos.2 ht)
  have hre : (H₄.resToImagAxis t).re = a * (H₂.resToImagAxis (1 / t)).re := by
    have := congrArg Complex.re hrel
    simpa [Complex.mul_re] using this
  rw [hre]
  exact mul_pos ht2 hH2pos

lemma H₂_S_inv_action : (H₂ ∣[(2 : ℤ)] S⁻¹) = -H₄ := by
  rw [← neg_eq_iff_eq_neg.mpr H₄_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₃_S_inv_action : (H₃ ∣[(2 : ℤ)] S⁻¹) = -H₃ := by
  nth_rw 1 [← neg_eq_iff_eq_neg.mpr H₃_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₄_S_inv_action : (H₄ ∣[(2 : ℤ)] S⁻¹) = -H₂ := by
  rw [← neg_eq_iff_eq_neg.mpr H₂_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

/-- Use β = -S * α^(-1) * S -/
public lemma H₂_β_action : (H₂ ∣[(2 : ℤ)] β.1) = H₂ := calc
  _ = (((H₂ ∣[(2 : ℤ)] negI.1) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α.1⁻¹) ∣[(2 : ℤ)] S := by
    simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul]
  _ = _ := by
    rw [H₂_negI_action, H₂_S_action, neg_slash, neg_slash, α_eq_T_sq]
    simp [sq, slash_mul, H₄_T_inv_action, H₃_T_inv_action, H₄_S_action]

/-- `H₃` is invariant under the `β` slash action (a generator for `Γ(2)`). -/
public lemma H₃_β_action : (H₃ ∣[(2 : ℤ)] β.1) = H₃ := by
  have hαinv : (H₃ ∣[(2 : ℤ)] α.1⁻¹) = H₃ :=
    slash_inv_eq_of_slash_eq (k := (2 : ℤ)) (F := H₃) (G := H₃) (γ := α.1) H₃_α_action
  simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul, H₃_negI_action, H₃_S_action, hαinv]

/-- `H₄` is invariant under the `β` slash action (a generator for `Γ(2)`). -/
public lemma H₄_β_action : (H₄ ∣[(2 : ℤ)] β.1) = H₄ := by
  have hαinv : (H₂ ∣[(2 : ℤ)] α.1⁻¹) = H₂ :=
    slash_inv_eq_of_slash_eq (k := (2 : ℤ)) (F := H₂) (G := H₂) (γ := α.1) H₂_α_action
  simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul, H₄_negI_action, H₄_S_action, H₂_S_action,
    hαinv]

/-- H₂, H₃, H₄ are modular forms of weight 2 and level Γ(2) -/
@[expose] public noncomputable def H₂_SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₂
  slash_action_eq' := slashaction_generators_Γ2 H₂ (2 : ℤ) H₂_α_action H₂_β_action H₂_negI_action

/-- The slash invariant form structure on `H₃` of level `Γ(2)` and weight `2`. -/
@[expose] public noncomputable def H₃_SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₃
  slash_action_eq' := slashaction_generators_Γ2 H₃ (2 : ℤ) H₃_α_action H₃_β_action H₃_negI_action

/-- The slash invariant form structure on `H₄` of level `Γ(2)` and weight `2`. -/
@[expose] public noncomputable def H₄_SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₄
  slash_action_eq' := slashaction_generators_Γ2 H₄ (2 : ℤ) H₄_α_action H₄_β_action H₄_negI_action

@[simp] lemma H₂_SIF_coe : (H₂_SIF : ℍ → ℂ) = H₂ := rfl

@[simp] lemma H₃_SIF_coe : (H₃_SIF : ℍ → ℂ) = H₃ := rfl

@[simp] lemma H₄_SIF_coe : (H₄_SIF : ℍ → ℂ) = H₄ := rfl

end H_SlashInvariant


section H_MDifferentiable

/-- Holomorphy of `H₂_SIF` as a slash invariant form. -/
public lemma H₂_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂_SIF := by
  rw [mdifferentiable_iff]
  simp only [H₂_SIF, SlashInvariantForm.coe_mk]
  have h_exp : DifferentiableOn ℂ (fun z : ℂ => cexp (((π : ℂ) * I / 4) * z)) {z | 0 < z.im} := by
    intro z hz
    exact ((differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp).differentiableWithinAt
  have h_theta : DifferentiableOn ℂ (fun z : ℂ => jacobiTheta₂ (z / 2) z) {z | 0 < z.im} := by
    intro z hz
    let f : ℂ → ℂ × ℂ := fun t => (t / 2, t)
    let g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
    have hg : DifferentiableAt ℂ g (f z) := by
      simpa [f, g] using (hasFDerivAt_jacobiTheta₂ (z / 2) (by simpa using hz)).differentiableAt
    have hf : DifferentiableAt ℂ f z := by
      simp [f, div_eq_mul_inv]
    simpa [f, g] using (DifferentiableAt.fun_comp' z hg hf).differentiableWithinAt
  have h_prod :
      DifferentiableOn ℂ
        (fun z : ℂ => cexp (((π : ℂ) * I / 4) * z) * jacobiTheta₂ (z / 2) z) {z | 0 < z.im} :=
    h_exp.mul h_theta
  refine (h_prod.pow 4).congr ?_
  intro z hz
  simp [Function.comp, H₂, Θ₂_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz, div_eq_mul_inv,
    mul_assoc, mul_comm]

/-- The function `H₂` is holomorphic on the upper half-plane. -/
public lemma mdifferentiable_H₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := by
  simpa [H₂_SIF] using H₂_SIF_MDifferentiable

private lemma differentiableOn_jacobiTheta₂_snd (z : ℂ) :
    DifferentiableOn ℂ (fun τ => jacobiTheta₂ z τ) {τ | 0 < τ.im} :=
  fun τ hτ => (differentiableAt_jacobiTheta₂_snd z (by simpa using hτ)).differentiableWithinAt

/-- Holomorphy of `H₃_SIF` as a slash invariant form. -/
public lemma H₃_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₃_SIF := by
  rw [mdifferentiable_iff]
  simp only [H₃_SIF, SlashInvariantForm.coe_mk]
  refine ((differentiableOn_jacobiTheta₂_snd (0 : ℂ)).pow 4).congr ?_
  intro _ hz
  simp [Function.comp, H₃, Θ₃_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz]

/-- The function `H₃` is holomorphic on the upper half-plane. -/
public lemma mdifferentiable_H₃ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₃ := by
  simpa [H₃_SIF] using H₃_SIF_MDifferentiable

/-- Holomorphy of `H₄_SIF` as a slash invariant form. -/
public lemma H₄_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄_SIF := by
  rw [mdifferentiable_iff]
  simp only [H₄_SIF, SlashInvariantForm.coe_mk]
  refine ((differentiableOn_jacobiTheta₂_snd (1 / 2 : ℂ)).pow 4).congr ?_
  intro _ hz
  simp [Function.comp, H₄, Θ₄_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz]

/-- The function `H₄` is holomorphic on the upper half-plane. -/
public lemma mdifferentiable_H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := by
  simpa [H₄_SIF] using H₄_SIF_MDifferentiable

end H_MDifferentiable


section H_isBoundedAtImInfty

variable (γ : SL(2, ℤ))

/-- Simplify `jacobiTheta₂_term n (z / 2) z` to an exponential with integer exponent. -/
public lemma jacobiTheta₂_term_half_apply (n : ℤ) (z : ℂ) :
    jacobiTheta₂_term n (z / 2) z = cexp (π * I * (n ^ 2 + n) * z) := by
  rw [jacobiTheta₂_term]
  ring_nf

public lemma jacobiTheta₂_rel_aux (n : ℤ) (t : ℝ) :
    rexp (-π * (n + 1 / 2) ^ 2 * t)
      = rexp (-π * t / 4) * jacobiTheta₂_term n (I * t / 2) (I * t) := by
  rw [jacobiTheta₂_term_half_apply, ofReal_exp, ofReal_exp, ← Complex.exp_add, ofReal_mul]
  congr 1
  ring_nf
  simp
  ring_nf

/-- The norm of `cexp (z * I)` is `Real.exp (-z.im)`. -/
public lemma Complex.norm_exp_mul_I (z : ℂ) : ‖cexp (z * I)‖ = rexp (-z.im) := by simp [norm_exp]

lemma norm_Θ₂_term (n : ℤ) (z : ℍ) :
    ‖Θ₂_term n z‖ = rexp (-π * (((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) * z.im) := by
  set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
  have hr : (n + (2⁻¹ : ℂ)) = (r : ℂ) := by
    apply Complex.ext <;> simp [r]
  have hsq : (n + (2⁻¹ : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
    simp_all
  have h_mulI :
      (π * I * (n + (2⁻¹ : ℂ)) ^ 2 * z : ℂ) = (π * ((r ^ 2 : ℝ) : ℂ) * z) * I := by
    simp [hsq, mul_assoc, mul_left_comm, mul_comm]
  have him : (π * ((r ^ 2 : ℝ) : ℂ) * z : ℂ).im = π * (r ^ 2) * z.im := by
    calc
      (π * ((r ^ 2 : ℝ) : ℂ) * z : ℂ).im = (((π : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * z : ℂ).im := by
        simp [mul_assoc]
      _ = (((Real.pi * (r ^ 2) : ℝ) : ℂ) * z : ℂ).im := by simp
      _ = (Real.pi * (r ^ 2)) * z.im := im_ofReal_mul (Real.pi * (r ^ 2)) (z : ℂ)
      _ = π * (r ^ 2) * z.im := by simp [mul_assoc]
  calc
    ‖Θ₂_term n z‖ = ‖cexp ((π * ((r ^ 2 : ℝ) : ℂ) * z) * I)‖ := by
      simp [Θ₂_term, one_div, h_mulI]
    _ = rexp (-(π * ((r ^ 2 : ℝ) : ℂ) * z).im) := by
      simp [Complex.norm_exp_mul_I]
    _ = rexp (-π * (r ^ 2) * z.im) := by
      rw [him]
      simp [mul_assoc]
    _ = rexp (-π * (((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) * z.im) := by
      simp [r, pow_two, mul_assoc]

lemma summable_exp_neg_pi_mul_int_add_half_sq :
    Summable fun n : ℤ => rexp (-π * ((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) := by
  simpa [norm_Θ₂_term, mul_one] using (summable_Θ₂_term UpperHalfPlane.I).norm

public theorem isBoundedAtImInfty_H₂ : IsBoundedAtImInfty H₂ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₂, Θ₂]
  use (∑' n : ℤ, rexp (-π * ((n : ℝ) + (2⁻¹ : ℝ)) ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  have hsum_norm : Summable fun n : ℤ => ‖Θ₂_term n z‖ := (summable_Θ₂_term z).norm
  have hsum_exp : Summable fun n : ℤ => rexp (-π * ((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) :=
    summable_exp_neg_pi_mul_int_add_half_sq
  have hterm_le (n : ℤ) :
      ‖Θ₂_term n z‖ ≤ rexp (-π * ((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) := by
    have h' :
        -π * (((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) * z.im ≤ -π * ((n : ℝ) + (2⁻¹ : ℝ)) ^ 2 := by
      have hπ : -π * (((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) ≤ 0 := by
        have : 0 ≤ (π : ℝ) * (((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) := by positivity
        have : -((π : ℝ) * (((n : ℝ) + (2⁻¹ : ℝ)) ^ 2)) ≤ 0 := neg_nonpos.2 this
        simpa [neg_mul, mul_assoc] using this
      simpa [mul_one, mul_assoc] using (mul_le_mul_of_nonpos_left hz hπ)
    rw [norm_Θ₂_term]
    exact Real.exp_monotone h'
  have hnorm : ‖Θ₂ z‖ ≤ ∑' n : ℤ, ‖Θ₂_term n z‖ := by
    simpa [Θ₂] using (norm_tsum_le_tsum_norm hsum_norm)
  exact hnorm.trans (Summable.tsum_le_tsum (fun n ↦ hterm_le n) hsum_norm hsum_exp)

-- We isolate this lemma out as it's also used in the proof for Θ₄
lemma isBoundedAtImInfty_H₃_aux (z : ℍ) (hz : 1 ≤ z.im) :
    ∑' (n : ℤ), ‖Θ₃_term n z‖ ≤ ∑' (n : ℤ), rexp (-π * n ^ 2) := by
  have h_rw (z : ℍ) (n : ℤ) : -(π * n ^ 2 * z : ℂ).im = -π * n ^ 2 * z.im := by
    rw [mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← ofReal_intCast, im_ofReal_mul]
    simp [← mul_assoc]
  have h_sum (z : ℍ) : Summable fun n : ℤ ↦ rexp (-π * n ^ 2 * z.im) := by
    have := (summable_jacobiTheta₂_term_iff 0 z).mpr z.coe_im_pos
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add,
      mul_right_comm _ I, norm_exp_mul_I, h_rw] at this
    simpa using summable_ofReal.mp this
  calc
    _ = ∑' (n : ℤ), ‖cexp (π * (n : ℂ) ^ 2 * z * I)‖ := by simp_rw [Θ₃_term, mul_right_comm _ I]
    _ = ∑' (n : ℤ), rexp (-π * (n : ℂ) ^ 2 * z).im := by simp_rw [Complex.norm_exp_mul_I]; simp
    _ = ∑' (n : ℤ), rexp (-π * (n : ℝ) ^ 2 * z.im) := by
      congr with n
      rw [← ofReal_neg, ← coe_im, ← im_ofReal_mul]
      simp
    _ ≤ _ := Summable.tsum_le_tsum (fun b ↦ ?_) ?_ ?_
  · apply exp_monotone
    simp only [neg_mul, neg_le_neg_iff]
    exact le_mul_of_one_le_right (by positivity) hz
  · exact h_sum z
  · simpa using h_sum UpperHalfPlane.I

theorem isBoundedAtImInfty_H₃ : IsBoundedAtImInfty H₃ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₃, Θ₃]
  use (∑' n : ℤ, rexp (-π * n ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  apply (norm_tsum_le_tsum_norm ?_).trans (isBoundedAtImInfty_H₃_aux z hz)
  simp_rw [Θ₃_term_as_jacobiTheta₂_term]
  apply Summable.norm
  rw [summable_jacobiTheta₂_term_iff]
  exact z.coe_im_pos

public theorem isBoundedAtImInfty_H₄ : IsBoundedAtImInfty H₄ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₄, Θ₄]
  use (∑' n : ℤ, rexp (-π * n ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  calc
    _ ≤ ∑' (n : ℤ), ‖Θ₄_term n z‖ := norm_tsum_le_tsum_norm ?_
    _ = ∑' (n : ℤ), ‖Θ₃_term n z‖ := by congr with n; simp [Θ₄_term, Θ₃_term]
    _ ≤ _ := isBoundedAtImInfty_H₃_aux z hz
  simp_rw [Θ₄_term_as_jacobiTheta₂_term]
  apply Summable.norm
  rw [summable_jacobiTheta₂_term_iff]
  exact z.coe_im_pos

public theorem isBoundedAtImInfty_H_slash : IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] γ)
      ∧ IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] γ) ∧ IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] γ) := by
  apply Subgroup.closure_induction_left (s := {S, T, ↑negI})
      (p := fun γ _ ↦ IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] γ) ∧ IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] γ)
        ∧ IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] γ))
  · simp [isBoundedAtImInfty_H₂, isBoundedAtImInfty_H₃, isBoundedAtImInfty_H₄]
  · intro x hx y _ h
    simp_rw [slash_mul]
    rcases hx with (rfl | rfl | rfl | _)
    · simp_rw [H₂_S_action, H₃_S_action, H₄_S_action, neg_slash, isBoundedAtImInfty_neg_iff]
      use h.right.right, h.right.left, h.left
    · simp_rw [H₂_T_action, H₃_T_action, H₄_T_action, neg_slash, isBoundedAtImInfty_neg_iff]
      use h.left, h.right.right, h.right.left
    · rw [SL_slash, H₂_negI_action, H₃_negI_action, H₄_negI_action]
      exact h
  · intro x hx y _ h
    simp_rw [slash_mul]
    rcases hx with (rfl | rfl | rfl | _)
    · simp_rw [H₂_S_inv_action, H₃_S_inv_action, H₄_S_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]
      use h.right.right, h.right.left, h.left
    · simp_rw [H₂_T_inv_action, H₃_T_inv_action, H₄_T_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]
      use h.left, h.right.right, h.right.left
    · rw [← Subgroup.coe_inv, modular_negI_inv, SL_slash,
        modular_slash_negI_of_even _ 2 (by decide)]
      rw [H₃_negI_action, H₄_negI_action]
      exact h
  · intro s hs
    simp_rw [Set.mem_setOf_eq, Set.mem_range] at hs
    obtain ⟨s, rfl⟩ := hs
    rw [Set.mem_iInter, SetLike.mem_coe]
    intro hs
    have hs2 : {S, T} ⊆ (s : Set (SL(2, ℤ))) := by
      apply subset_trans _ hs
      simp only [Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        Set.insert_subset_insert]
    simp only [top_le_iff.mp <| SL2Z_generate.symm ▸ (Subgroup.closure_le s).mpr hs2,
      Subgroup.mem_top]

/-!
## Boundedness at infinity for slash translates
-/

/-- Every `SL(2,ℤ)` slash translate of `H₂` is bounded at `Im z → ∞`. -/
public theorem isBoundedAtImInfty_H₂_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').left

/-- Every `SL(2,ℤ)` slash translate of `H₃` is bounded at `Im z → ∞`. -/
public theorem isBoundedAtImInfty_H₃_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').right.left

/-- Every `SL(2,ℤ)` slash translate of `H₄` is bounded at `Im z → ∞`. -/
public theorem isBoundedAtImInfty_H₄_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').right.right

end H_isBoundedAtImInfty

/-- The modular form of level `Γ(2)` and weight `2` associated to `H₂`. -/
@[expose] public noncomputable def H₂_MF : ModularForm (Γ 2) 2 := {
  H₂_SIF with
  holo' := H₂_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₂_slash
}

/-- The modular form of level `Γ(2)` and weight `2` associated to `H₃`. -/
@[expose] public noncomputable def H₃_MF : ModularForm (Γ 2) 2 := {
  H₃_SIF with
  holo' := H₃_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₃_slash
}

/-- The modular form of level `Γ(2)` and weight `2` associated to `H₄`. -/
@[expose] public noncomputable def H₄_MF : ModularForm (Γ 2) 2 := {
  H₄_SIF with
  holo' := H₄_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₄_slash
}

@[simp] lemma H₂_MF_coe : (H₂_MF : ℍ → ℂ) = H₂ := rfl

@[simp] lemma H₃_MF_coe : (H₃_MF : ℍ → ℂ) = H₃ := rfl

@[simp] lemma H₄_MF_coe : (H₄_MF : ℍ → ℂ) = H₄ := rfl
