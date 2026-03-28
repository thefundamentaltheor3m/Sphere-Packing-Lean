module
public import Mathlib.Algebra.Field.Power
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Order.CompletePartialOrder

public import SpherePacking.ForMathlib.AtImInfty
public import SpherePacking.ForMathlib.ComplexI
public import SpherePacking.ForMathlib.Cusps
public import SpherePacking.ForMathlib.FunctionsBoundedAtInfty
public import SpherePacking.ForMathlib.SlashActions
public import SpherePacking.ForMathlib.UpperHalfPlane
public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.CuspFormIsoModforms
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.Tactic.TendstoCont
import SpherePacking.Tactic.NormNumI

/-!
# Jacobi theta functions

This file defines the Jacobi theta functions `Θ₂`, `Θ₃`, `Θ₄` on the upper half-plane and their
fourth powers `H₂`, `H₃`, `H₄`. It proves modular transformation formulas, boundedness at infinity,
and Jacobi's identity relating `Delta` to the product `H₂ * H₃ * H₄`.

## Main declarations
* `Θ₂`, `Θ₃`, `Θ₄`
* `H₂`, `H₃`, `H₄`
* `H₂_MF`, `H₃_MF`, `H₄_MF`
* `Delta_eq_H₂_H₃_H₄`
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

/-- The term in the series defining `Θ₂`. -/
@[expose] public noncomputable def Θ₂_term (n : ℤ) (τ : ℍ) : ℂ :=
  cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)
/-- The term in the series defining `Θ₃`. -/
@[expose] public noncomputable def Θ₃_term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n : ℂ) ^ 2 * τ)
/-- The term in the series defining `Θ₄`. -/
@[expose] public noncomputable def Θ₄_term (n : ℤ) (τ : ℍ) : ℂ :=
  (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)
/-- The Jacobi theta function `Θ₂` on the upper half-plane. -/
@[expose] public noncomputable def Θ₂ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₂_term n τ
/-- The Jacobi theta function `Θ₃` on the upper half-plane. -/
@[expose] public noncomputable def Θ₃ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₃_term n τ
/-- The Jacobi theta function `Θ₄` on the upper half-plane. -/
@[expose] public noncomputable def Θ₄ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₄_term n τ
/-- The fourth power of `Θ₂`. -/
@[expose] public noncomputable def H₂ (τ : ℍ) : ℂ := (Θ₂ τ) ^ 4
/-- The fourth power of `Θ₃`. -/
@[expose] public noncomputable def H₃ (τ : ℍ) : ℂ := (Θ₃ τ) ^ 4
/-- The fourth power of `Θ₄`. -/
@[expose] public noncomputable def H₄ (τ : ℍ) : ℂ := (Θ₄ τ) ^ 4

/-!
## Connection with `jacobiTheta₂`
-/

/-- Identify `Θ₂_term` with a specialization of `jacobiTheta₂_term`. -/
public theorem Θ₂_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₂_term n τ = cexp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ := by
  rw [Θ₂_term, jacobiTheta₂_term, ← Complex.exp_add]; ring_nf

/-- Identify `Θ₂` with a specialization of `jacobiTheta₂`. -/
public theorem Θ₂_as_jacobiTheta₂ (τ : ℍ) :
    Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  simp_rw [Θ₂, Θ₂_term_as_jacobiTheta₂_term, tsum_mul_left, jacobiTheta₂]

/-- Identify `Θ₃_term` with a specialization of `jacobiTheta₂_term`. -/
public theorem Θ₃_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₃_term n τ = jacobiTheta₂_term n 0 τ := by simp [Θ₃_term, jacobiTheta₂_term]

/-- Identify `Θ₃` with a specialization of `jacobiTheta₂`. -/
public theorem Θ₃_as_jacobiTheta₂ (τ : ℍ) : Θ₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [Θ₃, Θ₃_term_as_jacobiTheta₂_term, jacobiTheta₂]

/-- Identify `Θ₄_term` with a specialization of `jacobiTheta₂_term`. -/
public theorem Θ₄_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₄_term n τ = jacobiTheta₂_term n (1 / 2 : ℂ) τ := by
  rw [Θ₄_term, jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]; ring_nf

/-- Identify `Θ₄` with a specialization of `jacobiTheta₂`. -/
public theorem Θ₄_as_jacobiTheta₂ (τ : ℍ) : Θ₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [Θ₄, Θ₄_term_as_jacobiTheta₂_term, jacobiTheta₂]

/-! ## Imaginary axis properties: realness on the positive imaginary axis. -/

section ImagAxisProperties

@[grind =] lemma I_mul_mul_I (x y : ℂ) : I * (x * (I * y)) = -(x * y) := by
  simp [mul_left_comm, mul_comm]

lemma summable_Θ₂_term (τ : ℍ) : Summable (fun n : ℤ => Θ₂_term n τ) := by
  simpa [Θ₂_term_as_jacobiTheta₂_term (τ := τ)] using
    ((summable_jacobiTheta₂_term_iff (z := (τ : ℂ) / 2) (τ := (τ : ℂ))).2
          (by simpa using τ.im_pos)).mul_left (cexp (π * Complex.I * (τ : ℂ) / 4))

private lemma Θ₂_term_eq_ofReal_exp_imag_axis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    Θ₂_term n (⟨Complex.I * t, by simp [ht]⟩ : ℍ) =
      (Real.exp (-(Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)) : ℂ) := by
  simp only [Θ₂_term, one_div, ofReal_exp]
  congr 1
  push_cast
  linear_combination (↑π : ℂ) * (↑n + 2⁻¹) ^ 2 * ↑t * I_sq

/-- `Θ₂(it)` is real for all `t > 0`. -/
theorem Θ₂_imag_axis_real : ResToImagAxis.Real Θ₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hterm_im (n : ℤ) : (Θ₂_term n τ).im = 0 :=
    congrArg Complex.im (Θ₂_term_eq_ofReal_exp_imag_axis n t ht)
  simp [Θ₂, im_tsum (summable_Θ₂_term τ), hterm_im]

lemma Θ₂_term_re_imag_axis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂_term n (⟨Complex.I * t, by simp [ht]⟩ : ℍ)).re =
      Real.exp (-(Real.pi * (((n : ℝ) + (1 / 2 : ℝ)) ^ 2) * t)) := by
  simpa only [Complex.ofReal_re] using
    congrArg Complex.re (Θ₂_term_eq_ofReal_exp_imag_axis n t ht)

/-- `Θ₂(it)` is real and positive for all `t > 0`. -/
theorem Θ₂_imag_axis_pos : ResToImagAxis.Pos Θ₂ := by
  refine ⟨Θ₂_imag_axis_real, fun t ht ↦ ?_⟩
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hsum := summable_Θ₂_term τ
  have hterm_pos (n : ℤ) : 0 < (Θ₂_term n τ).re := by
    rw [Θ₂_term_re_imag_axis n t ht]; exact Real.exp_pos _
  have hre_tsum : (Θ₂ τ).re = ∑' n, (Θ₂_term n τ).re := by
    simpa [Θ₂] using Complex.reCLM.map_tsum hsum
  simpa [hre_tsum] using
    (hsum.mapL Complex.reCLM).tsum_pos (fun n ↦ (hterm_pos n).le) 0 (hterm_pos 0)

/-- `Θ₄(it)` is real for all `t > 0`. -/
theorem Θ₄_imag_axis_real : ResToImagAxis.Real Θ₄ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have him : 0 < (τ : ℂ).im := by simp [τ, ht]
  have hsum : Summable (fun n : ℤ => Θ₄_term n τ) := by
    simpa [Θ₄_term_as_jacobiTheta₂_term (τ := τ)] using
      (summable_jacobiTheta₂_term_iff (z := (1 / 2 : ℂ)) (τ := (τ : ℂ))).2 him
  have hterm_im (n : ℤ) : (Θ₄_term n τ).im = 0 := by
    have : Θ₄_term n τ = ↑((-1 : ℝ) ^ n * Real.exp (-(Real.pi * ((n : ℝ) ^ 2) * t))) := by
      simp only [Θ₄_term, Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_exp,
        Complex.ofReal_neg]
      congr 2
      push_cast
      linear_combination ↑π * ↑n ^ 2 * ↑t * I_sq
    rw [this, Complex.ofReal_im]
  simp [Θ₄, im_tsum hsum, hterm_im]

/-- `H₂(it)` is real for all `t > 0`. -/
public theorem H₂_imag_axis_real : ResToImagAxis.Real H₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  simpa [H₂] using Complex.im_pow_eq_zero_of_im_eq_zero
    (by simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using Θ₂_imag_axis_real t ht) 4

/-- `H₂(it)` is real and positive for all `t > 0`. -/
public theorem H₂_imag_axis_pos : ResToImagAxis.Pos H₂ := by
  refine ⟨H₂_imag_axis_real, fun t ht ↦ ?_⟩
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hreal : (Θ₂ τ).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using Θ₂_imag_axis_real t ht
  have hpos : 0 < (Θ₂ τ).re := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using Θ₂_imag_axis_pos.2 t ht
  have hΘeq : Θ₂ τ = ((Θ₂ τ).re : ℂ) := Complex.ext (by simp) (by simpa using hreal)
  rw [H₂, hΘeq, ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- `H₄(it)` is real for all `t > 0`. -/
public theorem H₄_imag_axis_real : ResToImagAxis.Real H₄ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  simpa [H₄] using Complex.im_pow_eq_zero_of_im_eq_zero
    (by simpa [Function.resToImagAxis, ResToImagAxis, ht, τ] using Θ₄_imag_axis_real t ht) 4

end ImagAxisProperties

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
  _ = ∑' (n : ℤ), cexp (π * I * (n + 1 / 2) ^ 2 * ((1 : ℝ) +ᵥ x)) := by simp_rw [Θ₂, Θ₂_term]
  _ = ∑' (n : ℤ), cexp (π * I / 4) * cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    apply tsum_congr fun b ↦ ?_
    rw [coe_vadd, ofReal_one]
    simp only [← Complex.exp_add]
    congr 1
    ring
  _ = cexp (π * I / 4) * ∑' (n : ℤ), cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    rw [tsum_mul_left]
  _ = _ := by
    simp_rw [Θ₂, Θ₂_term]
    congr 1
    apply tsum_congr fun b ↦ ?_
    have hbb : b ^ 2 + b = b * (b + 1) := by ring
    have : Even (b ^ 2 + b) := hbb ▸ Int.even_mul_succ_self b
    norm_cast
    rw [Complex.exp_add, mul_comm (π * I), Complex.exp_int_mul, Complex.exp_pi_mul_I,
      this.neg_one_zpow, one_mul]

/-- The slash action of `T` sends `H₃` to `H₄`. -/
@[grind =]
public lemma H₃_T_action : (H₃ ∣[(2 : ℤ)] T) = H₄ := by
  ext x
  simp_rw [modular_slash_T_apply, H₃, H₄, Θ₃, Θ₄, Θ₃_term, Θ₄_term]
  congr 1
  apply tsum_congr fun b ↦ ?_
  rw [coe_vadd, ofReal_one, mul_add, Complex.exp_add, mul_one, mul_comm (π * I),
    ← Int.cast_pow, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  congr 1
  rcases Int.even_or_odd b with hb | hb <;>
    · simp [hb.neg_one_zpow, sq, hb, Odd.neg_one_zpow, Even.neg_one_zpow]

/-- The slash action of `T` sends `H₄` to `H₃`. -/
@[grind =]
public lemma H₄_T_action : (H₄ ∣[(2 : ℤ)] T) = H₃ := by
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
    simp only [inv_neg, mul_neg, mul_pow, ← Complex.exp_nat_mul, Nat.cast_ofNat, Int.reduceNeg,
      zpow_neg, neg_mul, mul_eq_mul_right_iff, inv_eq_zero]
    rw [mul_comm 4, div_mul_cancel₀ _ (by norm_num)]
    left
    congr 3 <;> simp [div_eq_mul_inv, mul_comm]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * (1 / (I / x) ^ ((1 : ℂ) / 2) * cexp (π * I / (4 * x)) * jacobiTheta₂ (1 / 2) x) ^ 4 := by
    rw [mul_right_comm, jacobiTheta₂_functional_equation]
    congr 4
    · ring_nf
    · congr 1; grind only
    all_goals ring_nf; simp [hx', inv_inv]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * ((1 / (I / x) ^ (2 : ℂ)) * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4) := by
    simp only [mul_pow, div_pow, one_pow, ← cpow_mul_nat]; ring_nf
  _ = cexp (-π * I / x) * (x ^ (-2 : ℤ) * (-x ^ (2 : ℤ)))
        * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4 := by
    repeat rw [← mul_assoc]
    congr 4
    rw [cpow_ofNat, div_pow, one_div_div, I_sq, div_neg, div_one]; rfl
  _ = -cexp (-π * I / x) * cexp (π * I / x) * jacobiTheta₂ (1 / 2) x ^ 4 := by
    rw [mul_neg, ← zpow_add₀ hx', neg_add_cancel, mul_neg, zpow_zero, mul_one]
    congr 2
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  _ = -H₄ ⟨x, hx⟩ := by
    rw [neg_mul, ← Complex.exp_add, neg_mul (π : ℂ), neg_div, neg_add_cancel, Complex.exp_zero,
      neg_one_mul]
    simp [H₄, Θ₄_as_jacobiTheta₂]

/-- The slash action of `S` sends `H₃` to `-H₃`. -/
@[grind =]
public lemma H₃_S_action : (H₃ ∣[(2 : ℤ)] S) = -H₃ := by
  ext x
  have hx' : (x : ℂ) ≠ 0 := by obtain ⟨x, hx⟩ := x; change x ≠ 0; simp [Complex.ext_iff, hx.ne.symm]
  have := jacobiTheta₂_functional_equation 0
  simp only [neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, Complex.exp_zero, mul_one] at this
  simp only [modular_slash_S_apply, H₃, inv_neg, Θ₃_as_jacobiTheta₂, Int.reduceNeg, zpow_neg,
    Pi.neg_apply]
  rw [this, mul_pow, neg_div, div_neg, neg_neg, one_div (x : ℂ)⁻¹, inv_inv,
    mul_right_comm, ← neg_one_mul (_ ^ 4)]; congr
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
  refine ⟨H₄_imag_axis_real, fun t ht ↦ ?_⟩
  set a : ℝ := t ^ (-(2 : ℤ)) with ha
  have hrel : H₄.resToImagAxis t = (a : ℂ) * H₂.resToImagAxis (1 / t) := by
    apply neg_injective
    simpa [H₂_S_action, (by norm_num1 : (Complex.I : ℂ) ^ (-(2 : ℤ)) = (-1 : ℂ)), ha,
      Function.resToImagAxis, ResToImagAxis, ht, mul_assoc, mul_left_comm, mul_comm] using
      ResToImagAxis.SlashActionS (F := H₂) (k := (2 : ℤ)) (t := t) ht
  have hre : (H₄.resToImagAxis t).re = a * (H₂.resToImagAxis (1 / t)).re := by
    simpa [Complex.mul_re] using congrArg Complex.re hrel
  rw [hre]
  exact mul_pos (by simpa [ha] using zpow_pos ht (-(2 : ℤ)))
    (H₂_imag_axis_pos.2 (1 / t) (one_div_pos.2 ht))

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
  have h_exp : DifferentiableOn ℂ (fun z => cexp ((π * I / 4) * z)) {z | 0 < z.im} :=
    fun z _ => ((differentiableAt_id.const_mul _).cexp).differentiableWithinAt
  have h_theta : DifferentiableOn ℂ (fun z => jacobiTheta₂ (z / 2) z) {z | 0 < z.im} := by
    intro z hz
    let f : ℂ → ℂ × ℂ := fun t => (t / 2, t)
    have hg : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f z) := by
      simpa [f] using (hasFDerivAt_jacobiTheta₂ (z / 2) (by simpa using hz)).differentiableAt
    simpa [f] using (hg.fun_comp' z (by simp [f, div_eq_mul_inv])).differentiableWithinAt
  refine ((h_exp.mul h_theta).pow 4).congr ?_
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
  intro _ hz; simp [Function.comp, H₃, Θ₃_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz]

/-- The function `H₃` is holomorphic on the upper half-plane. -/
public lemma mdifferentiable_H₃ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₃ := by
  simpa [H₃_SIF] using H₃_SIF_MDifferentiable

/-- Holomorphy of `H₄_SIF` as a slash invariant form. -/
public lemma H₄_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄_SIF := by
  rw [mdifferentiable_iff]
  simp only [H₄_SIF, SlashInvariantForm.coe_mk]
  refine ((differentiableOn_jacobiTheta₂_snd (1 / 2 : ℂ)).pow 4).congr ?_
  intro _ hz; simp [Function.comp, H₄, Θ₄_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz]

/-- The function `H₄` is holomorphic on the upper half-plane. -/
public lemma mdifferentiable_H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := by
  simpa [H₄_SIF] using H₄_SIF_MDifferentiable

/-- Differentiability of `t ↦ jacobiTheta₂(t/2, t)` at points in the upper half-plane. -/
lemma differentiableAt_jacobiTheta₂_half (τ : ℍ) :
    DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ := by
  let f : ℂ → ℂ × ℂ := fun t => (t / 2, t)
  have hg : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f τ) := by
    simpa [f] using (hasFDerivAt_jacobiTheta₂ (τ.1 / 2) τ.2).differentiableAt
  simpa [f] using hg.comp (τ : ℂ)
    ((differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id)

lemma Θ₂_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Θ₂ := by
  intro τ
  have hΘ₂_diff : DifferentiableAt ℂ
      (fun t => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) (τ : ℂ) :=
    ((differentiableAt_id.const_mul _).cexp).mul (differentiableAt_jacobiTheta₂_half τ)
  have hMD := hΘ₂_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
  have : (fun t : ℂ => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) ∘
      UpperHalfPlane.coe = Θ₂ := by
    ext x; simp only [Function.comp_apply, Θ₂_as_jacobiTheta₂]; ring_nf
  rwa [this] at hMD

end H_MDifferentiable

section H_isBoundedAtImInfty

variable (γ : SL(2, ℤ))

/-- Simplify `jacobiTheta₂_term n (z / 2) z` to an exponential with integer exponent. -/
public lemma jacobiTheta₂_term_half_apply (n : ℤ) (z : ℂ) :
    jacobiTheta₂_term n (z / 2) z = cexp (π * I * (n ^ 2 + n) * z) := by
  rw [jacobiTheta₂_term]; ring_nf

lemma jacobiTheta₂_rel_aux (n : ℤ) (t : ℝ) :
    rexp (-π * (n + 1 / 2) ^ 2 * t)
      = rexp (-π * t / 4) * jacobiTheta₂_term n (I * t / 2) (I * t) := by
  rw [jacobiTheta₂_term_half_apply, ofReal_exp, ofReal_exp, ← Complex.exp_add, ofReal_mul]
  congr 1
  push_cast
  linear_combination -(↑π : ℂ) * (↑n ^ 2 + ↑n) * ↑t * I_sq

/-- The norm of `cexp (z * I)` is `Real.exp (-z.im)`. -/
public lemma Complex.norm_exp_mul_I (z : ℂ) : ‖cexp (z * I)‖ = rexp (-z.im) := by simp [norm_exp]

lemma norm_Θ₂_term (n : ℤ) (z : ℍ) :
    ‖Θ₂_term n z‖ = rexp (-π * (((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) * z.im) := by
  set r : ℝ := (n : ℝ) + (2⁻¹ : ℝ)
  have hr : (n + (2⁻¹ : ℂ)) = (r : ℂ) := by apply Complex.ext <;> simp [r]
  have hsq : (n + (2⁻¹ : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by simp_all
  have h_mulI : (π * I * (n + (2⁻¹ : ℂ)) ^ 2 * z : ℂ) = (π * ((r ^ 2 : ℝ) : ℂ) * z) * I := by
    simp [hsq, mul_assoc, mul_left_comm, mul_comm]
  have him : (π * ((r ^ 2 : ℝ) : ℂ) * z : ℂ).im = π * (r ^ 2) * z.im := by
    have : (π : ℂ) * ↑(r ^ 2) = ↑(π * r ^ 2) := by push_cast; ring
    rw [this, im_ofReal_mul, coe_im]
  simp only [Θ₂_term, one_div, h_mulI, Complex.norm_exp_mul_I, him]
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
  have hterm_le (n : ℤ) : ‖Θ₂_term n z‖ ≤ rexp (-π * ((n : ℝ) + (2⁻¹ : ℝ)) ^ 2) := by
    rw [norm_Θ₂_term]
    apply Real.exp_monotone
    have h1 : 0 ≤ π * ((↑n + 2⁻¹) ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr h1)]
  have hnorm : ‖Θ₂ z‖ ≤ ∑' n, ‖Θ₂_term n z‖ := by
    simpa [Θ₂] using norm_tsum_le_tsum_norm (summable_Θ₂_term z).norm
  exact hnorm.trans (Summable.tsum_le_tsum hterm_le (summable_Θ₂_term z).norm
    summable_exp_neg_pi_mul_int_add_half_sq)

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
      congr with n; rw [← ofReal_neg, ← coe_im, ← im_ofReal_mul]; simp
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
  exact ((summable_jacobiTheta₂_term_iff _ _).2 z.coe_im_pos).norm

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
      exact ⟨h.2.2, h.2.1, h.1⟩
    · simp_rw [H₂_T_action, H₃_T_action, H₄_T_action, neg_slash, isBoundedAtImInfty_neg_iff]
      exact ⟨h.1, h.2.2, h.2.1⟩
    · rw [SL_slash, H₂_negI_action, H₃_negI_action, H₄_negI_action]; exact h
  · intro x hx y _ h
    simp_rw [slash_mul]
    rcases hx with (rfl | rfl | rfl | _)
    · simp_rw [H₂_S_inv_action, H₃_S_inv_action, H₄_S_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]; exact ⟨h.2.2, h.2.1, h.1⟩
    · simp_rw [H₂_T_inv_action, H₃_T_inv_action, H₄_T_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]; exact ⟨h.1, h.2.2, h.2.1⟩
    · rw [← Subgroup.coe_inv, modular_negI_inv, SL_slash,
        modular_slash_negI_of_even _ 2 (by decide)]
      rwa [H₃_negI_action, H₄_negI_action]
  · intro s hs
    simp_rw [Set.mem_setOf_eq, Set.mem_range] at hs
    obtain ⟨s, rfl⟩ := hs
    rw [Set.mem_iInter, SetLike.mem_coe]
    intro hs
    have hs2 : {S, T} ⊆ (s : Set (SL(2, ℤ))) :=
      Set.insert_subset_iff.2 ⟨hs (Set.mem_insert _ _), Set.singleton_subset_iff.2
        (hs (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))⟩
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

/-!
## Jacobi identity

The Jacobi identity states H₂ + H₄ = H₃ (equivalently Θ₂⁴ + Θ₄⁴ = Θ₃⁴).
This is blueprint Lemma 6.41, proved via dimension vanishing for weight 4 cusp forms.

The proof strategy:
1. Define g := H₂ + H₄ - H₃ and f := g²
2. Show f is SL₂(ℤ)-invariant (weight 4, level 1) via S/T invariance
3. Show f vanishes at i∞ (is a cusp form)
4. Apply cusp form vanishing: dim S₄(Γ₁) = 0
5. From g² = 0 conclude g = 0

The S/T slash action lemmas are proved here. The full proof requiring
asymptotics (atImInfty) is in AtImInfty.lean to avoid circular imports.
-/

section JacobiIdentity

/-- The difference g := H₂ + H₄ - H₃ -/
noncomputable def jacobi_g : ℍ → ℂ := H₂ + H₄ - H₃

/-- The squared difference f := g² -/
noncomputable def jacobi_f : ℍ → ℂ := jacobi_g ^ 2

/-- S-action on g: g|[2]S = -g -/
@[grind =]
lemma jacobi_g_S_action : (jacobi_g ∣[(2 : ℤ)] S) = -jacobi_g := by
  ext z
  simp [jacobi_g, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_S_action, H₃_S_action, H₄_S_action, add_assoc, add_left_comm, add_comm]

/-- T-action on g: g|[2]T = -g -/
@[grind =]
lemma jacobi_g_T_action : (jacobi_g ∣[(2 : ℤ)] T) = -jacobi_g := by
  ext z
  simp [jacobi_g, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_T_action, H₃_T_action, H₄_T_action, add_assoc, add_left_comm, add_comm]

/-- Rewrite jacobi_f as a pointwise product -/
@[grind =]
lemma jacobi_f_eq_mul : jacobi_f = jacobi_g * jacobi_g := by
  ext z
  simp [jacobi_f, sq]

private lemma jacobi_g_mul_slash (γ : SL(2, ℤ)) :
    ((jacobi_g * jacobi_g) ∣[(4 : ℤ)] γ) =
      (jacobi_g ∣[(2 : ℤ)] γ) * (jacobi_g ∣[(2 : ℤ)] γ) := by
  simpa [(by norm_num : (4 : ℤ) = 2 + 2)] using (mul_slash_SL2 2 2 γ jacobi_g jacobi_g)

/-- S-invariance of f: f|[4]S = f, because g|[2]S = -g. -/
lemma jacobi_f_S_action : (jacobi_f ∣[(4 : ℤ)] S) = jacobi_f := by
  simpa [jacobi_f_eq_mul, jacobi_g_S_action] using (jacobi_g_mul_slash S)

/-- T-invariance of f: f|[4]T = f, because g|[2]T = -g. -/
lemma jacobi_f_T_action : (jacobi_f ∣[(4 : ℤ)] T) = jacobi_f := by
  simpa [jacobi_f_eq_mul, jacobi_g_T_action] using (jacobi_g_mul_slash T)

/-- Full SL₂(ℤ) invariance of f with weight 4 -/
lemma jacobi_f_SL2Z_invariant : ∀ γ : SL(2, ℤ), jacobi_f ∣[(4 : ℤ)] γ = jacobi_f :=
  slashaction_generators_SL2Z jacobi_f 4 jacobi_f_S_action jacobi_f_T_action

/-- jacobi_f as a SlashInvariantForm of weight 4 and level Γ(1) -/
noncomputable def jacobi_f_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 4 where
  toFun := jacobi_f
  slash_action_eq' := slashaction_generators_GL2R jacobi_f 4 jacobi_f_S_action jacobi_f_T_action

/-- jacobi_g is holomorphic (MDifferentiable) since H₂, H₃, H₄ are -/
lemma jacobi_g_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jacobi_g :=
  (H₂_SIF_MDifferentiable.add H₄_SIF_MDifferentiable).sub H₃_SIF_MDifferentiable

/-- jacobi_f is holomorphic (MDifferentiable) since jacobi_g is -/
lemma jacobi_f_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jacobi_f := by
  simpa [jacobi_f, pow_two] using jacobi_g_MDifferentiable.mul jacobi_g_MDifferentiable

/-- jacobi_f_SIF is holomorphic -/
lemma jacobi_f_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jacobi_f_SIF :=
  jacobi_f_MDifferentiable

end JacobiIdentity

/-!
## Limits at infinity

We prove the limit of Θᵢ(z) and Hᵢ(z) as z tends to i∞. This is used to prove the Jacobi identity.
-/

/-- The function `x ↦ jacobiTheta₂ (x / 2) x` tends to `2` at `Im x → ∞`. -/
public theorem jacobiTheta₂_half_mul_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (x / 2) x) atImInfty (𝓝 2) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  have h₁ (n : ℤ) (z : ℂ) : π * I * n * z + π * I * n ^ 2 * z = π * (n + n ^ 2) * z * I := by ring
  convert tendsto_tsum_of_dominated_convergence
    (f := fun z (n : ℤ) ↦ cexp (2 * π * I * n * (z / 2) + π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := Set.indicator {-1, 0} 1)
    (bound := fun n : ℤ ↦ rexp (π / 4) * rexp (-π * ((n : ℝ) + 1 / 2) ^ 2)) ?_ ?_ ?_
  · simp [← tsum_subtype]
  · apply summable_ofReal.mp
    have (n : ℤ) := jacobiTheta₂_rel_aux n 1
    simp_rw [mul_one] at this
    simp_rw [ofReal_mul, this, ← smul_eq_mul]
    apply Summable.const_smul
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff]; simp
  · intro n
    have : n = -1 ∨ n = 0 ∨ n ∉ ({-1, 0} : Set ℤ) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rcases this with (rfl | rfl | hn) <;> ring_nf
    · simp
    · simp
    · simp only [hn, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have h_base' : rexp (-π) ^ ((n : ℝ) + n ^ 2) < 1 := by
        apply Real.rpow_lt_one (by positivity) (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos]))
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        push_neg at hn
        convert_to 0 < ((n * (n + 1) : ℤ) : ℝ)
        · push_cast; ring_nf
        · apply Int.cast_pos.mpr
          by_cases hn' : 0 < n
          · exact mul_pos hn' (by omega)
          · exact mul_pos_of_neg_of_neg (by omega) (by omega)
      simp_rw [h₁, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← Int.cast_add,
        ← ofReal_intCast, im_ofReal_mul, ← mul_assoc, Int.cast_add, Int.cast_pow, ← neg_mul,
        Real.exp_mul, coe_im]
      refine (tendsto_rpow_atTop_of_base_lt_one _ ?_ h_base').comp tendsto_im_atImInfty
      exact neg_one_lt_zero.trans (by positivity)
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [← Real.exp_add]
    ring_nf
    rw [h₁, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← Int.cast_add,
      ← ofReal_intCast, im_ofReal_mul, ← mul_assoc, Int.cast_add, Int.cast_pow, coe_im]
    apply Real.exp_monotone
    have (n : ℤ) : 0 ≤ (n : ℝ) ^ 2 + n := by
      nth_rw 2 [← mul_one n]
      rw [sq, Int.cast_mul, Int.cast_one, ← mul_add]
      rcases lt_trichotomy (-1) n with (hn | rfl | hn)
      · apply mul_nonneg <;> norm_cast; omega
      · norm_num
      · apply mul_nonneg_of_nonpos_of_nonpos <;> norm_cast <;> omega
    nlinarith [mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr (mul_nonneg Real.pi_nonneg (this k)))]

private theorem tsum_weighted_exp_sq_tendsto_atImInfty
    (w : ℤ → ℂ) (hw0 : w 0 = 1) (hw : ∀ n, ‖w n‖ ≤ 1) :
    Tendsto (fun x : ℍ ↦ ∑' n : ℤ, w n * cexp (π * I * n ^ 2 * x)) atImInfty (𝓝 1) := by
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ w n * cexp (π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun k ↦ if k = 0 then 1 else 0)
    (bound := fun n : ℤ ↦ rexp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · apply summable_ofReal.mp
    have := (summable_jacobiTheta₂_term_iff 0 I).mpr (by simp)
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, mul_assoc, ← sq, I_sq,
      mul_neg_one, norm_exp, re_ofReal_mul, neg_re, mul_neg, ← neg_mul, ← ofReal_intCast,
      ← ofReal_pow, ofReal_re] at this
    exact this
  · intro k
    by_cases hk : k = 0
    · subst hk; simp [hw0]
    · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hk_exp : Tendsto (fun z : ℍ ↦ ‖cexp (π * I * k ^ 2 * z)‖) atImInfty (𝓝 0) := by
        simp_rw [mul_right_comm _ I, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← ofReal_intCast,
          ← ofReal_pow, im_ofReal_mul, ← mul_assoc, coe_im]
        exact tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_im_atImInfty.const_mul_atTop (mul_pos Real.pi_pos (sq_pos_of_ne_zero hk')))
      have : Tendsto (fun z : ℍ ↦ w k * cexp (π * I * k ^ 2 * z)) atImInfty (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using tendsto_const_nhds.mul hk_exp
      simpa [hk] using this
  · rw [eventually_atImInfty]
    refine ⟨1, fun z hz k ↦ ?_⟩
    have hmul : ‖w k * cexp (π * I * k ^ 2 * z)‖ ≤ ‖cexp (π * I * k ^ 2 * z)‖ := by simpa using hw k
    refine hmul.trans ?_
    simp_rw [mul_right_comm _ I, norm_exp_mul_I]
    simpa [← ofReal_intCast, ← ofReal_pow] using le_mul_of_one_le_right (by positivity) hz

theorem jacobiTheta₂_zero_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ 0 x) atImInfty (𝓝 1) := by
  simpa [jacobiTheta₂, jacobiTheta₂_term, mul_zero, zero_add] using
    (tsum_weighted_exp_sq_tendsto_atImInfty (w := fun _ : ℤ ↦ (1 : ℂ)) (by simp)
      (by intro n; simp))

theorem jacobiTheta₂_half_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (1 / 2 : ℂ) x) atImInfty (𝓝 1) := by
  have hΘ₄ : Tendsto Θ₄ atImInfty (𝓝 1) := by
    simpa [Θ₄, Θ₄_term] using
      (tsum_weighted_exp_sq_tendsto_atImInfty (w := fun n : ℤ ↦ (-1 : ℂ) ^ n) (by simp)
        (by intro n; simp))
  simpa [funext Θ₄_as_jacobiTheta₂] using hΘ₄

/-- The theta function `Θ₂` tends to `0` at `Im z → ∞`. -/
public theorem Θ₂_tendsto_atImInfty : Tendsto Θ₂ atImInfty (𝓝 0) := by
  rw [funext Θ₂_as_jacobiTheta₂, ← zero_mul (2 : ℂ)]
  refine Tendsto.mul ?_ jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have (z : ℍ) : ‖cexp (π * I * z / 4)‖ = rexp (-π * z.im / 4) := by
    rw [mul_right_comm, mul_div_right_comm, norm_exp_mul_I]; simp [neg_div]
  simp_rw [this]
  exact (Real.tendsto_exp_atBot).comp <|
    (tendsto_div_const_atBot_of_pos zero_lt_four).mpr
      (tendsto_im_atImInfty.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))

/-- The theta function `Θ₃` tends to `1` at `Im z → ∞`. -/
public theorem Θ₃_tendsto_atImInfty : Tendsto Θ₃ atImInfty (𝓝 1) := by
  simpa [funext Θ₃_as_jacobiTheta₂] using jacobiTheta₂_zero_apply_tendsto_atImInfty

/-- The theta function `Θ₄` tends to `1` at `Im z → ∞`. -/
public theorem Θ₄_tendsto_atImInfty : Tendsto Θ₄ atImInfty (𝓝 1) := by
  simpa [funext Θ₄_as_jacobiTheta₂] using jacobiTheta₂_half_apply_tendsto_atImInfty

/-- The function `H₂ = Θ₂^4` tends to `0` at `Im z → ∞`. -/
public theorem H₂_tendsto_atImInfty : Tendsto H₂ atImInfty (𝓝 0) := by
  simpa [H₂] using (Θ₂_tendsto_atImInfty.pow 4)

/-- The function `H₃ = Θ₃^4` tends to `1` at `Im z → ∞`. -/
public theorem H₃_tendsto_atImInfty : Tendsto H₃ atImInfty (𝓝 1) := by
  simpa [H₃] using (Θ₃_tendsto_atImInfty.pow 4)

/-- The function `H₄ = Θ₄^4` tends to `1` at `Im z → ∞`. -/
public theorem H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 1) := by
  simpa [H₄] using (Θ₄_tendsto_atImInfty.pow 4)

/-! ## Jacobi identity proof via limits at i∞. -/

/-- g := H₂ + H₄ - H₃ tends to 0 at i∞. -/
theorem jacobi_g_tendsto_atImInfty : Tendsto jacobi_g atImInfty (𝓝 0) := by
  have := H₂_tendsto_atImInfty
  have := H₃_tendsto_atImInfty
  have := H₄_tendsto_atImInfty
  change Tendsto (fun z => H₂ z + H₄ z - H₃ z) atImInfty (𝓝 0)
  tendsto_cont

/-- f := g² tends to 0 at i∞. -/
theorem jacobi_f_tendsto_atImInfty : Tendsto jacobi_f atImInfty (𝓝 0) := by
  have := jacobi_g_tendsto_atImInfty
  change Tendsto (fun z => jacobi_g z ^ 2) atImInfty (𝓝 0)
  tendsto_cont

private noncomputable def jacobi_f_CF : CuspForm (Γ 1) 4 :=
  cuspFormOfSIFTendstoZero jacobi_f_SIF jacobi_f_SIF_MDifferentiable
    jacobi_f_tendsto_atImInfty

/-- jacobi_f = 0 by dimension argument: weight-4 cusp forms vanish. -/
theorem jacobi_f_eq_zero : jacobi_f = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 4 (by norm_num)) jacobi_f_CF)

/-- jacobi_g = 0 as a function (from g² = 0) -/
theorem jacobi_g_eq_zero : jacobi_g = 0 := by
  ext z
  simpa [jacobi_f] using congr_fun jacobi_f_eq_zero z

/-- Jacobi identity: H₂ + H₄ = H₃ (Blueprint Lemma 6.41) -/
public theorem jacobi_identity : H₂ + H₄ = H₃ := by
  ext z; simpa [jacobi_g, sub_eq_zero] using congr_fun jacobi_g_eq_zero z

noncomputable def thetaDelta_f : ℍ → ℂ := H₂ * (H₃ * H₄)

noncomputable def thetaDeltaFun : ℍ → ℂ := ((256 : ℂ)⁻¹) • (thetaDelta_f ^ 2)

lemma thetaDeltaFun_div_exp_tendsto_atImInfty :
    Tendsto (fun z : ℍ => thetaDeltaFun z / cexp (2 * π * I * (z : ℂ))) atImInfty (𝓝 1) := by
  -- Rewrite `thetaDeltaFun / exp(2π i z)` using the asymptotics of theta functions.
  -- For `Θ₂`, divide out the factor `exp(π i z / 4)` (which is `q^(1/8)`).
  let g : ℍ → ℂ := fun z => jacobiTheta₂ (z / 2) z
  let h : ℍ → ℂ := fun z => jacobiTheta₂ 0 z
  let k : ℍ → ℂ := fun z => jacobiTheta₂ (1 / 2 : ℂ) z
  have hg : Tendsto g atImInfty (𝓝 2) := jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  have hh : Tendsto h atImInfty (𝓝 1) := by
    simpa [h] using jacobiTheta₂_zero_apply_tendsto_atImInfty
  have hk : Tendsto k atImInfty (𝓝 1) := by
    simpa [k] using jacobiTheta₂_half_apply_tendsto_atImInfty
  have hghk : Tendsto (fun z : ℍ => g z * h z * k z) atImInfty (𝓝 (2 : ℂ)) := by
    simpa [mul_assoc] using hg.mul (hh.mul hk)
  have : Tendsto (fun z : ℍ => (g z * h z * k z) ^ 8 / (256 : ℂ)) atImInfty (𝓝 1) := by
    have hlim := (hghk.pow 8).mul (tendsto_const_nhds (x := (256 : ℂ)⁻¹))
    simpa [div_eq_mul_inv, (by norm_num : (2 : ℂ) ^ 8 * (256 : ℂ)⁻¹ = 1)] using hlim
  have hrewrite :
      (fun z : ℍ => thetaDeltaFun z / cexp (2 * π * I * (z : ℂ))) =
        fun z : ℍ => (g z * h z * k z) ^ 8 / (256 : ℂ) := by
    funext z
    have hΘ₂ : Θ₂ z = cexp (π * I * (z : ℂ) / 4) * g z := by simpa [g] using Θ₂_as_jacobiTheta₂ z
    have hΘ₃ : Θ₃ z = h z := by simpa [h] using Θ₃_as_jacobiTheta₂ z
    have hΘ₄ : Θ₄ z = k z := by simpa [k] using Θ₄_as_jacobiTheta₂ z
    have hfz2 : (thetaDelta_f z) ^ 2 = (Θ₂ z * Θ₃ z * Θ₄ z) ^ 8 := by
      dsimp [thetaDelta_f, H₂, H₃, H₄]; ring
    have hΘprod : Θ₂ z * Θ₃ z * Θ₄ z = cexp (π * I * (z : ℂ) / 4) * (g z * h z * k z) := by
      rw [hΘ₂, hΘ₃, hΘ₄]; ring
    have hΘ8 : (Θ₂ z * Θ₃ z * Θ₄ z) ^ 8 =
        cexp (2 * π * I * (z : ℂ)) * (g z * h z * k z) ^ 8 := by
      rw [hΘprod, mul_pow, ← Complex.exp_nat_mul]; congr 1; ring
    simp only [thetaDeltaFun, Pi.smul_apply, smul_eq_mul, Pi.pow_apply, hfz2, hΘ8]
    field_simp
  simpa [hrewrite] using this

/-- Jacobi's identity relating `Delta` to the product `H₂ * H₃ * H₄`. -/
public lemma Delta_eq_H₂_H₃_H₄ (τ : ℍ) :
    Delta τ = ((H₂ τ) * (H₃ τ) * (H₄ τ))^2 / (256 : ℂ) := by
  -- The product `H₂ * H₃ * H₄` is anti-invariant under both `S` and `T` (at weight 6).
  have hslash3 (A : SL(2, ℤ)) :
      (thetaDelta_f ∣[(6 : ℤ)] A) =
        (H₂ ∣[(2 : ℤ)] A) * ((H₃ ∣[(2 : ℤ)] A) * (H₄ ∣[(2 : ℤ)] A)) := by
    have h34 : ((H₃ * H₄) ∣[(4 : ℤ)] A) = (H₃ ∣[(2 : ℤ)] A) * (H₄ ∣[(2 : ℤ)] A) := by
      simpa [(by norm_num : (4 : ℤ) = 2 + 2)] using mul_slash_SL2 2 2 A H₃ H₄
    have h234 : ((H₂ * (H₃ * H₄)) ∣[(6 : ℤ)] A) =
        (H₂ ∣[(2 : ℤ)] A) * ((H₃ * H₄) ∣[(4 : ℤ)] A) := by
      simpa [(by norm_num : (6 : ℤ) = 2 + 4), mul_assoc] using mul_slash_SL2 2 4 A H₂ (H₃ * H₄)
    simp [thetaDelta_f, h234, h34]
  have hprod_S : (thetaDelta_f ∣[(6 : ℤ)] S) = -thetaDelta_f := by
    rw [hslash3 S, H₂_S_action, H₃_S_action, H₄_S_action]
    ext z; simp [thetaDelta_f, mul_left_comm, mul_comm]
  have hprod_T : (thetaDelta_f ∣[(6 : ℤ)] T) = -thetaDelta_f := by
    rw [hslash3 T, H₂_T_action, H₃_T_action, H₄_T_action]
    ext z; simp [thetaDelta_f, mul_comm]
  -- Squaring removes the sign, so `thetaDeltaFun` is invariant under `S` and `T` at weight 12.
  have thetaDeltaFun_action (g : SL(2, ℤ)) (hg : (thetaDelta_f ∣[(6 : ℤ)] g) = -thetaDelta_f) :
      (thetaDeltaFun ∣[(12 : ℤ)] g) = thetaDeltaFun := by
    have hsq : ((thetaDelta_f ^ 2) ∣[(12 : ℤ)] g) = thetaDelta_f ^ 2 := by
      simpa [pow_two, (by norm_num : (12 : ℤ) = 6 + 6), hg] using
        mul_slash_SL2 6 6 g thetaDelta_f thetaDelta_f
    dsimp [thetaDeltaFun]; rw [SL_smul_slash]; simp [hsq]
  -- Build a level-1 modular form out of `thetaDeltaFun`.
  have thetaDeltaFun_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) thetaDeltaFun := by
    have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) thetaDelta_f := by
      simpa [thetaDelta_f] using
        H₂_SIF_MDifferentiable.mul (H₃_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable)
    have hsq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaDelta_f ^ 2) := by simpa [pow_two] using hf.mul hf
    simpa [thetaDeltaFun] using hsq.const_smul ((256 : ℂ)⁻¹)
  -- `thetaDeltaFun` is zero at `i∞`, hence bounded there.
  have thetaDeltaFun_tendsto_atImInfty : Tendsto thetaDeltaFun atImInfty (𝓝 0) := by
    have hf0 : Tendsto thetaDelta_f atImInfty (𝓝 0) := by
      simpa [thetaDelta_f, mul_assoc] using
        H₂_tendsto_atImInfty.mul (H₃_tendsto_atImInfty.mul H₄_tendsto_atImInfty)
    simpa [thetaDeltaFun, Pi.smul_apply, smul_eq_mul, mul_zero] using
      tendsto_const_nhds.mul (hf0.pow 2)
  -- Package as a `CuspForm` via `cuspFormOfSIFTendstoZero`.
  let thetaDelta_CF : CuspForm (Γ 1) 12 :=
    cuspFormOfSIFTendstoZero
      { toFun := thetaDeltaFun
        slash_action_eq' := slashaction_generators_GL2R thetaDeltaFun 12
          (thetaDeltaFun_action S hprod_S) (thetaDeltaFun_action T hprod_T) }
      thetaDeltaFun_holo thetaDeltaFun_tendsto_atImInfty
  have hthetaDeltaFun_coe : (thetaDelta_CF : ℍ → ℂ) = thetaDeltaFun := rfl
  have hr : Module.finrank ℂ (CuspForm (Γ 1) 12) = 1 := by
    have e := CuspForms_iso_Modforms (12 : ℤ)
    apply Module.finrank_eq_of_rank_eq
    rw [LinearEquiv.rank_eq e]
    simp only [Int.reduceSub, Nat.cast_one]; exact ModularForm.levelOne_weight_zero_rank_one
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).1 hr thetaDelta_CF
  have hlim_Delta :
      Tendsto (fun z : ℍ => Delta z / cexp (2 * π * I * (z : ℂ))) atImInfty (𝓝 1) := by
    have hrew : (fun z : ℍ => Delta z / cexp (2 * π * I * (z : ℂ))) =
        fun z : ℍ => ∏' (n : ℕ), (1 - cexp (2 * π * I * (↑n + 1) * (z : ℂ))) ^ 24 := by
      funext z; simp [Delta_apply, Δ, div_eq_mul_inv, mul_left_comm, mul_comm]
    simpa [hrew] using Delta_boundedfactor
  have hlim_thetaDeltaCF :
      Tendsto (fun z : ℍ => (thetaDelta_CF z) / cexp (2 * π * I * (z : ℂ))) atImInfty (𝓝 1) := by
    simpa [hthetaDeltaFun_coe] using thetaDeltaFun_div_exp_tendsto_atImInfty
  have hEqCF : thetaDelta_CF = Delta := by
    have hlim' : Tendsto (fun z : ℍ => (thetaDelta_CF z) / cexp (2 * π * I * (z : ℂ)))
        atImInfty (𝓝 c) := by
      have hEqFun : (thetaDelta_CF : ℍ → ℂ) = fun z => (c : ℂ) * Delta z := by
        ext z
        simpa [Pi.smul_apply, smul_eq_mul] using
          congrArg (fun f : CuspForm (Γ 1) 12 => (f : ℍ → ℂ) z) hc.symm
      simp_rw [hEqFun, mul_div_assoc]
      simpa using tendsto_const_nhds.mul hlim_Delta
    rw [← hc, tendsto_nhds_unique hlim' hlim_thetaDeltaCF, one_smul]
  simpa [thetaDeltaFun, thetaDelta_f, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using
    (congrFun (congrArg DFunLike.coe hEqCF) τ : thetaDelta_CF τ = Delta τ).symm

/-- The product `H₂ z * H₃ z * H₄ z` is nonzero for `z ∈ ℍ`. -/
public lemma H₂_mul_H₃_mul_H₄_ne_zero (z : ℍ) : H₂ z * H₃ z * H₄ z ≠ 0 := by
  have hD : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
  have hEq : (Δ z : ℂ) = ((H₂ z) * (H₃ z) * (H₄ z)) ^ 2 / (256 : ℂ) := by
    simpa [Delta_apply] using (Delta_eq_H₂_H₃_H₄ z)
  intro h0
  exact hD (by simp [hEq, h0])

/-- The function `H₂` does not vanish on `ℍ`. -/
public lemma H₂_ne_zero (z : ℍ) : H₂ z ≠ 0 := by
  simpa using (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (H₂_mul_H₃_mul_H₄_ne_zero z)).1).1

/-- The function `H₃` does not vanish on `ℍ`. -/
public lemma H₃_ne_zero (z : ℍ) : H₃ z ≠ 0 := by
  simpa using (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (H₂_mul_H₃_mul_H₄_ne_zero z)).1).2

/-- The function `H₄` does not vanish on `ℍ`. -/
public lemma H₄_ne_zero (z : ℍ) : H₄ z ≠ 0 := by
  simpa using (mul_ne_zero_iff.mp (H₂_mul_H₃_mul_H₄_ne_zero z)).2
