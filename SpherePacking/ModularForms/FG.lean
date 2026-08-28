/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import SpherePacking.ForMathlib.MDifferentiableFunProp
public import SpherePacking.ModularForms.Derivative
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.ModularForms.EisensteinAsymptotics
public import SpherePacking.ModularForms.JacobiTheta.Basic
public import SpherePacking.ModularForms.JacobiTheta.Derivative
public import SpherePacking.ModularForms.QExpansion
public import SpherePacking.ModularForms.RamanujanIdentities
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.ModularForms.tsumderivWithin
public import SpherePacking.Tactic.TendstoCont

/-!
# The Modular Forms `F` and `G`

This file develops the quasimodular forms `F = (E₂ E₄ - E₆) ^ 2` and
`G = H₂ ^ 3 (2 H₂ ^ 2 + 5 H₂ H₄ + 5 H₄ ^ 2)` used in the construction of the magic function.

## Main results

* `MLDE_F`, `MLDE_G`: the modular linear differential equations satisfied by `F` and `G`.
* `F_imag_axis_pos`, `G_imag_axis_pos`: `F` and `G` are positive on the imaginary axis.
* `F_vanishing_order`, `G_vanishing_order`: the vanishing orders `2` and `3/2` at `i∞`.
* `FmodG_strictAntiOn`: `t ↦ F(it) / G(it)` is strictly decreasing on `(0, ∞)`.
* `FmodG_rightLimitAt_zero`: its right limit at `0` is `18 π⁻²`.
* `FG_inequality_1`, `FG_inequality_2`: the resulting bounds `F(it) < 18 π⁻² G(it)`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Filter Complex ModularGroup SlashAction
open scoped Real Manifold CongruenceSubgroup ArithmeticFunction.sigma UpperHalfPlane

/-- `F = (E₂ E₄ - E₆) ^ 2`, a quasimodular form of weight `12`; it equals `9 (D E₄) ^ 2`. -/
noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

/-- `F₁ = E₂ E₄ - E₆`, the square root of `F`. -/
noncomputable def F₁ := E₂ * E₄.toFun - E₆.toFun

/-- `G = H₂ ^ 3 (2 H₂ ^ 2 + 5 H₂ H₄ + 5 H₄ ^ 2)`, built from the theta functions `H₂ = Θ₂ ^ 4` and
`H₄ = Θ₄ ^ 4`. -/
noncomputable def G := H₂ ^ 3 * ((2 : ℝ) • H₂ ^ 2 + (5 : ℝ) • H₂ * H₄ + (5 : ℝ) • H₄ ^ 2)

/-- `negDE₂ = -D E₂`, which has positive `q`-coefficients (`negDE₂_qexp`). -/
noncomputable def negDE₂ := - (D E₂)

/-- `L₁₀ = (D F) G - F (D G)`, the Wronskian of `F` and `G`; its sign governs the monotonicity of
`F / G` on the imaginary axis. -/
noncomputable def L₁₀ := (D F) * G - F * (D G)

/-- `L₁₀` evaluated pointwise. -/
lemma L₁₀_eq_FD_G_sub_F_DG (z : ℍ) : L₁₀ z = D F z * G z - F z * D G z := rfl

/-- The real function `t ↦ F(it)` on the imaginary axis (`F` is real there, `F_imag_axis_real`). -/
noncomputable def FReal (t : ℝ) : ℝ := (F.resToImagAxis t).re

/-- The real function `t ↦ G(it)` on the imaginary axis (`G` is real there, `G_imag_axis_real`). -/
noncomputable def GReal (t : ℝ) : ℝ := (G.resToImagAxis t).re

/-- The ratio `t ↦ F(it) / G(it)` on the imaginary axis. -/
noncomputable def FmodGReal (t : ℝ) : ℝ := FReal t / GReal t

/-- `F(it)` is the real number `FReal t`. -/
theorem F_eq_FReal (t : ℝ) : F.resToImagAxis t = FReal t :=
  ResToImagAxis.Real.eq_real_part (by unfold F; fun_prop) t

/-- `G(it)` is the real number `GReal t`. -/
theorem G_eq_GReal (t : ℝ) : G.resToImagAxis t = GReal t :=
  ResToImagAxis.Real.eq_real_part (by unfold G; fun_prop) t

/-- `F = 9 (D E₄)²`, by Ramanujan's formula `D E₄ = (E₂ E₄ - E₆) / 3`. -/
theorem F_eq_nine_DE₄_sq : F = (9 : ℂ) • (D E₄.toFun) ^ 2 := by
  ext z
  simp only [F, ramanujan_E₄, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply,
    Pi.inv_apply, Pi.ofNat_apply, smul_eq_mul]
  ring

/-- `G` with complex scalars, the form of the definition that `fun_prop` handles. -/
lemma G_eq : G = H₂ ^ 3 * ((2 : ℂ) • H₂ ^ 2 + (5 : ℂ) • H₂ * H₄ + (5 : ℂ) • H₄ ^ 2) := by
  ext τ
  simp [G]

/-- `F` is holomorphic. -/
@[fun_prop]
theorem F_holo : MDiff F := by unfold F; fun_prop

/-- `G` is holomorphic. -/
@[fun_prop]
theorem G_holo : MDiff G := by rw [G_eq]; fun_prop

/-- `∂₁₀ F` is holomorphic. -/
theorem SerreF_holo : MDiff (serre_D 10 F) := by unfold F; fun_prop

/-- `∂₁₀ G` is holomorphic. -/
theorem SerreG_holo : MDiff (serre_D 10 G) := by rw [G_eq]; fun_prop

/-- `L₁₀` is holomorphic. -/
theorem L₁₀_holo : MDiff L₁₀ := by unfold L₁₀; fun_prop

/-- `FReal` is differentiable at every `t > 0`. -/
theorem FReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ FReal t :=
  (hasDerivAt_resToImagAxis_re F_holo ht).differentiableAt

/-- `GReal` is differentiable at every `t > 0`. -/
theorem GReal_Differentiable {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ GReal t :=
  (hasDerivAt_resToImagAxis_re G_holo ht).differentiableAt

/-- The discriminant `Δ = 1728⁻¹ (E₄ ^ 3 - E₆ ^ 2)`, as an identity of functions on `ℍ`. -/
private lemma Δ_eq_E₄_cube_sub_E₆_sq : Δ = 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2) :=
  funext fun z ↦ (ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z).trans (div_eq_inv_mul _ _)

/-- The modular linear differential equation satisfied by `F`. -/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * E₄.toFun * F + 7200 * Δ * negDE₂ := by
  change serre_D 12 (D F - 10 * 12⁻¹ * E₂ * F) = _
  simp (disch := fun_prop) only [serre_D_eq, F, Δ_eq_E₄_cube_sub_E₆_sq, negDE₂, D_sub, D_add, D_mul,
    D_sq, ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
  ext z
  simp only [pi_ofNat_eq_const, pi_inv_const_eq_const, D_const, Pi.sub_apply, Pi.add_apply,
    Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.zero_apply, Function.const_apply]
  ring

/-- Modular linear differential equation satisfied by `G`. -/
theorem MLDE_G : serre_D 12 (serre_D 10 G) = 5 * 6⁻¹ * E₄.toFun * G - 640 * Δ * H₂ := by
  change serre_D 12 (D G - 10 * 12⁻¹ * E₂ * G) = _
  simp (disch := fun_prop) only [G_eq, D_mul, D_cube, D_H₂, D_add, D_smul, D_sq, D_H₄, serre_D_eq,
    D_sub, ramanujan_E₂, E₄_eq_H_sum_sq]
  ext z
  simp only [pi_ofNat_eq_const, D_const, pi_inv_const_eq_const, Pi.sub_apply, Pi.add_apply,
    Pi.mul_apply, Pi.zero_apply, Pi.pow_apply, Function.const_apply, Pi.smul_apply, smul_eq_mul,
    H_sum_sq, Δ_eq_H₂_H₃_H₄, ← jacobi_identity]
  ring

/-- The `q`-series `∑' n : ℕ+, n ^ a * σ b n * exp (2 π i n z)` is summable for `z : ℍ`. -/
lemma sigma_qexp_summable_generic (a b : ℕ) (z : UpperHalfPlane) :
    Summable (fun n : ℕ+ ↦ (n : ℂ) ^ a * (ArithmeticFunction.sigma b n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z)) := by
  refine ((summable_norm_pow_mul_geometric_of_norm_lt_one (a + b + 1)
    (norm_exp_two_pi_I_lt_one z)).comp_injective PNat.coe_injective).of_norm_bounded fun n ↦ ?_
  rw [show (2 * π * I * n * z : ℂ) = n * (2 * π * I * z) by ring, Complex.exp_nat_mul]
  simp only [Function.comp_apply, norm_mul, norm_pow, Complex.norm_natCast]
  rw [add_assoc, pow_add]
  gcongr
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ b n

/-- The `q`-expansion `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`. This restates Mathlib's
`EisensteinSeries.E2_eq_tsum_cexp` with `cexp (2πi n z)` in place of `𝕢 z ^ n`. -/
lemma E₂_sigma_qexp (z : UpperHalfPlane) :
    E₂ z = 1 - 24 * ∑' (n : ℕ+), (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) := by
  simp [E₂, EisensteinSeries.E2_eq_tsum_cexp, ← Complex.exp_nat_mul, mul_comm, mul_left_comm,
    mul_assoc]

/-- Summable bound on compact sets for the terms of the differentiated `σ_k` `q`-series. -/
lemma sigma_qexp_deriv_bound_generic (k : ℕ) :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (z : K),
        ‖(ArithmeticFunction.sigma k n : ℂ) * (2 * Real.pi * Complex.I * n) *
          Complex.exp (2 * Real.pi * Complex.I * n * z.1)‖ ≤ u n := by
  intro K hK hKc
  obtain ⟨u₀, hu₀_sum, hu₀_bound⟩ := iter_deriv_comp_bound3 K hK hKc (k + 2)
  refine ⟨fun n ↦ u₀ n, hu₀_sum.subtype _, fun n z ↦ le_trans ?_ (hu₀_bound n z)⟩
  have hσ : (ArithmeticFunction.sigma k n : ℝ) ≤ (2 * π * n) ^ (k + 1) :=
    le_trans (by exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n) <| pow_le_pow_left₀
      (by positivity) (le_mul_of_one_le_left (by positivity) (by linarith [Real.two_le_pi])) _
  simpa [abs_of_pos Real.pi_pos, Real.pi_pos, pow_succ] using hσ

/-- `E₄ = 1 + 240 ∑' n : ℕ+, σ₃ n qⁿ`. -/
lemma E₄_sigma_qexp (z : UpperHalfPlane) :
    E₄ z = 1 + 240 * ∑' (n : ℕ+), (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) := by
  refine (EisensteinSeries.q_expansion_bernoulli (by norm_num : 3 ≤ 4) (by decide) z).trans ?_
  norm_num [bernoulli, bernoulli'_four, ← Complex.exp_nat_mul, mul_comm, mul_assoc, mul_left_comm]

/-- Termwise differentiation of a `c₀ + c • ∑' n : ℕ+, a n * qⁿ` expansion: if a holomorphic `g`
agrees pointwise with such a series (`c ≠ 0`), then `D g z = c * ∑' n, n * a n * qⁿ`. -/
private lemma D_qexp_const_add_smul {g : ℍ → ℂ} {c₀ c : ℂ} {a : ℕ+ → ℂ} (hc : c ≠ 0)
    (hg_md : MDiff g)
    (hg : ∀ w : ℍ, g w = c₀ + c * ∑' n : ℕ+, a n * cexp (2 * π * Complex.I * n * w))
    (hsum : ∀ w : ℍ, Summable fun n : ℕ+ ↦ a n * cexp (2 * π * Complex.I * n * w))
    (hbound : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (k : K),
        ‖a n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖ ≤ u n) (z : ℍ) :
    D g z = c * ∑' n : ℕ+, n * a n * cexp (2 * π * Complex.I * n * z) := by
  let f : ℍ → ℂ := fun w ↦ ∑' n : ℕ+, a n * cexp (2 * π * Complex.I * n * w)
  have hDf : D f z = ∑' n : ℕ+, n * a n * cexp (2 * π * Complex.I * n * z) :=
    D_qexp_tsum_pnat a z (hsum z) hbound
  have hf_md : MDiff f := by
    have h : f = c⁻¹ • fun w ↦ g w - c₀ := by
      ext w
      rw [Pi.smul_apply, hg w, smul_eq_mul, add_sub_cancel_left, inv_mul_cancel_left₀ hc]
    rw [h]
    exact (hg_md.sub mdifferentiable_const).const_smul _
  have hg_eq : g = (fun _ ↦ c₀) + c • f := by
    ext w
    simp [f, hg w]
  have hD_const : D (fun _ : ℍ ↦ c₀) z = 0 := congrFun (D_const c₀) z
  rw [hg_eq, congrFun (D_add _ _ mdifferentiable_const (hf_md.const_smul _)) z, Pi.add_apply,
    hD_const, zero_add, congrFun (D_smul c f hf_md) z, Pi.smul_apply, smul_eq_mul, hDf]

/-- `D E₄ = 240 ∑' n : ℕ+, n σ₃ n qⁿ`, by differentiating the `q`-expansion of `E₄` termwise. -/
theorem DE₄_qexp (z : UpperHalfPlane) :
    D E₄.toFun z = 240 * ∑' (n : ℕ+), (n : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) :=
  D_qexp_const_add_smul (by norm_num) E₄.holo' E₄_sigma_qexp
    (fun w ↦ by simpa using sigma_qexp_summable_generic 0 3 w)
    (sigma_qexp_deriv_bound_generic 3) z

/-- `E₂ E₄ - E₆ = 720 ∑' n : ℕ+, n σ₃ n qⁿ`, since `E₂ E₄ - E₆ = 3 D E₄` (`ramanujan_E₄`). -/
theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    E₂ z * E₄ z - E₆ z = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) := by
  have h : D E₄.toFun z = 3⁻¹ * (E₂ z * E₄ z - E₆ z) := congrFun ramanujan_E₄ z
  linear_combination -3 * h + 3 * DE₄_qexp z

/-- Each term `n σ_k n exp (-2πnt)` of a differentiated `σ_k` `q`-series is positive at `z = it`. -/
private lemma sigma_qexp_term_re_pos (k : ℕ) (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    0 < ((n : ℂ) * (ArithmeticFunction.sigma k n : ℂ) *
      cexp (2 * π * I * n * (⟨I * t, by simp [ht]⟩ : ℍ))).re := by
  rw [mul_right_comm (2 * π * I), exp_imag_axis_arg t ht n]
  simp only [Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im, mul_zero, sub_zero,
    Complex.natCast_re, Complex.natCast_im]
  refine mul_pos (mul_pos ?_ ?_) (Real.exp_pos _)
  · exact_mod_cast n.pos
  · exact_mod_cast ArithmeticFunction.sigma_pos k n n.ne_zero

/-- A differentiated `σ_k` `q`-series has positive real part at `z = it` for `t > 0`. -/
private lemma sigma_qexp_tsum_re_pos (k : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < (∑' n : ℕ+, (n : ℂ) * (ArithmeticFunction.sigma k n : ℂ) *
      cexp (2 * π * I * n * (⟨I * t, by simp [ht]⟩ : ℍ))).re := by
  have hsum : Summable fun n : ℕ+ ↦ (n : ℂ) * (ArithmeticFunction.sigma k n : ℂ) *
      cexp (2 * π * I * n * (⟨I * t, by simp [ht]⟩ : ℍ)) := by
    simpa [pow_one] using sigma_qexp_summable_generic 1 k ⟨I * t, by simp [ht]⟩
  rw [Complex.re_tsum hsum]
  exact Summable.tsum_pos ⟨_, Complex.hasSum_re hsum.hasSum⟩
    (fun n ↦ (sigma_qexp_term_re_pos k t ht n).le) 1 (sigma_qexp_term_re_pos k t ht 1)

/-- `D E₄` is real on the imaginary axis. -/
lemma DE₄_imag_axis_real : ResToImagAxis.Real (D E₄.toFun) := by fun_prop

/-- The real part of `(D E₄)(it)` is positive for `t > 0`. -/
lemma DE₄_imag_axis_re_pos (t : ℝ) (ht : 0 < t) :
    0 < ((D E₄.toFun).resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, DE₄_qexp, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  exact mul_pos (by norm_num) (sigma_qexp_tsum_re_pos 3 t ht)

/-- `D E₄` is real and positive on the imaginary axis. -/
@[fun_prop]
lemma DE₄_imag_axis_pos : ResToImagAxis.Pos (D E₄.toFun) :=
  ⟨DE₄_imag_axis_real, DE₄_imag_axis_re_pos⟩

/-- `negDE₂ = 24 ∑' n : ℕ+, n σ₁ n qⁿ`, by differentiating the `q`-expansion of `E₂` termwise. -/
theorem negDE₂_qexp (z : UpperHalfPlane) :
    negDE₂ z = 24 * ∑' (n : ℕ+), (n : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * n * z) := by
  rw [negDE₂, Pi.neg_apply, neg_eq_iff_eq_neg, ← neg_mul]
  exact D_qexp_const_add_smul (c₀ := 1) (by norm_num) E₂_holo'
    (fun w ↦ by rw [E₂_sigma_qexp]; ring)
    (fun w ↦ by simpa using sigma_qexp_summable_generic 0 1 w)
    (sigma_qexp_deriv_bound_generic 1) z

/-- `negDE₂` is real on the imaginary axis. -/
lemma negDE₂_imag_axis_real : ResToImagAxis.Real negDE₂ := by unfold negDE₂; fun_prop

/-- The real part of `negDE₂(it)` is positive for `t > 0`. -/
lemma negDE₂_imag_axis_re_pos (t : ℝ) (ht : 0 < t) :
    0 < (negDE₂.resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, negDE₂_qexp, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  exact mul_pos (by norm_num) (sigma_qexp_tsum_re_pos 1 t ht)

/-- `negDE₂` is real and positive on the imaginary axis. -/
@[fun_prop]
lemma negDE₂_imag_axis_pos : ResToImagAxis.Pos negDE₂ :=
  ⟨negDE₂_imag_axis_real, negDE₂_imag_axis_re_pos⟩

/-!
## Imaginary Axis Properties

Properties of `F` and `G` restricted to the positive imaginary axis `z = it`.
-/

section ImagAxisProperties

/-- `G(it) > 0` for all `t > 0` (blueprint Lemma 8.6): all factors of `G` are positive there. -/
@[fun_prop]
theorem G_imag_axis_pos : ResToImagAxis.Pos G := by unfold G; fun_prop (disch := positivity)

/-- `G(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem G_imag_axis_real : ResToImagAxis.Real G := G_imag_axis_pos.1

/-- `F(it) > 0` for all `t > 0`, since `F = 9 (D E₄)²` and `D E₄ > 0` on the imaginary axis. -/
@[fun_prop]
theorem F_imag_axis_pos : ResToImagAxis.Pos F := by
  rw [F_eq_nine_DE₄_sq]
  fun_prop (disch := positivity)

/-- `F(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem F_imag_axis_real : ResToImagAxis.Real F := F_imag_axis_pos.1

/-- `F₁(it)` is real for all `t > 0`. -/
theorem F₁_imag_axis_real : ResToImagAxis.Real F₁ := by unfold F₁; fun_prop

end ImagAxisProperties

/-- `L₁₀` is also the Wronskian of the weight-`10` Serre derivatives, the `E₂` terms cancelling. -/
private lemma L₁₀_eq_serre_D : L₁₀ = serre_D 10 F * G - F * serre_D 10 G := by
  change D F * G - F * D G = (D F - 10 * 12⁻¹ * E₂ * F) * G - F * (D G - 10 * 12⁻¹ * E₂ * G)
  ring

/-- `∂₂₂ L₁,₀ = (∂₁₂ ∂₁₀ F) G - F (∂₁₂ ∂₁₀ G)`, by the Leibniz rule for Serre derivatives. -/
private lemma serre_D_22_L₁₀_eq :
    serre_D 22 L₁₀ = serre_D 12 (serre_D 10 F) * G - F * serre_D 12 (serre_D 10 G) := by
  have h₀ := serre_D_sub 22 (serre_D 10 F * G) (F * serre_D 10 G) (SerreF_holo.mul G_holo)
    (F_holo.mul SerreG_holo)
  have h₁ := serre_D_mul 12 10 (serre_D 10 F) G SerreF_holo G_holo
  have h₂ := serre_D_mul 10 12 F (serre_D 10 G) F_holo SerreG_holo
  norm_num at h₀ h₁ h₂
  rw [L₁₀_eq_serre_D, h₀, h₁, h₂]
  ring

/-!
### Serre Derivative Positivity of L₁,₀

We compute `∂₂₂ L₁,₀` explicitly via the modular linear differential equations for `F` and `G`,
and show it is positive on the imaginary axis.
-/

/-- `∂₂₂ L₁,₀(it) > 0` for all `t > 0` (blueprint Corollary 8.9): the differential equations for
`F` and `G` give `∂₂₂ L₁,₀ = Δ (7200 (-E₂') G + 640 H₂ F)`, and every factor is positive. -/
private theorem serre_D_L₁₀_pos_imag_axis : ResToImagAxis.Pos (serre_D 22 L₁₀) := by
  have h_eq : serre_D 22 L₁₀ = Δ * ((7200 : ℝ) • (negDE₂ * G) + (640 : ℝ) • (H₂ * F)) := by
    rw [serre_D_22_L₁₀_eq, MLDE_F, MLDE_G]
    ext z
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.ofNat_apply,
      Pi.inv_apply, real_smul, ofReal_ofNat]
    ring
  rw [h_eq]
  have := Δ_imag_axis_pos
  have := H₂_imag_axis_pos
  fun_prop (disch := positivity)

/-!
## Asymptotic Analysis of `F` at Infinity

Vanishing orders and log-derivative limits for the `F`-side analysis, used to establish
`L₁₀_eventually_pos_imag_axis` (large-`t` positivity of `L₁,₀`).
-/

section AsymptoticAnalysis

/-- If `‖a m‖ ≤ (m + 1) ^ p` for all `m`, then `∑' m, a m qᵐ → a 0` as `im(z) → ∞`. -/
private theorem qexp_tendsto_of_poly_bound {a : ℕ → ℂ} {p : ℕ}
    (hbound : ∀ m, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ p) :
    Tendsto (fun z : ℍ ↦ ∑' m : ℕ, a m * cexp (2 * π * I * z * m)) atImInfty (nhds (a 0)) :=
  QExp.tendsto_nat a <| .of_nonneg_of_le (fun _ ↦ by positivity)
    (fun m ↦ mul_le_mul_of_nonneg_right (hbound m) (Real.exp_nonneg _))
    (by exact_mod_cast summable_pow_shift p)

/-- If `f / g → c ≠ 0` as `im(z) → ∞`, then `f` is eventually nonzero. -/
private lemma eventually_ne_zero_of_tendsto_div {f g : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : Tendsto (fun z ↦ f z / g z) atImInfty (nhds c)) : ∀ᶠ z : ℍ in atImInfty, f z ≠ 0 :=
  (h.eventually_ne hc).mono fun _ hz hf ↦ hz (by simp [hf])

/-- `(E₂E₄ - E₆)(z) / exp(2πiz) → 720` as `im(z) → ∞`. -/
theorem E₂E₄_sub_E₆_div_q_tendsto :
    Tendsto (fun z : ℍ ↦ (E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z)) atImInfty (nhds 720) := by
  have h_eq : ∀ z : ℍ, (E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z) =
      720 * ∑' m : ℕ, (↑(m + 1) * ↑(σ 3 (m + 1)) : ℂ) * cexp (2 * π * I * z * m) := fun z ↦ by
    rw [E₂_mul_E₄_sub_E₆ z, tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ (n * σ 3 n *
      cexp (2 * π * I * n * z) : ℂ)), mul_div_assoc, ← tsum_div_const]
    exact congrArg _ (tsum_congr fun m ↦ by push_cast [mul_div_assoc, ← Complex.exp_sub]; ring_nf)
  have hbound : ∀ m : ℕ, ‖(↑(m + 1) * ↑(σ 3 (m + 1)) : ℂ)‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 5 := fun m ↦ by
    exact_mod_cast (Nat.mul_le_mul_left _ (ArithmeticFunction.sigma_le_pow_succ 3 _)).trans_eq
      (by ring)
  simpa [h_eq] using (qexp_tendsto_of_poly_bound hbound).const_mul (720 : ℂ)

/-- The normalized log-derivative of `w ↦ exp (c * w)` is the constant `c / (2πi)`. -/
theorem D_cexp_div (c : ℂ) (z : ℍ) :
    D (fun w ↦ cexp (c * w)) z / cexp (c * z) = c / (2 * π * I) := by
  have h : deriv ((fun w : ℍ ↦ cexp (c * w)) ∘ ⇑ofComplex) (z : ℂ) = cexp (c * z) * (c * 1) :=
    ((eventuallyEq_coe_comp_ofComplex z.2).fun_comp fun w ↦ cexp (c * w)).deriv_eq.trans
      (((hasDerivAt_id (z : ℂ)).const_mul c).cexp).deriv
  simp only [D, h]
  field_simp

/-- If `F z / exp (a * z) → C ≠ 0` at `i∞`, then `D F / F → a / (2πi)`. -/
lemma logderiv_tendsto_of_div_exp_tendsto {F : ℍ → ℂ} (hF : MDiff F) {a C : ℂ} (hC : C ≠ 0)
    (hlim : Tendsto (fun z : ℍ ↦ F z / cexp (a * z)) atImInfty (nhds C)) :
    Tendsto (fun z : ℍ ↦ D F z / F z) atImInfty (nhds (a / (2 * π * I))) := by
  set q : ℍ → ℂ := fun w ↦ cexp (a * w)
  set g : ℍ → ℂ := fun w ↦ F w / q w with hg
  have hq_ne : ∀ w : ℍ, q w ≠ 0 := fun w ↦ Complex.exp_ne_zero _
  have hq_md : MDiff q := fun τ ↦ DifferentiableAt_MDifferentiableAt
    (G := fun t : ℂ ↦ cexp (a * t)) ((differentiableAt_id.const_mul a).cexp)
  have hg_md : MDiff g := MDifferentiable_div hF hq_md hq_ne
  have hDg : Tendsto (D g / g) atImInfty (nhds 0) := by
    simpa using (D_tendsto_zero_of_isBoundedAtImInfty hg_md (hlim.isBigO_one ℝ)).div hlim hC
  have hF_eq : F = q * g := by ext w; simp only [hg, Pi.mul_apply, mul_div_cancel₀ _ (hq_ne w)]
  have key : ∀ᶠ z : ℍ in atImInfty, a / (2 * π * I) + D g z / g z = D F z / F z := by
    filter_upwards [hlim.eventually_ne hC] with z hz
    rw [← D_cexp_div a z, hF_eq, congrFun (D_mul q g hq_md hg_md) z]
    exact div_add_div _ _ (hq_ne z) hz
  simpa using (tendsto_const_nhds.add hDg).congr' key

/-- `F(z) / exp(2πi · 2z) → 720²` as `im(z) → ∞`: `F` vanishes to order 2 at `i∞`. -/
theorem F_vanishing_order : Tendsto (fun z : ℍ ↦ F z / cexp (2 * π * Complex.I * 2 * z))
    atImInfty (nhds (720 ^ 2)) := by
  refine (E₂E₄_sub_E₆_div_q_tendsto.pow 2).congr fun z ↦ ?_
  simp [F, div_pow, ← Complex.exp_nat_mul, mul_comm, mul_left_comm]

/-- `(D F)/F → 2` as `im(z) → ∞`, since `F` vanishes to order 2 at `i∞`. -/
theorem D_F_div_F_tendsto : Tendsto (fun z : ℍ ↦ D F z / F z) atImInfty (nhds (2 : ℂ)) := by
  simpa using logderiv_tendsto_of_div_exp_tendsto F_holo (by norm_num) F_vanishing_order

/-!
### `G`-Side Asymptotic Analysis

Vanishing order and log-derivative limits for `G`, leading to eventual positivity of `L₁,₀`.
-/

/-- `G(z) / exp(2πi · (3/2)z) → 20480` as `im(z) → ∞`: `G` vanishes to order 3/2 at `i∞`. -/
theorem G_vanishing_order :
    Tendsto (fun z : ℍ ↦ G z / cexp (2 * π * I * (3/2) * z)) atImInfty (nhds 20480) := by
  have h : ∀ z : ℍ, G z / cexp (2 * π * I * (3 / 2) * z) =
      (H₂ z / cexp (π * I * z)) ^ 3 * (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) := fun z ↦ by
    simp [G, div_pow, ← Complex.exp_nat_mul]
    ring_nf
  simp_rw [h]
  tendsto_cont [H₂_div_exp_tendsto, H₂_tendsto_atImInfty, H₄_tendsto_atImInfty]

/-- `(D G)/G → 3/2` as `im(z) → ∞`, since `G` vanishes to order 3/2 at `i∞`. -/
theorem D_G_div_G_tendsto : Tendsto (fun z : ℍ ↦ D G z / G z) atImInfty (nhds ((3 : ℂ) / 2)) := by
  simpa using logderiv_tendsto_of_div_exp_tendsto G_holo (by norm_num) G_vanishing_order

/-- `L₁,₀(it)` is real for all `t > 0`. -/
theorem L₁₀_imag_axis_real : ResToImagAxis.Real L₁₀ := by fun_prop [L₁₀]

/-- `lim_{t→∞} L₁,₀(it)/(F(it)G(it)) = 1/2`. -/
theorem L₁₀_div_FG_tendsto : Tendsto (fun t : ℝ ↦ (L₁₀.resToImagAxis t).re /
    ((F.resToImagAxis t).re * (G.resToImagAxis t).re)) atTop (nhds (1 / 2)) := by
  have hF_ne := eventually_ne_zero_of_tendsto_div (by norm_num) F_vanishing_order
  have hG_ne := eventually_ne_zero_of_tendsto_div (by norm_num) G_vanishing_order
  have h : Tendsto (L₁₀ / (F * G)) atImInfty (nhds (2 - 3 / 2)) :=
    (D_F_div_F_tendsto.sub D_G_div_G_tendsto).congr' <| by
      filter_upwards [hF_ne, hG_ne] with z hF hG using div_sub_div _ _ hF hG
  exact ((Complex.continuous_re.tendsto' _ (1 / 2) (by norm_num)).comp
    (tendsto_resToImagAxis_of_tendsto_atImInfty h)).congr
      (ResToImagAxis.Real.re_div_mul_eq F_imag_axis_real G_imag_axis_real)

/-- `L₁,₀(it) > 0` for all sufficiently large `t`. -/
theorem L₁₀_eventually_pos_imag_axis : ResToImagAxis.EventuallyPos L₁₀ := by
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (L₁₀_div_FG_tendsto.eventually_const_lt one_half_pos)
  refine ⟨L₁₀_imag_axis_real, max t₀ 1, by positivity, fun t ht ↦ ?_⟩
  have ht_pos : (0 : ℝ) < t := zero_lt_one.trans_le ((le_max_right t₀ 1).trans ht)
  have hFG := mul_pos (F_imag_axis_pos.2 t ht_pos) (G_imag_axis_pos.2 t ht_pos)
  simpa using (lt_div_iff₀ hFG).mp (ht₀ t ((le_max_left t₀ 1).trans ht))

end AsymptoticAnalysis

/-- `L₁,₀(it) > 0` for all `t > 0`. -/
theorem L₁₀_pos : ResToImagAxis.Pos L₁₀ :=
  antiSerreDerPos L₁₀_holo serre_D_L₁₀_pos_imag_axis L₁₀_eventually_pos_imag_axis

/-!
## Monotonicity of `F / G` on the Imaginary Axis

Proposition 8.12 from the blueprint: the function `FmodGReal t = F(it) / G(it)` is strictly
decreasing on `(0, ∞)`.
-/

/-- `FmodGReal` is differentiable on `(0, ∞)`. -/
theorem FmodGReal_differentiableOn : DifferentiableOn ℝ FmodGReal (Set.Ioi 0) := fun t ht ↦
  ((FReal_Differentiable ht).div (GReal_Differentiable ht)
    (G_imag_axis_pos.2 t ht).ne').differentiableWithinAt

/-- The derivative of `FmodGReal` is `-2π L₁,₀(it) / G(it)²`. -/
theorem deriv_FmodGReal (t : ℝ) (ht : 0 < t) :
    deriv FmodGReal t = (-2 * π) * (L₁₀ ⟨Complex.I * t, by simp [ht]⟩).re /
      (G ⟨Complex.I * t, by simp [ht]⟩).re ^ 2 := by
  have hF_real := F_imag_axis_real t ht
  have hG_real := G_imag_axis_real t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hF_real hG_real
  rw [(show HasDerivAt FmodGReal _ t from
    (hasDerivAt_resToImagAxis_re F_holo ht).div (hasDerivAt_resToImagAxis_re G_holo ht)
      (G_imag_axis_pos.2 t ht).ne').deriv, L₁₀_eq_FD_G_sub_F_DG]
  simp only [GReal, Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, mul_re, sub_re,
    hF_real, hG_real, mul_zero, sub_zero, zero_mul]
  ring

/-- `deriv FmodGReal t < 0` for all `t > 0`. -/
theorem deriv_FmodGReal_neg (t : ℝ) (ht : 0 < t) : deriv FmodGReal t < 0 := by
  rw [deriv_FmodGReal t ht]
  have hL := L₁₀_pos.2 t ht
  have hG := G_imag_axis_pos.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hL hG
  exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) (by positivity)

/-- **Proposition 8.12**: `FmodGReal` is strictly decreasing on `(0, ∞)`. -/
theorem FmodG_strictAntiOn : StrictAntiOn FmodGReal (Set.Ioi 0) :=
  strictAntiOn_of_deriv_neg (convex_Ioi 0) FmodGReal_differentiableOn.continuousOn fun t ht ↦
    deriv_FmodGReal_neg t (by rwa [interior_Ioi] at ht)

/-- Reduce a power of `I * w` via `I ^ 4 = 1`. -/
lemma I_mul_npow (w : ℂ) (n : ℕ) : (I * w) ^ n = I ^ (n % 4) * w ^ n := by
  rw [mul_pow, I_pow_eq_pow_mod]

/-- Functional equation of `F` under the modular inversion `S`. -/
theorem F_functional_equation (z : ℍ) :
    F (S • z) = z ^ 12 * F z - 12 * I * π ^ (-1 : ℤ) * z ^ 11 * (F₁ * E₄.toFun) z
      - 36 * π ^ (-2 : ℤ) * z ^ 10 * (E₄.toFun z) ^ 2 := by
  simp only [F, F₁, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, ModularForm.toFun_eq_coe,
    E₂_S_transform, E₄_S_transform, E₆_S_transform, zpow_neg, zpow_one]
  field_simp [ne_zero z]
  linear_combination (12 * I * (z : ℂ) * π * (E₂ z * E₄ z - E₆ z) * E₄ z + 36 * E₄ z ^ 2) * I_sq

/-- Functional equation of `F` restricted to the imaginary axis. -/
theorem F_functional_equation' {t : ℝ} (ht : 0 < t) :
    FReal (1 / t) = t ^ 12 * FReal t - 12 * π ^ (-1 : ℤ) * t ^ 11 * (F₁ * E₄.toFun).resToImagAxis t
      + 36 * π ^ (-2 : ℤ) * t ^ 10 * (E₄.toFun.resToImagAxis t) ^ 2 := by
  rw [← F_eq_FReal (1 / t), ResToImagAxis.one_div_eq_S_smul F ht, F_functional_equation]
  simp only [I_mul_npow, Nat.reduceMod, I_sq, I_pow_three, F_eq_FReal t,
    ResToImagAxis.I_mul_t_eq F t ht, ResToImagAxis.I_mul_t_eq (F₁ * E₄.toFun) t ht,
    ResToImagAxis.I_mul_t_eq E₄.toFun t ht]
  linear_combination 12 * π ^ (-1 : ℤ) * t ^ 11 * (F₁ * E₄.toFun).resToImagAxis t * I_sq

/-- Functional equation of `G` under the modular inversion `S`. -/
theorem G_functional_equation (z : ℍ) :
    G (S • z) = -z ^ 10 * H₄ z ^ 3 * (2 * H₄ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₂ z ^ 2) := by
  simp only [G, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.pow_apply, real_smul, ofReal_ofNat,
    H₂_S_action', H₄_S_action']
  ring

/-- Functional equation of `G` restricted to the imaginary axis. -/
theorem G_functional_equation' {t : ℝ} (ht : 0 < t) :
    GReal (1 / t) = t ^ 10 * H₄.resToImagAxis t ^ 3
      * (2 * H₄.resToImagAxis t ^ 2 + 5 * H₂.resToImagAxis t * H₄.resToImagAxis t
        + 5 * H₂.resToImagAxis t ^ 2) := by
  rw [← G_eq_GReal (1 / t), ResToImagAxis.one_div_eq_S_smul G ht, G_functional_equation,
    ResToImagAxis.I_mul_t_eq H₂ t ht, ResToImagAxis.I_mul_t_eq H₄ t ht, I_mul_npow, I_sq]
  ring

/-!
### Helper lemmas for the limit computation

The following lemmas establish the asymptotic behavior needed to compute the limit of
`FmodGReal` as `t → 0⁺`.
-/

/-- A level-one modular form tending to `1` at `i∞` satisfies `f - 1 = O(exp(-2π im τ))`. -/
private lemma sub_one_isBigO_exp_atImInfty {k : ℤ} (f : ModularForm Γ(1) k)
    (hf : Tendsto ⇑f atImInfty (nhds 1)) :
    (fun z : ℍ ↦ f z - 1) =O[atImInfty] fun z ↦ Real.exp (-(2 * π) * z.im) := by
  simpa [show valueAtInfty ⇑f = 1 from hf.limUnder_eq] using
    exp_decay_sub_atImInfty one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f (by simp))
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)

/-- `F₁` has exponential decay `O(exp(-2π im τ))` at infinity, as `F₁ = 3 D E₄`. -/
lemma F₁_isBigO_exp_atImInfty : F₁ =O[atImInfty] fun τ ↦ Real.exp (-(2 * π) * τ.im) := by
  have hprod : (fun z ↦ (E₂ z - 1) * E₄ z) =O[atImInfty] fun z ↦ Real.exp (-(2 * π) * z.im) := by
    simpa using E₂_sub_one_isBigO_exp.mul E₄_isBoundedAtImInfty
  rw [show F₁ = (E₂ - 1) * E₄.toFun + (E₄.toFun - 1) - (E₆.toFun - 1) by unfold F₁; ring]
  exact (hprod.add (sub_one_isBigO_exp_atImInfty E₄ E₄_tendsto_one_atImInfty)).sub
    (sub_one_isBigO_exp_atImInfty E₆ E₆_tendsto_one_atImInfty)

/-- `F = F₁ ^ 2` has exponential decay `O(exp(-4π im τ))` at infinity. -/
lemma F_isBigO_exp_atImInfty : F =O[atImInfty] fun τ ↦ Real.exp (-(4 * π) * τ.im) :=
  (F₁_isBigO_exp_atImInfty.pow 2).congr_right fun τ ↦ by rw [← Real.exp_nat_mul]; ring_nf

/-- `F₁ * E₄` has exponential decay `O(exp(-2π im τ))` at infinity, as `E₄` is bounded. -/
lemma F₁_mul_E₄_isBigO_exp_atImInfty :
    (F₁ * E₄.toFun) =O[atImInfty] fun τ ↦ Real.exp (-(2 * π) * τ.im) := by
  simpa [Pi.mul_def] using F₁_isBigO_exp_atImInfty.mul E₄_isBoundedAtImInfty

/-- `s ^ 2 * FReal s` tends to `0` as `s → ∞`. -/
lemma sq_mul_FReal_tendsto_zero : Tendsto (fun s : ℝ ↦ s ^ 2 * FReal s) atTop (nhds 0) :=
  tendsto_pow_mul_resToImagAxis_re_of_isBigO_exp (by positivity) F_isBigO_exp_atImInfty 2

/-- `s * Re ((F₁ * E₄) (i s))` tends to `0` as `s → ∞`. -/
lemma mul_F₁E₄_re_tendsto_zero :
    Tendsto (fun s ↦ s * ((F₁ * E₄.toFun).resToImagAxis s).re) atTop (nhds 0) := by
  simpa using tendsto_pow_mul_resToImagAxis_re_of_isBigO_exp (by positivity)
    F₁_mul_E₄_isBigO_exp_atImInfty 1

/-- The numerator of `FmodGReal (1 / s)` after cancelling `s ^ 10` tends to `36 * π ^ (-2 : ℤ)`. -/
lemma FmodG_numerator_tendsto :
  Tendsto (fun s ↦ s ^ 2 * FReal s
    - 12 * π ^ (-1 : ℤ) * (s * ((F₁ * E₄.toFun).resToImagAxis s).re)
    + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) atTop (nhds (36 * π ^ (-2 : ℤ))) := by
  tendsto_cont [sq_mul_FReal_tendsto_zero, mul_F₁E₄_re_tendsto_zero,
    tendsto_resToImagAxis_of_tendsto_atImInfty E₄_tendsto_one_atImInfty]

/-- The denominator of `FmodGReal (1 / s)` after cancelling `s ^ 10` tends to `2`. -/
lemma FmodG_denominator_tendsto :
  Tendsto (fun s ↦ (H₄.resToImagAxis s).re ^ 3
    * (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
    + 5 * (H₂.resToImagAxis s).re ^ 2)) atTop (nhds 2) := by
  tendsto_cont [tendsto_resToImagAxis_of_tendsto_atImInfty H₂_tendsto_atImInfty,
    tendsto_resToImagAxis_of_tendsto_atImInfty H₄_tendsto_atImInfty]

/-- Real form of the functional equation of `F`:
`F(i/s) = s¹⁰ (s² F(is) - 12π⁻¹ s (F₁E₄)(is) + 36π⁻² E₄(is)²)`. -/
lemma F_functional_eq_real {s : ℝ} (hs : 0 < s) :
    FReal (1 / s) = s ^ 10 * (s ^ 2 * FReal s
      - 12 * π ^ (-1 : ℤ) * (s * ((F₁ * E₄.toFun).resToImagAxis s).re)
      + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) := by
  push_cast [← Complex.ofReal_inj, ← (F₁_imag_axis_real.mul E₄_imag_axis_real).eq_real_part s,
    ← E₄_imag_axis_real.eq_real_part s]
  linear_combination F_functional_equation' hs

/-- Real form of the functional equation of `G`:
`G(i/s) = s¹⁰ H₄(is)³ (2 H₄(is)² + 5 H₂(is) H₄(is) + 5 H₂(is)²)`. -/
lemma G_functional_eq_real {s : ℝ} (hs : 0 < s) :
    GReal (1 / s) = s ^ 10 * (H₄.resToImagAxis s).re ^ 3 *
      (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
        + 5 * (H₂.resToImagAxis s).re ^ 2) := by
  push_cast [← Complex.ofReal_inj, ← H₂_imag_axis_real.eq_real_part s,
    ← H₄_imag_axis_real.eq_real_part s]
  linear_combination G_functional_equation' hs

/-- `lim_{t → 0⁺} F(it) / G(it) = 18 π⁻²` (blueprint Lemma 8.8). -/
theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhds (18 * (π ^ (-2 : ℤ)))) := by
  have hlim : Tendsto (fun s : ℝ ↦ FmodGReal (1 / s)) atTop (nhds (18 * π ^ (-2 : ℤ))) := by
    rw [show (18 : ℝ) * π ^ (-2 : ℤ) = 36 * π ^ (-2 : ℤ) / 2 by ring]
    refine (FmodG_numerator_tendsto.div FmodG_denominator_tendsto two_ne_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [FmodGReal, F_functional_eq_real hs, G_functional_eq_real hs, mul_assoc (s ^ 10)]
    exact (mul_div_mul_left _ _ (pow_ne_zero 10 hs.ne')).symm
  exact (hlim.comp tendsto_inv_nhdsGT_zero).congr fun t ↦ by simp

/-!
### Main inequalities between `F` and `G` on the imaginary axis
-/

/-- `F(it) + 18 π⁻² G(it) > 0` for `t > 0`, since `F` and `G` are both positive on the
imaginary axis. -/
theorem FG_inequality_1 {t : ℝ} (ht : 0 < t) :
    FReal t + 18 * (π ^ (-2 : ℤ)) * GReal t > 0 :=
  add_pos (F_imag_axis_pos.2 t ht) (mul_pos (by positivity) (G_imag_axis_pos.2 t ht))

/-- `F(it) - 18 π⁻² G(it) < 0` for `t > 0`: the ratio `F / G` is strictly antitone on the
imaginary axis with right limit `18 π⁻²` at `0`, so it stays strictly below `18 π⁻²`. -/
theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  have hlt : FmodGReal t < 18 * (π ^ (-2 : ℤ)) :=
    (FmodG_strictAntiOn (half_pos ht) ht (half_lt_self ht)).trans_le <|
      ge_of_tendsto FmodG_rightLimitAt_zero <| by
        filter_upwards [Ioo_mem_nhdsGT (half_pos ht)] with s hs
        exact (FmodG_strictAntiOn hs.1 (half_pos ht) hs.2).le
  exact sub_neg.mpr ((div_lt_iff₀ (G_imag_axis_pos.2 t ht)).mp hlt)
