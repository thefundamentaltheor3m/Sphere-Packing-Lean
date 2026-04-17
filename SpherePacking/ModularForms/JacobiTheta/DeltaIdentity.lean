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
public import SpherePacking.ModularForms.JacobiTheta.SlashActions
public import SpherePacking.ForMathlib.AtImInfty
public import SpherePacking.ForMathlib.Cusps
public import SpherePacking.ForMathlib.SlashActions
public import SpherePacking.ForMathlib.UpperHalfPlane
public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.CuspFormIsoModforms
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.Tactic.TendstoCont
import SpherePacking.Tactic.NormNumI

/-!
# Jacobi theta functions: Jacobi identity and the `Delta` identity

This file proves the classical Jacobi identity `H₂ + H₄ = H₃` (Blueprint Lemma 6.41) using the
dimension-zero vanishing theorem for weight-4 cusp forms on `Γ(1)`. It also proves the identity
expressing the modular discriminant `Delta` as the product `H₂ * H₃ * H₄` (up to a normalization
constant), and derives the non-vanishing of `H₂`, `H₃`, `H₄` on the upper half-plane.

## Main declarations
* `jacobi_identity`
* `Delta_eq_H₂_H₃_H₄`
* `H₂_ne_zero`, `H₃_ne_zero`, `H₄_ne_zero`
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

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

private lemma four_eq_two_add_two : (4 : ℤ) = 2 + 2 := rfl

private lemma jacobi_g_mul_slash (γ : SL(2, ℤ)) :
    ((jacobi_g * jacobi_g) ∣[(4 : ℤ)] γ) =
      (jacobi_g ∣[(2 : ℤ)] γ) * (jacobi_g ∣[(2 : ℤ)] γ) := by
  simpa [four_eq_two_add_two] using (mul_slash_SL2 2 2 γ jacobi_g jacobi_g)

/-- S-invariance of f: f|[4]S = f, because g|[2]S = -g. -/
lemma jacobi_f_S_action : (jacobi_f ∣[(4 : ℤ)] S) = jacobi_f := by
  simpa [jacobi_f_eq_mul, jacobi_g_S_action] using (jacobi_g_mul_slash S)

/-- T-invariance of f: f|[4]T = f, because g|[2]T = -g. -/
lemma jacobi_f_T_action : (jacobi_f ∣[(4 : ℤ)] T) = jacobi_f := by
  simpa [jacobi_f_eq_mul, jacobi_g_T_action] using (jacobi_g_mul_slash T)

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
    rw [summable_jacobiTheta₂_term_iff]
    simp
  · intro n
    have : n = -1 ∨ n = 0 ∨ n ∉ ({-1, 0} : Set ℤ) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rcases this with (rfl | rfl | hn) <;> ring_nf
    · simp
    · simp
    · simp only [hn, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have h₁ (n : ℤ) (z : ℂ) : (π * I * n * z + π * I * n ^ 2 * z) = π * (n + n ^ 2) * z * I := by
        ring_nf
      have h_base' : rexp (-π) ^ ((n : ℝ) + n ^ 2) < 1 := by
        apply Real.rpow_lt_one
        · positivity
        · exact Real.exp_lt_one_iff.mpr (by simpa using (neg_lt_zero.mpr Real.pi_pos))
        convert_to 0 < ((n * (n + 1) : ℤ) : ℝ)
        · push_cast
          ring_nf
        · apply Int.cast_pos.mpr
          by_cases hn' : 0 < n
          · apply mul_pos hn' (by omega)
          · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
            exact mul_pos_of_neg_of_neg (by omega) (by omega)
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
    trans ‖cexp (((π * k + π * k ^ 2 : ℝ) * z) * I)‖
    · apply le_of_eq
      simpa [add_mul] using by ring_nf
    · rw [norm_exp_mul_I, im_ofReal_mul]
      have (n : ℤ) : 0 ≤ (n : ℝ) ^ 2 + n := by
        nth_rw 2 [← mul_one n]
        rw [sq, Int.cast_mul, Int.cast_one, ← mul_add]
        rcases lt_trichotomy (-1) n with (hn | rfl | hn)
        · apply mul_nonneg <;> norm_cast; omega
        · norm_num
        · apply mul_nonneg_of_nonpos_of_nonpos <;> norm_cast <;> omega
      simpa using le_mul_of_one_le_right
        (by rw [← mul_add, add_comm]; exact mul_nonneg Real.pi_nonneg (this k)) hz

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
    · subst hk
      simp [hw0]
    · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hpos : 0 < π * (k : ℝ) ^ 2 := mul_pos Real.pi_pos (sq_pos_of_ne_zero hk')
      have hk_im : Tendsto (fun z : ℍ ↦ (π * (k : ℝ) ^ 2) * z.im) atImInfty atTop :=
        tendsto_im_atImInfty.const_mul_atTop hpos
      have hk_exp : Tendsto (fun z : ℍ ↦ ‖cexp (π * I * k ^ 2 * z)‖) atImInfty (𝓝 0) := by
        simp_rw [mul_right_comm _ I, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← ofReal_intCast,
          ← ofReal_pow, im_ofReal_mul, ← mul_assoc, coe_im]
        exact tendsto_exp_neg_atTop_nhds_zero.comp hk_im
      have : Tendsto (fun z : ℍ ↦ w k * cexp (π * I * k ^ 2 * z)) atImInfty (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using (tendsto_const_nhds.mul hk_exp)
      simpa [hk] using this
  · rw [eventually_atImInfty]
    refine ⟨1, fun z hz k ↦ ?_⟩
    have hwk : ‖w k‖ ≤ 1 := hw k
    have hmul : ‖w k * cexp (π * I * k ^ 2 * z)‖ ≤ ‖cexp (π * I * k ^ 2 * z)‖ := by simpa
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
  -- simp_rw directly below fails
  have (z : ℍ) : ‖cexp (π * I * z / 4)‖ = rexp (-π * z.im / 4) := by
    rw [mul_right_comm, mul_div_right_comm, norm_exp_mul_I]
    simp [neg_div]
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
  have :
      Tendsto (fun z : ℍ => (g z * h z * k z) ^ 8 / (256 : ℂ)) atImInfty (𝓝 1) := by
    have hlim :
        Tendsto (fun z : ℍ => (g z * h z * k z) ^ 8 / (256 : ℂ)) atImInfty
          (𝓝 ((2 : ℂ) ^ 8 / (256 : ℂ))) := by
      simpa [div_eq_mul_inv] using (hghk.pow 8).mul tendsto_const_nhds
    simpa using (show ((2 : ℂ) ^ 8 / (256 : ℂ)) = (1 : ℂ) by norm_num) ▸ hlim
  have hrewrite :
      (fun z : ℍ => thetaDeltaFun z / cexp (2 * π * I * (z : ℂ))) =
        fun z : ℍ => (g z * h z * k z) ^ 8 / (256 : ℂ) := by
    funext z
    have hΘ₂ : Θ₂ z = cexp (π * I * (z : ℂ) / 4) * g z := by
      simpa [g] using (Θ₂_as_jacobiTheta₂ z)
    have hΘ₃ : Θ₃ z = h z := by
      simpa [h] using (Θ₃_as_jacobiTheta₂ z)
    have hΘ₄ : Θ₄ z = k z := by
      simpa [k] using (Θ₄_as_jacobiTheta₂ z)
    have hfz : thetaDelta_f z = (Θ₂ z * Θ₃ z * Θ₄ z) ^ 4 := by
      dsimp [thetaDelta_f, H₂, H₃, H₄]
      ring
    have hfz2 : (thetaDelta_f z) ^ 2 = (Θ₂ z * Θ₃ z * Θ₄ z) ^ 8 := by
      calc
        (thetaDelta_f z) ^ 2 = ((Θ₂ z * Θ₃ z * Θ₄ z) ^ 4) ^ 2 := by
          simp [hfz]
        _ = (Θ₂ z * Θ₃ z * Θ₄ z) ^ 8 := by
          simpa [show 4 * 2 = 8 by norm_num] using (pow_mul (Θ₂ z * Θ₃ z * Θ₄ z) 4 2).symm
    have hΘprod :
        Θ₂ z * Θ₃ z * Θ₄ z = cexp (π * I * (z : ℂ) / 4) * (g z * h z * k z) := by
      grind only
    have hexp : cexp (π * I * (z : ℂ) / 4) ^ 8 = cexp (2 * π * I * (z : ℂ)) := by
      have h := (Complex.exp_nat_mul (π * I * (z : ℂ) / 4) 8).symm
      have harg : (8 : ℂ) * (π * I * (z : ℂ) / 4) = 2 * π * I * (z : ℂ) := by
        ring_nf
      simpa [harg] using h
    have hΘ8 :
        (Θ₂ z * Θ₃ z * Θ₄ z) ^ 8 = cexp (2 * π * I * (z : ℂ)) * (g z * h z * k z) ^ 8 := by
      calc
        (Θ₂ z * Θ₃ z * Θ₄ z) ^ 8 =
            (cexp (π * I * (z : ℂ) / 4) * (g z * h z * k z)) ^ 8 := by
              simp [hΘprod]
        _ = cexp (π * I * (z : ℂ) / 4) ^ 8 * (g z * h z * k z) ^ 8 := by
              simp [mul_pow]
        _ = cexp (2 * π * I * (z : ℂ)) * (g z * h z * k z) ^ 8 :=
              congrArg (fun t : ℂ => t * (g z * h z * k z) ^ 8) hexp
    calc
      thetaDeltaFun z / cexp (2 * π * I * (z : ℂ)) =
          ((256 : ℂ)⁻¹) * (thetaDelta_f z) ^ 2 / cexp (2 * π * I * (z : ℂ)) := by
            simp [thetaDeltaFun, Pi.smul_apply, smul_eq_mul]
      _ = ((256 : ℂ)⁻¹) * (Θ₂ z * Θ₃ z * Θ₄ z) ^ 8 / cexp (2 * π * I * (z : ℂ)) := by
            simp [hfz2]
      _ =
          ((256 : ℂ)⁻¹) *
              (cexp (2 * π * I * (z : ℂ)) * (g z * h z * k z) ^ 8) /
            cexp (2 * π * I * (z : ℂ)) := by
            simp [hΘ8]
      _ = ((256 : ℂ)⁻¹) * (g z * h z * k z) ^ 8 := by
            set a : ℂ := cexp (2 * π * I * (z : ℂ))
            set b : ℂ := (g z * h z * k z) ^ 8
            have ha : a ≠ 0 := by simp [a]
            grind only
      _ = (g z * h z * k z) ^ 8 / (256 : ℂ) := by
            simp [div_eq_mul_inv, mul_left_comm, mul_comm]
  simpa [hrewrite] using this

/-- Jacobi's identity relating `Delta` to the product `H₂ * H₃ * H₄`. -/
public lemma Delta_eq_H₂_H₃_H₄ (τ : ℍ) :
    Delta τ = ((H₂ τ) * (H₃ τ) * (H₄ τ))^2 / (256 : ℂ) := by
  -- The product `H₂ * H₃ * H₄` is anti-invariant under both `S` and `T` (at weight 6).
  have hslash3 (A : SL(2, ℤ)) :
      (thetaDelta_f ∣[(6 : ℤ)] A) =
        (H₂ ∣[(2 : ℤ)] A) * ((H₃ ∣[(2 : ℤ)] A) * (H₄ ∣[(2 : ℤ)] A)) := by
    have h34 :
        ((H₃ * H₄) ∣[(4 : ℤ)] A) = (H₃ ∣[(2 : ℤ)] A) * (H₄ ∣[(2 : ℤ)] A) := by
      simpa [show (4 : ℤ) = 2 + 2 by norm_num] using (mul_slash_SL2 2 2 A H₃ H₄)
    have h234 :
        ((H₂ * (H₃ * H₄)) ∣[(6 : ℤ)] A) =
          (H₂ ∣[(2 : ℤ)] A) * ((H₃ * H₄) ∣[(4 : ℤ)] A) := by
      simpa [show (6 : ℤ) = 2 + 4 by norm_num, mul_assoc] using
        (mul_slash_SL2 2 4 A H₂ (H₃ * H₄))
    simp [thetaDelta_f, h234, h34]
  have hprod_S : (thetaDelta_f ∣[(6 : ℤ)] S) = -thetaDelta_f := by
    rw [hslash3 S, H₂_S_action, H₃_S_action, H₄_S_action]
    ext z
    simp [thetaDelta_f, mul_left_comm, mul_comm]
  have hprod_T : (thetaDelta_f ∣[(6 : ℤ)] T) = -thetaDelta_f := by
    rw [hslash3 T, H₂_T_action, H₃_T_action, H₄_T_action]
    ext z
    simp [thetaDelta_f, mul_comm]
  -- Squaring removes the sign, so `thetaDeltaFun` is invariant under `S` and `T` at weight 12.
  have thetaDeltaFun_S_action : (thetaDeltaFun ∣[(12 : ℤ)] S) = thetaDeltaFun := by
    have hsq : ((thetaDelta_f ^ 2) ∣[(12 : ℤ)] S) = thetaDelta_f ^ 2 := by
      simpa [pow_two, show (12 : ℤ) = 6 + 6 by norm_num, hprod_S] using
        (mul_slash_SL2 6 6 S thetaDelta_f thetaDelta_f)
    dsimp [thetaDeltaFun]
    rw [SL_smul_slash]
    simp [hsq]
  have thetaDeltaFun_T_action : (thetaDeltaFun ∣[(12 : ℤ)] T) = thetaDeltaFun := by
    have hsq : ((thetaDelta_f ^ 2) ∣[(12 : ℤ)] T) = thetaDelta_f ^ 2 := by
      simpa [pow_two, show (12 : ℤ) = 6 + 6 by norm_num, hprod_T] using
        (mul_slash_SL2 6 6 T thetaDelta_f thetaDelta_f)
    dsimp [thetaDeltaFun]
    rw [SL_smul_slash]
    simp [hsq]
  -- Build a level-1 modular form out of `thetaDeltaFun`.
  have thetaDeltaFun_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) thetaDeltaFun := by
    have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) thetaDelta_f := by
      simpa [thetaDelta_f] using
        H₂_SIF_MDifferentiable.mul (H₃_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable)
    have hsq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaDelta_f ^ 2) := by
      simpa [pow_two] using hf.mul hf
    simpa [thetaDeltaFun] using hsq.const_smul ((256 : ℂ)⁻¹)
  have thetaDeltaFun_SL2Z_invariant :
      ∀ γ : SL(2, ℤ), thetaDeltaFun ∣[(12 : ℤ)] γ = thetaDeltaFun :=
    slashaction_generators_SL2Z thetaDeltaFun 12 thetaDeltaFun_S_action thetaDeltaFun_T_action
  -- `thetaDeltaFun` is zero at `i∞`, hence bounded there.
  have thetaDeltaFun_tendsto_atImInfty : Tendsto thetaDeltaFun atImInfty (𝓝 0) := by
    have hf0 : Tendsto thetaDelta_f atImInfty (𝓝 0) := by
      simpa [thetaDelta_f, mul_assoc] using
        H₂_tendsto_atImInfty.mul (H₃_tendsto_atImInfty.mul H₄_tendsto_atImInfty)
    have hf2 : Tendsto (fun z : ℍ => (thetaDelta_f z) ^ 2) atImInfty (𝓝 (0 : ℂ)) := by
      simpa using hf0.pow 2
    have : Tendsto (fun z : ℍ => ((256 : ℂ)⁻¹) * (thetaDelta_f z) ^ 2) atImInfty (𝓝 0) := by
      simpa [mul_zero] using (tendsto_const_nhds.mul hf2)
    simpa [thetaDeltaFun, Pi.smul_apply, smul_eq_mul] using this
  have isBoundedAtImInfty_thetaDeltaFun : IsBoundedAtImInfty thetaDeltaFun :=
    IsZeroAtImInfty.isBoundedAtImInfty thetaDeltaFun_tendsto_atImInfty
  -- Any slash by an element of `SL(2,ℤ)` is just itself
  -- (for use with `bounded_at_cusps_of_bounded_at_infty`).
  have thetaDeltaFun_slash_eq (A' : SL(2, ℤ)) :
      thetaDeltaFun ∣[(12 : ℤ)] (SpecialLinearGroup.mapGL ℝ A') = thetaDeltaFun := by
    simpa [ModularForm.SL_slash] using thetaDeltaFun_SL2Z_invariant A'
  have isBoundedAtImInfty_thetaDeltaFun_slash :
      ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (thetaDeltaFun ∣[(12 : ℤ)] (A : GL (Fin 2) ℝ)) := by
    simpa using
      (isBoundedAtImInfty_slash_of_slash_eq thetaDeltaFun_slash_eq isBoundedAtImInfty_thetaDeltaFun)
  -- Package as a `ModularForm`.
  let thetaDelta_SIF : SlashInvariantForm (Γ 1) 12 :=
    { toFun := thetaDeltaFun
      slash_action_eq' :=
        slashaction_generators_GL2R thetaDeltaFun 12 thetaDeltaFun_S_action thetaDeltaFun_T_action }
  let thetaDelta_MF : ModularForm (Γ 1) 12 := {
    thetaDelta_SIF with
    holo' := thetaDeltaFun_holo
    bdd_at_cusps' := fun hc =>
      bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_thetaDeltaFun_slash
  }
  have thetaDelta_MF_IsCuspForm : IsCuspForm (Γ 1) 12 thetaDelta_MF := by
    rw [IsCuspForm_iff_coeffZero_eq_zero, ModularFormClass.qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    -- Use the vanishing at `i∞`.
    exact IsZeroAtImInfty.cuspFunction_apply_zero thetaDeltaFun_tendsto_atImInfty
      (by norm_num : (0 : ℝ) < 1)
  -- Turn it into an element of the 1-dimensional cusp space and compare with `Delta`.
  let thetaDelta_CF : CuspForm (Γ 1) 12 :=
    IsCuspForm_to_CuspForm (Γ 1) 12 thetaDelta_MF thetaDelta_MF_IsCuspForm
  have hthetaDeltaFun_coe : (thetaDelta_CF : ℍ → ℂ) = thetaDeltaFun := by
    funext z
    have hcoe :=
      CuspForm_to_ModularForm_Fun_coe (Γ 1) 12 thetaDelta_MF thetaDelta_MF_IsCuspForm
    -- `thetaDelta_MF` is definitionally `thetaDeltaFun` as a function.
    simpa [thetaDelta_MF, thetaDeltaFun] using congrArg (fun f : ℍ → ℂ => f z) hcoe
  have hr : Module.finrank ℂ (CuspForm (Γ 1) 12) = 1 := by
    have e := CuspForms_iso_Modforms (12 : ℤ)
    apply Module.finrank_eq_of_rank_eq
    rw [LinearEquiv.rank_eq e]
    simp only [Int.reduceSub, Nat.cast_one]
    exact ModularForm.levelOne_weight_zero_rank_one
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).1 hr thetaDelta_CF
  -- Identify the scalar `c` by comparing the leading exponential decay at `i∞`.
  have hlim_thetaDeltaFun :
      Tendsto (fun z : ℍ => thetaDeltaFun z / cexp (2 * π * I * (z : ℂ))) atImInfty (𝓝 1) :=
    thetaDeltaFun_div_exp_tendsto_atImInfty
  have hlim_Delta :
      Tendsto (fun z : ℍ => Delta z / cexp (2 * π * I * (z : ℂ))) atImInfty (𝓝 1) := by
    -- `Delta z = exp(2π i z) * (boundedfactor z)` and the bounded factor tends to `1`.
    have hb : Tendsto
        (fun z : ℍ => ∏' (n : ℕ), (1 - cexp (2 * π * I * (↑n + 1) * (z : ℂ))) ^ 24)
        atImInfty (𝓝 1) := Delta_boundedfactor
    have hrew :
        (fun z : ℍ => Delta z / cexp (2 * π * I * (z : ℂ))) =
          fun z : ℍ => ∏' (n : ℕ), (1 - cexp (2 * π * I * (↑n + 1) * (z : ℂ))) ^ 24 := by
      funext z
      -- Expand `Delta` via the product formula `Δ`.
      simp [Delta_apply, Δ, div_eq_mul_inv, mul_left_comm, mul_comm]
    simpa [hrew] using hb
  -- Use the 1-dimensionality to identify `c`.
  have hlim_thetaDeltaCF :
      Tendsto (fun z : ℍ => (thetaDelta_CF z) / cexp (2 * π * I * (z : ℂ))) atImInfty (𝓝 1) := by
    simpa [hthetaDeltaFun_coe] using hlim_thetaDeltaFun
  have hlim_thetaDeltaCF' :
      Tendsto (fun z : ℍ => (thetaDelta_CF z) / cexp (2 * π * I * (z : ℂ))) atImInfty (𝓝 c) := by
    -- Rewrite `thetaDelta_CF` using `hc`.
    have hEqFun : (thetaDelta_CF : ℍ → ℂ) = fun z => (c : ℂ) * Delta z := by
      funext z
      have := congrArg (fun f : CuspForm (Γ 1) 12 => (f : ℍ → ℂ) z) hc.symm
      simpa [Pi.smul_apply, smul_eq_mul] using this
    -- Now take limits.
    have : Tendsto (fun z : ℍ => (c : ℂ) *
      (Delta z / cexp (2 * π * I * (z : ℂ)))) atImInfty (𝓝 c) :=
      by
        simpa using (tendsto_const_nhds.mul hlim_Delta)
    -- Massage the expression to match `thetaDelta_CF z / exp`.
    have hrew :
        (fun z : ℍ => (thetaDelta_CF z) / cexp (2 * π * I * (z : ℂ))) =
          fun z : ℍ => (c : ℂ) * (Delta z / cexp (2 * π * I * (z : ℂ))) := by
      funext z
      simp [hEqFun, div_eq_mul_inv, mul_left_comm, mul_comm]
    simpa [hrew] using this
  have hc_one : c = (1 : ℂ) :=
    (tendsto_nhds_unique hlim_thetaDeltaCF' hlim_thetaDeltaCF)
  -- Conclude equality of cusp forms and then evaluate at `τ`.
  have hEqCF : thetaDelta_CF = Delta := by
    -- From `hc : c • Delta = thetaDelta_CF` and `c = 1`.
    have : (1 : ℂ) • Delta = thetaDelta_CF := by simpa [hc_one] using hc
    simpa using this.symm
  -- Evaluate at `τ`.
  have hEqFun' : thetaDeltaFun τ = Delta τ := by
    -- Use coercions to functions.
    have : thetaDelta_CF τ = Delta τ := congrArg (fun f : CuspForm (Γ 1) 12 => f τ) hEqCF
    simpa [hthetaDeltaFun_coe] using this
  simpa [thetaDeltaFun, thetaDelta_f, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hEqFun'.symm

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
