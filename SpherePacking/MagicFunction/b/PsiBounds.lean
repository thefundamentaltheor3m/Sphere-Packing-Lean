module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.ModularForms.Delta
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import SpherePacking.ForMathlib.DerivHelpers

import Mathlib.Topology.Algebra.InfiniteSum.NatInt


/-!
# Bounds for the `ψ`-functions (imaginary axis)

This file provides the analytic bounds on `ψS` needed to prove the Schwartz decay of the
integrals defining Viazovska's magic function `b`.
-/

namespace MagicFunction.b.PsiBounds

open scoped Topology UpperHalfPlane Manifold

open Complex Real Filter Topology UpperHalfPlane Set

noncomputable section

/-! ## Algebraic factorization of `ψS` -/

/-- Factorization of `ψS` in terms of the Jacobi theta functions `H₂`, `H₃`, and `H₄`. -/
public lemma ψS_apply_eq_factor (z : ℍ) :
    ψS z =
      (-128 : ℂ) *
        (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2) := by
  have hJ : H₃ z = H₂ z + H₄ z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) jacobi_identity.symm
  refine (eq_div_iff (mul_ne_zero (pow_ne_zero 2 (H₃_ne_zero z))
    (pow_ne_zero 2 (H₄_ne_zero z)))).2 ?_
  rw [show ψS z = 128 * (((H₄ z - H₂ z) / (H₃ z) ^ 2) - ((H₂ z + H₃ z) / (H₄ z) ^ 2)) by
    simpa using congrArg (fun f : ℍ → ℂ => f z) ψS_eq']
  field_simp [H₃_ne_zero z, H₄_ne_zero z]
  simp [hJ]; ring_nf

end

/-! ## Continuity and bounds for `ψS` on the imaginary axis -/

/-- Continuity of the modular function `ψS`. -/
public lemma continuous_ψS : Continuous ψS := by
  have hH2 := mdifferentiable_H₂.continuous
  have hH3 := mdifferentiable_H₃.continuous
  have hH4 := mdifferentiable_H₄.continuous
  simpa [ψS_eq', mul_assoc] using continuous_const.mul
    (((hH4.sub hH2).div (hH3.pow 2) (fun z => pow_ne_zero 2 (H₃_ne_zero z))).sub
      ((hH2.add hH3).div (hH4.pow 2) (fun z => pow_ne_zero 2 (H₄_ne_zero z))))

/-- Continuity of the modular function `ψT`. -/
public lemma continuous_ψT : Continuous ψT := by
  have hH2 := mdifferentiable_H₂.continuous
  have hH3 := mdifferentiable_H₃.continuous
  have hH4 := mdifferentiable_H₄.continuous
  simpa [ψT_eq, mul_assoc] using continuous_const.mul
    (((hH3.add hH4).div (hH2.pow 2) (fun z => pow_ne_zero 2 (H₂_ne_zero z))).add
      ((hH2.add hH3).div (hH4.pow 2) (fun z => pow_ne_zero 2 (H₄_ne_zero z))))

/-- Continuity of the modular function `ψI`. -/
public lemma continuous_ψI : Continuous ψI := by
  have hH2 := mdifferentiable_H₂.continuous
  have hH3 := mdifferentiable_H₃.continuous
  have hH4 := mdifferentiable_H₄.continuous
  rw [show ψI = fun z : ℍ =>
        (128 : ℂ) * ((H₃ z + H₄ z) / (H₂ z) ^ 2) +
          (128 : ℂ) * ((H₄ z - H₂ z) / (H₃ z) ^ 2) from funext fun z => by
    simpa [nsmul_eq_mul, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using congrArg (fun f : ℍ → ℂ => f z) ψI_eq]
  simpa [mul_assoc] using (continuous_const.mul
    ((hH3.add hH4).div (hH2.pow 2) (fun z => pow_ne_zero 2 (H₂_ne_zero z)))).add
    (continuous_const.mul
      ((hH4.sub hH2).div (hH3.pow 2) (fun z => pow_ne_zero 2 (H₃_ne_zero z))))

/-- `ψS` tends to `0` at `Im z → ∞`. -/
public theorem tendsto_ψS_atImInfty : Tendsto ψS atImInfty (𝓝 (0 : ℂ)) := by
  have hH2 := H₂_tendsto_atImInfty
  have hH3 := H₃_tendsto_atImInfty
  have hH4 := H₄_tendsto_atImInfty
  have hpoly :
      Tendsto (fun z : ℍ => 2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)
        atImInfty (𝓝 (5 : ℂ)) := by
    have h1 : Tendsto (fun z : ℍ => 2 * (H₂ z) ^ 2) atImInfty (𝓝 (0 : ℂ)) := by
      simpa using tendsto_const_nhds.mul (hH2.pow 2)
    have h2 : Tendsto (fun z : ℍ => 5 * (H₂ z) * (H₄ z)) atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_assoc] using tendsto_const_nhds.mul (hH2.mul hH4)
    have h3 : Tendsto (fun z : ℍ => 5 * (H₄ z) ^ 2) atImInfty (𝓝 (5 : ℂ)) := by
      simpa using tendsto_const_nhds.mul (hH4.pow 2)
    simpa [add_assoc] using (h1.add h2).add h3
  rw [show ψS = fun z : ℍ =>
        -((128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2))) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2) from funext fun z => by simp [ψS_apply_eq_factor]]
  simpa [Pi.div_apply] using ((tendsto_const_nhds.mul (hH2.mul hpoly)).neg.div
    (by simpa using (hH3.pow 2).mul (hH4.pow 2)) (by norm_num : (1 : ℂ) ≠ 0))

/-- Uniform bound for `‖ψS.resToImagAxis t‖` on `Ici (1 : ℝ)`. -/
public lemma exists_bound_norm_ψS_resToImagAxis_Ici_one :
    ∃ M, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ M := by
  have htop : Tendsto (fun t : ℝ => ψS.resToImagAxis t) atTop (𝓝 (0 : ℂ)) := by
    simpa using Function.tendsto_resToImagAxis_atImInfty (F := ψS) (l := (0 : ℂ))
      tendsto_ψS_atImInfty
  rcases eventually_atTop.1 <|
    ((tendsto_zero_iff_norm_tendsto_zero).1 htop).eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)) with ⟨A, hA⟩
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc (a := 1) (b := max A 1)
    (hab := le_max_right _ _)
    (hg := continuous_norm.comp_continuousOn <|
      (Function.continuousOn_resToImagAxis_Ioi_of (F := ψS) continuous_ψS).mono fun _ ht =>
        lt_of_lt_of_le (by norm_num) ht.1)
  refine ⟨max C 1, fun t ht => ?_⟩
  by_cases htB : t ≤ max A 1
  · exact (hC t ⟨ht, htB⟩).trans (le_max_left _ _)
  · exact (hA t (le_trans (le_max_left _ _) (le_of_not_ge htB))).le.trans (le_max_right _ _)

end MagicFunction.b.PsiBounds

namespace SpherePacking.ForMathlib

open Filter Real

/-- Uniform bound for `x ^ k * exp (-b * x)` on `0 ≤ x` when `0 < b`. -/
public lemma exists_bound_pow_mul_exp_neg_mul (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * x) ≤ C := by
  let f : ℝ → ℝ := fun x ↦ x ^ k * Real.exp (-b * x)
  have ht : Tendsto f atTop (nhds (0 : ℝ)) := by
    simpa [f, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (k : ℝ)) (b := b) hb)
  rcases (eventually_atTop.1 <| ht.eventually (Iio_mem_nhds zero_lt_one)) with ⟨A, hA⟩
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (max A 0))).exists_isMaxOn
      (Set.nonempty_Icc.2 (le_max_right A 0)) (by fun_prop : Continuous f).continuousOn
    with ⟨x0, hx0, hxmax⟩
  refine ⟨max (f x0) 1, fun x hx => ?_⟩
  by_cases hxA : x ≤ max A 0
  · exact (hxmax ⟨hx, hxA⟩).trans (le_max_left _ _)
  · exact (le_of_lt (hA x ((le_max_left _ _).trans (le_of_not_ge hxA)))).trans (le_max_right _ _)

/-- Uniform bound for `x ^ k * exp (-b * sqrt x)` on `0 ≤ x`. -/
public lemma exists_bound_pow_mul_exp_neg_mul_sqrt (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * Real.sqrt x) ≤ C := by
  rcases exists_bound_pow_mul_exp_neg_mul (k := 2 * k) (b := b) hb with ⟨C, hC⟩
  exact ⟨C, fun x hx => by
    simpa [pow_mul, Real.sq_sqrt hx] using hC (Real.sqrt x) (Real.sqrt_nonneg _)⟩

/-- AM-GM style inequality for the exponential weight: for `0 ≤ x`, `0 < t`,
`exp (-π / t) * exp (-π * x * t) ≤ exp (-2 * π * sqrt x)`. -/
public lemma exp_neg_pi_div_mul_exp_neg_pi_mul_le (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) ≤
      Real.exp (-2 * Real.pi * Real.sqrt x) := by
  have hAMGM : 2 * Real.sqrt (x * t) * (Real.sqrt t)⁻¹ ≤ x * t + 1 / t := by
    have h := two_mul_le_add_sq (Real.sqrt (x * t)) ((Real.sqrt t)⁻¹)
    have hinv : ((Real.sqrt t)⁻¹ : ℝ) ^ 2 = (1 / t : ℝ) := by simp [one_div, Real.sq_sqrt ht.le]
    simpa [Real.sq_sqrt (mul_nonneg hx ht.le), hinv, mul_assoc, mul_left_comm, mul_comm] using h
  have hmul_sqrt : Real.sqrt (x * t) * (Real.sqrt t)⁻¹ = Real.sqrt x := by
    have hsqrt : Real.sqrt (x * t) = Real.sqrt x * Real.sqrt t := by
      simpa [mul_comm] using Real.sqrt_mul hx t
    grind
  have hIneq : 2 * Real.sqrt x ≤ x * t + 1 / t := by
    simpa [hmul_sqrt, mul_assoc] using hAMGM
  refine (Real.exp_add _ _).symm.trans_le (Real.exp_le_exp.2 ?_)
  rw [show (-Real.pi / t) + (-Real.pi * x * t) = -(Real.pi * (x * t + 1 / t)) from by ring,
    show -2 * Real.pi * Real.sqrt x = -(Real.pi * (2 * Real.sqrt x)) from by ring]
  exact neg_le_neg (mul_le_mul_of_nonneg_left hIneq Real.pi_pos.le)

end SpherePacking.ForMathlib
