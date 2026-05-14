module
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.ResToImagAxis
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import SpherePacking.ForMathlib.DerivHelpers

import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Topology.Order.Compact


/-!
# Bounds for the `ψ`-functions (imaginary axis)

This file provides the analytic bounds on `ψS` needed to prove the Schwartz decay of the
integrals defining Viazovska's magic function `b`.

Also derives `‖H₂(it)‖ ≤ C * exp(-π t)` for `t ≥ 1`, then combines that exponential bound with
the algebraic factorization of `ψS` to obtain `‖ψS(it)‖ ≤ C * exp(-π t)` for `t ≥ 1`
(originally in `Schwartz.PsiExpBounds.PsiSDecay`).
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

namespace MagicFunction

open scoped Interval

open Complex Real Set
open MagicFunction.Parametrisations UpperHalfPlane

/-- A generic continuity lemma for a modular rewrite on `Ioc 0 1`. -/
public lemma continuousOn_ψT'_Ioc_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ) (z : ℝ → ℂ)
    (hψS : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ContinuousOn (fun t : ℝ => ψT' (z t)) (Ioc (0 : ℝ) 1) := by
  have hpow : Continuous fun t : ℝ => ((Complex.I : ℂ) * (t : ℂ)) ^ k := by
    simpa using (continuous_const.mul Complex.continuous_ofReal).pow k
  have hcont_one_div : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Ioc (0 : ℝ) 1) := by
    simpa [one_div] using
      (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono
        (fun t ht => by simp [ne_of_gt ht.1])
  exact ((hψS.comp hcont_one_div (fun t ht => one_le_one_div ht.1 ht.2)).mul
    hpow.continuousOn).congr hEq

/-- Continuity of the modular rewrite along `t ↦ z₁' t` on `(0, 1)`. -/
public lemma continuousOn_ψT'_z₁'_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ)
    (hψS : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ContinuousOn (fun t : ℝ => ψT' (z₁' t)) (Ioo (0 : ℝ) 1) :=
  (continuousOn_ψT'_Ioc_of (k := k) (ψS := ψS) (ψT' := ψT') (z := z₁') hψS hEq).mono
    fun _ ht => ⟨ht.1, le_of_lt ht.2⟩

/-- A uniform bound for `‖ψT' (z₁' t)‖` on `(0, 1)`, given a bound for `ψS` on `Ici 1`. -/
public lemma exists_bound_norm_ψT'_z₁'_of (k : ℕ) (ψS : ℍ → ℂ) (ψT' : ℂ → ℂ)
    (hBound : ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ M)
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k) :
    ∃ M : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖ψT' (z₁' t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hBound
  refine ⟨M, fun t ht => ?_⟩
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M := hM (1 / t) (one_le_one_div ht.1 ht.2.le)
  have htK : t ^ k ≤ (1 : ℝ) := by simpa using pow_le_one₀ (n := k) ht.1.le ht.2.le
  have hnorm : ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ = t ^ k := by
    simp [norm_pow, Complex.norm_real, abs_of_nonneg ht.1.le]
  calc
    ‖ψT' (z₁' t)‖ = ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ := by
      simp [hEq t ⟨ht.1, ht.2.le⟩]
    _ = ‖ψS.resToImagAxis (1 / t)‖ * t ^ k := by simp [hnorm]
    _ ≤ M * t ^ k := mul_le_mul_of_nonneg_right hψS (pow_nonneg ht.1.le k)
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left htK ((norm_nonneg _).trans hψS)
    _ = M := mul_one M

/-- Pointwise bound for a modular rewrite on `Ioc 0 1`. -/
public lemma norm_modular_rewrite_Ioc_bound (k : ℕ) (ψS : ℍ → ℂ) (ψZ : ℂ → ℂ) (z : ℝ → ℂ)
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψZ (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {B : ℝ} (hB : ‖ψS.resToImagAxis (1 / t)‖ ≤ B) :
    ‖ψZ (z t)‖ ≤ B * t ^ k := by
  have hnorm : ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ = t ^ k := by
    simp [norm_pow, Complex.norm_real, abs_of_nonneg ht.1.le]
  calc
    ‖ψZ (z t)‖ = ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ k‖ := by
      simp [hEq t ht]
    _ = ‖ψS.resToImagAxis (1 / t)‖ * t ^ k := by simp [hnorm]
    _ ≤ B * t ^ k := mul_le_mul_of_nonneg_right hB (pow_nonneg ht.1.le k)

/-- Pointwise bound for a modular rewrite on `Ioc 0 1` with exponential decay. -/
public lemma norm_modular_rewrite_Ioc_exp_bound (k : ℕ) (Cψ : ℝ) (ψS : ℍ → ℂ) (ψZ : ℂ → ℂ)
    (z : ℝ → ℂ)
    (hCψ : ∀ y : ℝ, 1 ≤ y → ‖ψS.resToImagAxis y‖ ≤ Cψ * Real.exp (-Real.pi * y))
    (hEq : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ψZ (z t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ k)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖ψZ (z t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ k :=
  norm_modular_rewrite_Ioc_bound k ψS ψZ z hEq ht (hCψ (1 / t) (one_le_one_div ht.1 ht.2))

end MagicFunction

namespace MagicFunction.b.PsiBounds.PsiExpBounds

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Filter Topology UpperHalfPlane Set HurwitzKernelBounds

lemma norm_Θ₂_resToImagAxis_le (t : ℝ) (ht : 0 < t) :
    ‖Θ₂.resToImagAxis t‖ ≤
      (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) := by
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hτ : (τ : ℂ) = (Complex.I : ℂ) * t := rfl
  have hΘ (n : ℤ) : ‖Θ₂_term n τ‖ = f_int 0 (1 / 2 : ℝ) t n := by
    have hnorm_pref : ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ = rexp (-π * (t / 4)) := by
      simp [Complex.norm_exp, hτ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hnorm_core :
        ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
          rexp (-(π * (n : ℝ) ^ 2 * t) - 2 * π * (n : ℝ) * (t / 2)) := by
      rw [show ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
        rexp (-π * (n : ℝ) ^ 2 * t - 2 * π * (n : ℝ) * (t / 2)) by
          simpa [hτ] using norm_jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)]
      ring_nf
    simp [HurwitzKernelBounds.f_int, pow_zero, one_mul,
      show ‖Θ₂_term n τ‖ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) from
        calc ‖Θ₂_term n τ‖ =
                ‖cexp (π * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ *
                  ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ := by
                  simp [Θ₂_term_as_jacobiTheta₂_term, hτ, mul_assoc]
          _ = rexp (-π * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
                  rw [hnorm_pref, hnorm_core, ← Real.exp_add]; congr 1; ring]
  have hsumm : Summable (fun n : ℤ => ‖Θ₂_term n τ‖) :=
    (summable_f_int 0 (1 / 2 : ℝ) ht).congr (fun n => by simpa using (hΘ n).symm)
  have hbd_nat' :
      F_nat 0 (1 / 2 : ℝ) t ≤ rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) := by
    have hnonneg' : 0 ≤ F_nat 0 (2⁻¹ : ℝ) t :=
      tsum_nonneg (fun n : ℕ => by simp only [HurwitzKernelBounds.f_nat, pow_zero]; positivity)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg'] using
      (F_nat_zero_le (a := (1 / 2 : ℝ)) (ha := by norm_num) ht)
  calc ‖Θ₂.resToImagAxis t‖
      ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖ := by
        simpa [ResToImagAxis, Θ₂, τ, ht] using (norm_tsum_le_tsum_norm hsumm)
    _ = F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t := by
        simpa [HurwitzKernelBounds.F_int] using tsum_congr fun n => by simpa using hΘ n
    _ = F_nat 0 (1 / 2 : ℝ) t + F_nat 0 (1 / 2 : ℝ) t := by
        simpa [show (1 : ℝ) - (2⁻¹ : ℝ) = (2⁻¹ : ℝ) by norm_num] using
          F_int_eq_of_mem_Icc 0 (a := (1 / 2 : ℝ)) ⟨by norm_num, by norm_num⟩ ht
    _ ≤ _ := by rw [show (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) =
                    rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) +
                    rexp (-π * ((1 / 2 : ℝ) ^ 2) * t) / (1 - rexp (-π * t)) from by ring]; gcongr

/-- Exponential decay bound for `H₂` on the positive imaginary axis. -/
public lemma exists_bound_norm_H₂_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  let Cθ : ℝ := (2 : ℝ) / (1 - rexp (-π))
  refine ⟨Cθ ^ 4, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hΘ2 : ‖Θ₂.resToImagAxis t‖ ≤ Cθ * rexp (-π * (t / 4)) := by
    have hden_pos : 0 < (1 - rexp (-π : ℝ)) :=
      sub_pos.2 (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
    calc
      ‖Θ₂.resToImagAxis t‖ ≤
          (2 * rexp (-π * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - rexp (-π * t)) :=
            norm_Θ₂_resToImagAxis_le t ht0
      _ = (2 * rexp (-π * (t / 4))) / (1 - rexp (-π * t)) := by
            rw [show -π * ((1 / 2 : ℝ) ^ 2) * t = -π * (t / 4) by ring]
      _ ≤ (2 * rexp (-π * (t / 4))) / (1 - rexp (-π : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos
              (sub_le_sub_left (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht])) 1)
      _ = Cθ * rexp (-π * (t / 4)) := by
            simp [Cθ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := by
      simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow]
    _ ≤ (Cθ * rexp (-π * (t / 4))) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hΘ2 4
    _ = (Cθ ^ 4) * rexp (-π * t) := by
      rw [mul_pow, ← Real.exp_nat_mul, show (4 : ℕ) * (-π * (t / 4)) = -π * t by push_cast; ring]

/-- Exponential decay bound for `ψS.resToImagAxis` on `Ici (1 : ℝ)`. -/
public theorem exists_bound_norm_ψS_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * rexp (-π * t) := by
  obtain ⟨CH2, hH2⟩ := exists_bound_norm_H₂_resToImagAxis_exp_Ici_one
  let CH2' : ℝ := max CH2 0
  have hCH2' : 0 ≤ CH2' := le_max_right _ _
  have hH2' : ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ CH2' * rexp (-π * t) := fun t ht =>
    le_mul_of_le_mul_of_nonneg_right (hH2 t ht) (le_max_left _ _) (by positivity)
  -- `H₃` and `H₄` converge to `1` along the imaginary axis, so their norms are bounded above
  -- and below away from `0` on `t ≥ 1` by compactness on an initial segment.
  have hEv (H : ℍ → ℂ) (hH : Tendsto (fun z : ℍ => H z) atImInfty (𝓝 (1 : ℂ))) :
      ∀ᶠ t in atTop, ‖H.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) :=
    (tendsto_sub_nhds_zero_iff.mpr (by simpa using
        (Function.tendsto_resToImagAxis_atImInfty (F := H) (l := (1 : ℂ)) hH))).norm.eventually
      (Iic_mem_nhds (by norm_num))
  obtain ⟨T0, hT0⟩ :=
    eventually_atTop.1 ((hEv H₃ H₃_tendsto_atImInfty).and (hEv H₄ H₄_tendsto_atImInfty))
  let T : ℝ := max T0 1
  have hH_ne (H : ℍ → ℂ) (hne : ∀ z : ℍ, H z ≠ 0) :
      ∀ t : ℝ, 1 ≤ t → H.resToImagAxis t ≠ (0 : ℂ) := fun t ht ↦ by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using hne ⟨Complex.I * t, by simp [ht0]⟩
  let φ : Icc 1 T → ℍ := fun t ↦ ⟨(Complex.I : ℂ) * (t : ℝ), by
    have : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1; simp [this]⟩
  have hcont_norm_resToImagAxis (H : ℍ → ℂ) (hH : Continuous H) :
      ContinuousOn (fun t : ℝ => ‖ResToImagAxis H t‖) (Icc 1 T) :=
    (continuousOn_iff_continuous_restrict).2 <| by
      simpa [show ((Icc 1 T).restrict fun t : ℝ ↦ ‖ResToImagAxis H t‖) =
        fun t : Icc 1 T ↦ ‖H (φ t)‖ from funext fun t ↦ by
          have ht0 : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.2.1
          simp [Set.restrict, ResToImagAxis, ht0, φ]] using
        (hH.comp (by fun_prop : Continuous φ)).norm
  have hcontH4 : ContinuousOn (fun t : ℝ => ‖ResToImagAxis H₄ t‖) (Icc 1 T) :=
    hcont_norm_resToImagAxis H₄ mdifferentiable_H₄.continuous
  obtain ⟨m3, hm3, hm3le⟩ := SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc
    (g := fun t ↦ ‖H₃.resToImagAxis t‖)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using
      hcont_norm_resToImagAxis H₃ mdifferentiable_H₃.continuous)
    (hpos := fun t ht => norm_pos_iff.2 (hH_ne H₃ H₃_ne_zero t ht.1))
  obtain ⟨m4, hm4, hm4le⟩ := SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc
    (g := fun t ↦ ‖H₄.resToImagAxis t‖)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
    (hpos := fun t ht => norm_pos_iff.2 (hH_ne H₄ H₄_ne_zero t ht.1))
  obtain ⟨M4Icc, hM4Icc⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc
    (g := fun t : ℝ => ‖H₄.resToImagAxis t‖) (hab := le_max_right _ _)
    (hg := by simpa [Function.resToImagAxis_eq_resToImagAxis] using hcontH4)
  let M4 : ℝ := max M4Icc 2
  have half_le_norm {x : ℂ} (h : ‖x - (1 : ℂ)‖ ≤ (1 / 2 : ℝ)) : (1 / 2 : ℝ) ≤ ‖x‖ := by
    have := (sub_le_iff_le_add).2 (norm_le_norm_add_norm_sub' (1 : ℂ) x)
    simp [norm_sub_rev] at this; linarith
  have hH3_lower : ∀ t : ℝ, 1 ≤ t → min m3 (1 / 2 : ℝ) ≤ ‖H₃.resToImagAxis t‖ := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact inf_le_of_left_le (hm3le t ⟨ht, htT⟩)
    · exact inf_le_of_right_le
        (half_le_norm (hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).1)
  have hH4_lower : ∀ t : ℝ, 1 ≤ t → min m4 (1 / 2 : ℝ) ≤ ‖H₄.resToImagAxis t‖ := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact inf_le_of_left_le (hm4le t ⟨ht, htT⟩)
    · exact inf_le_of_right_le
        (half_le_norm (hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).2)
  have hH4_upper : ∀ t : ℝ, 1 ≤ t → ‖H₄.resToImagAxis t‖ ≤ M4 := fun t ht ↦ by
    by_cases htT : t ≤ T
    · exact (hM4Icc t ⟨ht, htT⟩).trans (le_max_left _ _)
    · have hx : ‖H₄.resToImagAxis t‖ ≤ ‖H₄.resToImagAxis t - (1 : ℂ)‖ + 1 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_one] using
          norm_add_le (H₄.resToImagAxis t - (1 : ℂ)) (1 : ℂ)
      have h32 : ‖H₄.resToImagAxis t‖ ≤ (3 / 2 : ℝ) := by
        linarith [(hT0 t ((le_max_left _ _).trans (le_of_not_ge htT))).2]
      exact h32.trans ((by norm_num : (3 / 2 : ℝ) ≤ 2).trans (le_max_right _ _))
  -- Bound the polynomial factor in `ψS_apply_eq_factor`.
  let P : ℝ := 2 * (CH2' ^ 2) + 5 * CH2' * M4 + 5 * (M4 ^ 2)
  let c3 : ℝ := min m3 (1 / 2 : ℝ)
  let c4 : ℝ := min m4 (1 / 2 : ℝ)
  have hc3 : 0 < c3 := lt_min hm3 (by norm_num)
  have hc4 : 0 < c4 := lt_min hm4 (by norm_num)
  refine ⟨(128 : ℝ) * P * ((c3 ^ 2 * c4 ^ 2)⁻¹) * CH2', ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hH2t : ‖H₂.resToImagAxis t‖ ≤ CH2' * rexp (-π * t) := hH2' t ht
  have hH2le : ‖H₂.resToImagAxis t‖ ≤ CH2' := hH2t.trans <| by
    simpa using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, ht0.le])) hCH2'
  have hH4le : ‖H₄.resToImagAxis t‖ ≤ M4 := hH4_upper t ht
  have hpoly :
      ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2
          + (5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)
          + (5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ P := by
    have h1 : ‖(2 : ℂ) * (H₂.resToImagAxis t) ^ 2‖ ≤ 2 * (CH2' ^ 2) := by
      simpa [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH2le 2) (norm_nonneg (2 : ℂ))
    have h2 : ‖(5 : ℂ) * (H₂.resToImagAxis t) * (H₄.resToImagAxis t)‖ ≤ 5 * CH2' * M4 := by
      simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
        (by gcongr : ‖H₂.resToImagAxis t‖ * ‖H₄.resToImagAxis t‖ ≤ CH2' * M4) (norm_nonneg (5 : ℂ))
    have h3 : ‖(5 : ℂ) * (H₄.resToImagAxis t) ^ 2‖ ≤ 5 * (M4 ^ 2) := by
      simpa [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hH4le 2) (norm_nonneg (5 : ℂ))
    exact norm_add_le_of_le ((norm_add_le _ _).trans (by linarith [h1, h2])) h3
  -- Now bound `ψS.resToImagAxis t` using `ψS_apply_eq_factor`.
  let z : ℍ := ⟨Complex.I * t, by simp [ht0]⟩
  have hψS : ‖ψS.resToImagAxis t‖ = ‖(-128 : ℂ) *
      (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
        ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := by
    change ‖ResToImagAxis ψS t‖ = _
    rw [show ResToImagAxis ψS t = ψS z by simp [ResToImagAxis, ht0, z],
      show ψS z = (-128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
            ((H₃ z) ^ 2 * (H₄ z) ^ 2) by simpa using ψS_apply_eq_factor z]
  have hHz2 : ResToImagAxis H₂ t = H₂ z := by simp [ResToImagAxis, ht0, z]
  have hHz3 : ResToImagAxis H₃ t = H₃ z := by simp [ResToImagAxis, ht0, z]
  have hHz4 : ResToImagAxis H₄ t = H₄ z := by simp [ResToImagAxis, ht0, z]
  have hden_lower : c3 ≤ ‖H₃ z‖ := by
    simpa [hHz3] using (show c3 ≤ ‖ResToImagAxis H₃ t‖ from hH3_lower t ht)
  have hden_lower4 : c4 ≤ ‖H₄ z‖ := by
    simpa [hHz4] using (show c4 ≤ ‖ResToImagAxis H₄ t‖ from hH4_lower t ht)
  have hinv : ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤ (c3 ^ 2 * c4 ^ 2)⁻¹ := by
    have hpos : 0 < ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ :=
      norm_pos_iff.2 (mul_ne_zero (pow_ne_zero 2 (H₃_ne_zero z)) (pow_ne_zero 2 (H₄_ne_zero z)))
    have hden : c3 ^ 2 * c4 ^ 2 ≤ ‖(H₃ z) ^ 2 * (H₄ z) ^ 2‖ := by
      simpa [norm_mul, norm_pow] using mul_le_mul (pow_le_pow_left₀ hc3.le hden_lower 2)
        (pow_le_pow_left₀ hc4.le hden_lower4 2) (by positivity) (by positivity)
    simpa [norm_inv] using (inv_le_inv₀ hpos (by positivity)).2 hden
  have hH2z : ‖H₂ z‖ ≤ CH2' * rexp (-π * t) := by
    simpa [hHz2, Function.resToImagAxis] using hH2t
  have hpoly' :
      ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖ ≤ P := by
    simpa [hHz2, hHz4, Function.resToImagAxis] using hpoly
  have hP0 : (0 : ℝ) ≤ P := (norm_nonneg _).trans hpoly'
  calc
    ‖ψS.resToImagAxis t‖ = ‖(-128 : ℂ) *
        (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) /
          ((H₃ z) ^ 2 * (H₄ z) ^ 2)‖ := hψS
    _ = ‖(-128 : ℂ) *
            (H₂ z * (2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2)) *
              ((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
          ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ (128 : ℝ) * (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have h2 : (‖H₂ z‖ * ‖2 * (H₂ z) ^ 2 + 5 * (H₂ z) * (H₄ z) + 5 * (H₄ z) ^ 2‖) *
                ‖((H₃ z) ^ 2 * (H₄ z) ^ 2)⁻¹‖ ≤ (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpoly' (norm_nonneg _)) hinv (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hP0)
          grind only
    _ ≤ (128 : ℝ) * ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ := by
          have h2 : (‖H₂ z‖ * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ ≤
              ((CH2' * rexp (-π * t)) * P) * (c3 ^ 2 * c4 ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH2z hP0) (by positivity)
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 128)
    _ = ((128 : ℝ) * P * (c3 ^ 2 * c4 ^ 2)⁻¹ * CH2') * rexp (-π * t) := by ring

end

end MagicFunction.b.PsiBounds.PsiExpBounds
