/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

-- import Mathlib

import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
import SpherePacking.MagicFunction.a.Basic

/-! # `a` is a Schwartz Function

The purpose of this file is to prove that `a` is a Schwartz function. It collects results stated
elsewhere and presents them concisely.
-/

-- NOTE: We are not ready for the contents of this file. We first need to fix
-- the dimension bridge for Schwartz functions.

-- #exit

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

open Set Complex Real SchwartzMap

open scoped ContDiff

namespace MagicFunction.a.SchwartzProperties

section Smooth

/-! # `a` is smooth.

There is no reference for this in the blueprint. The idea is to use integrability to differentiate
inside the integrals. The proof path I have in mind is the following.

We need to use the Leibniz Integral Rule to differentiate under the integral sign. This is stated as
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` in `Mathlib.Analysis.Calculus.ParametricIntegral`
-/

theorem I₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₁' := by
  sorry

theorem I₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₂' := by
  sorry

private lemma I₃'_eq_cexp_mul_I₁' :
    RealIntegrals.I₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.I₁' x := by
  ext x
  have hEqOn : EqOn
      (fun t => I * φ₀'' (-1 / (z₃' t - 1)) * (z₃' t - 1) ^ 2 * cexp (π * I * x * z₃' t))
      (fun t => cexp (2 * π * I * x) * (I * φ₀'' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ 2 *
                                        cexp (π * I * x * z₁' t)))
      (uIcc 0 1) := fun t ht => by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have h1 := z₁'_eq_of_mem ht; have h3 := z₃'_eq_of_mem ht
    simp_rw [
      show z₃' t - 1 = I * t by simp [h3],
      show z₃' t = z₁' t + 2 by simp [h1, h3]; ring,
      show z₁' t + 1 = I * t by simp [h1],
      mul_add, Complex.exp_add, mul_comm, mul_left_comm, mul_assoc]
  simpa [RealIntegrals.I₃', Φ₃, Φ₃', RealIntegrals.I₁', Φ₁, Φ₁', mul_comm, mul_left_comm,
    mul_assoc] using intervalIntegral.integral_congr (a := 0) (b := 1) hEqOn

theorem I₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₃' := by
  simpa [I₃'_eq_cexp_mul_I₁'] using
    (contDiff_const.mul ofRealCLM.contDiff).cexp.mul I₁'_smooth'

theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' := by
  sorry

theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := by
  sorry

theorem I₆'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₆' := by
  sorry

end Smooth

section Decay

/-! # `a` decays faster than any inverse power of the norm squared.

We follow the proof of Proposition 7.8 in the blueprint.
-/

theorem I₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ ≤ C := by
  sorry

theorem I₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₂' x‖ ≤ C := by
  sorry

private lemma hasDerivAt_cexp_cmul_ofReal (c : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => cexp (c * (↑x : ℂ))) (c * cexp (c * (↑x : ℂ))) x := by
  have : HasDerivAt (fun x : ℝ => c * (↑x : ℂ)) c x := by
    simpa using ofRealCLM.hasDerivAt.const_mul c
  rw [show c * cexp (c * ↑x) = cexp (c * ↑x) * c from mul_comm _ _]
  exact this.cexp

private lemma iteratedDeriv_cexp_cmul_ofReal (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => cexp (c * (↑x : ℂ))) =
    fun x : ℝ => c ^ n * cexp (c * (↑x : ℂ)) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    ext x; rw [iteratedDeriv_succ]; conv_lhs => rw [ih]
    rw [(hasDerivAt_cexp_cmul_ofReal c x).const_mul (c ^ n) |>.deriv,
      pow_succ]; ring

private lemma norm_iteratedFDeriv_cexp_2piI_le (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => cexp (2 * ↑π * I * (↑x : ℂ))) x‖ ≤
    ‖(2 : ℂ) * ↑π * I‖ ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_cexp_cmul_ofReal, norm_mul, norm_pow,
      show 2 * (↑π : ℂ) * I * ↑x = ↑(2 * π * x) * I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]

theorem I₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤ C := by
  intro k n
  choose D hD using fun j => I₁'_decay' k j
  have he : ContDiff ℝ ∞ (fun x : ℝ => cexp (2 * ↑π * I * (↑x : ℂ))) :=
    (contDiff_const.mul ofRealCLM.contDiff).cexp
  refine ⟨∑ i ∈ Finset.range (n + 1),
    ↑(n.choose i) * ‖(2 : ℂ) * ↑π * I‖ ^ i * D (n - i), fun x => ?_⟩
  conv_lhs => rw [I₃'_eq_cexp_mul_I₁']
  have hmul := norm_iteratedFDeriv_mul_le he I₁'_smooth' x (n := n)
    ENat.LEInfty.out
  calc ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun x => cexp (2 * ↑π * I * ↑x) * I₁' x) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), ↑(n.choose i) *
          ‖iteratedFDeriv ℝ i (fun x => cexp (2 * ↑π * I * ↑x)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) I₁' x‖ :=
        mul_le_mul_of_nonneg_left hmul (pow_nonneg (norm_nonneg _) _)
    _ = ∑ i ∈ Finset.range (n + 1), ↑(n.choose i) *
          ‖iteratedFDeriv ℝ i (fun x => cexp (2 * ↑π * I * ↑x)) x‖ *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) I₁' x‖) := by
        rw [Finset.mul_sum]; congr 1; ext i; ring
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          ↑(n.choose i) * ‖(2 : ℂ) * ↑π * I‖ ^ i * D (n - i) := by
        apply Finset.sum_le_sum; intro i _
        have h1 := norm_iteratedFDeriv_cexp_2piI_le i x
        have h2 := hD (n - i) x
        calc ↑(n.choose i) *
              ‖iteratedFDeriv ℝ i (fun x => cexp (2 * ↑π * I * ↑x)) x‖ *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) I₁' x‖)
            ≤ ↑(n.choose i) * ‖(2 : ℂ) * ↑π * I‖ ^ i *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) I₁' x‖) := by
              gcongr
          _ ≤ ↑(n.choose i) * ‖(2 : ℂ) * ↑π * I‖ ^ i * D (n - i) := by
              gcongr

theorem I₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C := by
  sorry

theorem I₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₅' x‖ ≤ C := by
  sorry

theorem I₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C := by
  sorry

end Decay

end MagicFunction.a.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.a.SchwartzIntegrals

def I₁' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.a.RealIntegrals.I₁'
  smooth' := MagicFunction.a.SchwartzProperties.I₁'_smooth'
  decay' := MagicFunction.a.SchwartzProperties.I₁'_decay'

def I₂' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.a.RealIntegrals.I₂'
  smooth' := MagicFunction.a.SchwartzProperties.I₂'_smooth'
  decay' := MagicFunction.a.SchwartzProperties.I₂'_decay'

def I₃' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.a.RealIntegrals.I₃'
  smooth' := MagicFunction.a.SchwartzProperties.I₃'_smooth'
  decay' := MagicFunction.a.SchwartzProperties.I₃'_decay'

def I₄' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.a.RealIntegrals.I₄'
  smooth' := MagicFunction.a.SchwartzProperties.I₄'_smooth'
  decay' := MagicFunction.a.SchwartzProperties.I₄'_decay'

def I₅' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.a.RealIntegrals.I₅'
  smooth' := MagicFunction.a.SchwartzProperties.I₅'_smooth'
  decay' := MagicFunction.a.SchwartzProperties.I₅'_decay'

def I₆' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.a.RealIntegrals.I₆'
  smooth' := MagicFunction.a.SchwartzProperties.I₆'_smooth'
  decay' := MagicFunction.a.SchwartzProperties.I₆'_decay'

def I₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₁'

def I₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₂'

def I₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₃'

def I₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₄'

def I₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₅'

def I₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₆'

end MagicFunction.a.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.a.SchwartzIntegrals.I₁'
  + MagicFunction.a.SchwartzIntegrals.I₂'
  + MagicFunction.a.SchwartzIntegrals.I₃'
  + MagicFunction.a.SchwartzIntegrals.I₄'
  + MagicFunction.a.SchwartzIntegrals.I₅'
  + MagicFunction.a.SchwartzIntegrals.I₆'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := schwartzMap_multidimensional_of_schwartzMap_real
  (EuclideanSpace ℝ (Fin 8)) a'

theorem a_eq_sum_integrals_RadialFunctions : a =
    MagicFunction.a.RadialFunctions.I₁
  + MagicFunction.a.RadialFunctions.I₂
  + MagicFunction.a.RadialFunctions.I₃
  + MagicFunction.a.RadialFunctions.I₄
  + MagicFunction.a.RadialFunctions.I₅
  + MagicFunction.a.RadialFunctions.I₆ := rfl

theorem a_eq_sum_integrals_SchwartzIntegrals : a =
    MagicFunction.a.SchwartzIntegrals.I₁
  + MagicFunction.a.SchwartzIntegrals.I₂
  + MagicFunction.a.SchwartzIntegrals.I₃
  + MagicFunction.a.SchwartzIntegrals.I₄
  + MagicFunction.a.SchwartzIntegrals.I₅
  + MagicFunction.a.SchwartzIntegrals.I₆ := rfl

theorem a'_eq_sum_RealIntegrals : a' =
    MagicFunction.a.RealIntegrals.I₁'
  + MagicFunction.a.RealIntegrals.I₂'
  + MagicFunction.a.RealIntegrals.I₃'
  + MagicFunction.a.RealIntegrals.I₄'
  + MagicFunction.a.RealIntegrals.I₅'
  + MagicFunction.a.RealIntegrals.I₆' := rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap
