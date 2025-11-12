/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

-- import Mathlib

import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
import SpherePacking.MagicFunction.b.Basic

/-! # `b` is a Schwartz Function

The purpose of this file is to prove that `b` is a Schwartz function. It collects results stated
elsewhere and presents them concisely.
-/

-- NOTE: We are not ready for the contents of this file. We first need to fix
-- the dimension bridge for Schwartz functions.

-- #exit

open MagicFunction MagicFunction.b MagicFunction.b.RadialFunctions MagicFunction.b.RealIntegrals
  MagicFunction.Parametrisations

open Set Complex Real SchwartzMap

open scoped ContDiff

namespace MagicFunction.b.SchwartzProperties

section Smooth

/-! # `b` is smooth.

There is no reference for this in the blueprint. The idea is to use integrability to differentiate
inside the integrals. The proof path I have in mind is the following.

We need to use the Leibniz Integral Rule to differentiate under the integral sign. This is stated as
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` in `Mathlib.Analysis.Calculus.ParametricIntegral`
-/

theorem J₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₁' := by
  sorry

theorem J₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₂' :=
by
  have hJ : RealIntegrals.J₁' = fun x : ℝ => (I : ℂ) * RealIntegrals.J₂' x := by
    funext x
    simp [RealIntegrals.J₁', RealIntegrals.J₂', mul_comm, mul_left_comm, mul_assoc]
  have hJ₂ : RealIntegrals.J₂' = fun x : ℝ => (-I : ℂ) * RealIntegrals.J₁' x := by
    funext x
    have hI : (-I : ℂ) * I = 1 := by simp [I_mul_I]
    calc
      RealIntegrals.J₂' x = ((-I : ℂ) * I) * RealIntegrals.J₂' x := by simp [hI]
      _ = (-I : ℂ) * (I * RealIntegrals.J₂' x) := by
        simpa using (mul_assoc (-I : ℂ) I (RealIntegrals.J₂' x))
      _ = (-I : ℂ) * RealIntegrals.J₁' x := by simp [hJ]
  simpa [hJ₂] using
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (-I : ℂ))).mul J₁'_smooth')

theorem J₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₃' :=
by
  have hJ : RealIntegrals.J₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.J₁' x := by
    funext x
    have hEqOn : EqOn (fun t : ℝ => I * ψT' (z₁' t) * cexp (π * I * x * (z₃' t)))
        (fun t : ℝ => cexp (2 * π * I * x) * (I * ψT' (z₁' t) * cexp (π * I * x * (z₁' t))))
        (uIcc (0 : ℝ) 1) := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hz32 : z₃' t = z₁' t + (2 : ℂ) := by
        have h : z₃' t - z₁' t = (2 : ℂ) := by
          simp [z₁'_eq_of_mem ht', z₃'_eq_of_mem ht', one_add_one_eq_two]
        simpa [add_comm] using
          (sub_eq_iff_eq_add' (a := z₃' t) (b := z₁' t) (c := (2 : ℂ))).1 h
      simp [hz32, mul_add, Complex.exp_add, mul_comm, mul_left_comm, mul_assoc]
    simpa [RealIntegrals.J₃', RealIntegrals.J₁'] using
      (intervalIntegral.integral_congr (a := (0 : ℝ)) (b := (1 : ℝ)) hEqOn).trans
        (by
          simp [mul_comm, mul_left_comm, mul_assoc])
  have h_exp : ContDiff ℝ ∞ (fun x : ℝ => cexp (2 * π * I * x)) := by
    have hmul : ContDiff ℝ ∞ (fun x : ℝ => (2 * π * I : ℂ) * (x : ℂ)) :=
      contDiff_const.mul (by simpa using (ofRealCLM.contDiff : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ))))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.cexp
  simpa [hJ] using (h_exp.mul J₁'_smooth')

theorem J₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₄' := by
  sorry

theorem J₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₅' := by
  sorry

theorem J₆'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₆' := by
  sorry

end Smooth

section Decay

/-! # `b` decays faster than any inverse power of the norm squared.

We follow the proof of Proposition 7.8 in the blueprint.
-/

theorem J₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖ ≤ C := by
  sorry

theorem J₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₂' x‖ ≤ C :=
by
  intro k n
  have hJ₂ : RealIntegrals.J₂' = fun x : ℝ => (-I : ℂ) * RealIntegrals.J₁' x := by
    funext x
    have hJ : RealIntegrals.J₁' x = (I : ℂ) * RealIntegrals.J₂' x := by
      simp [RealIntegrals.J₁', RealIntegrals.J₂', mul_comm, mul_left_comm, mul_assoc]
    calc
      RealIntegrals.J₂' x = ((-I : ℂ) * I) * RealIntegrals.J₂' x := by simp
      _ = (-I : ℂ) * (I * RealIntegrals.J₂' x) := by
        simpa using (mul_assoc (-I : ℂ) I (RealIntegrals.J₂' x))
      _ = (-I : ℂ) * RealIntegrals.J₁' x := by simp [hJ]
  obtain ⟨C, hC⟩ := J₁'_decay' k n
  refine ⟨C, ?_⟩
  intro x
  rw [hJ₂]
  have hmul_eq_smul :
      (fun x => (-I : ℂ) * RealIntegrals.J₁' x)
        = (fun x => (-I : ℂ) • RealIntegrals.J₁' x) := by
    funext y; simp
  rw [hmul_eq_smul]
  have hderiv :
      iteratedFDeriv ℝ n (fun x => (-I : ℂ) • RealIntegrals.J₁' x) x
        = (-I : ℂ) • iteratedFDeriv ℝ n RealIntegrals.J₁' x := by
    apply iteratedFDeriv_const_smul_apply'
    exact (J₁'_smooth'.of_le (by norm_cast; exact le_top)).contDiffAt
  rw [hderiv, norm_smul]
  calc
    ‖x‖ ^ k * (‖(-I : ℂ)‖ * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖)
        = ‖(-I : ℂ)‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖) := by
          simp [mul_left_comm]
    _ ≤ ‖(-I : ℂ)‖ * C := by
      have hpos : 0 ≤ ‖(-I : ℂ)‖ := by simp
      exact mul_le_mul_of_nonneg_left (hC x) hpos
    _ = C := by simp

theorem J₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₃' x‖ ≤ C := by
  sorry

theorem J₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C := by
  sorry

theorem J₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖ ≤ C := by
  sorry

theorem J₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₆' x‖ ≤ C := by
  sorry

end Decay

end MagicFunction.b.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.b.SchwartzIntegrals

def J₁' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₁'
  smooth' := MagicFunction.b.SchwartzProperties.J₁'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₁'_decay'

def J₂' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₂'
  smooth' := MagicFunction.b.SchwartzProperties.J₂'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₂'_decay'

def J₃' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₃'
  smooth' := MagicFunction.b.SchwartzProperties.J₃'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₃'_decay'

def J₄' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₄'
  smooth' := MagicFunction.b.SchwartzProperties.J₄'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₄'_decay'

def J₅' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₅'
  smooth' := MagicFunction.b.SchwartzProperties.J₅'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₅'_decay'

def J₆' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₆'
  smooth' := MagicFunction.b.SchwartzProperties.J₆'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₆'_decay'

def J₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₁'

def J₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₂'

def J₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₃'

def J₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₄'

def J₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₅'

def J₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₆'

end MagicFunction.b.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b' : 𝓢(ℝ, ℂ) :=
    MagicFunction.b.SchwartzIntegrals.J₁'
  + MagicFunction.b.SchwartzIntegrals.J₂'
  + MagicFunction.b.SchwartzIntegrals.J₃'
  + MagicFunction.b.SchwartzIntegrals.J₄'
  + MagicFunction.b.SchwartzIntegrals.J₅'
  + MagicFunction.b.SchwartzIntegrals.J₆'

/-- The -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := schwartzMap_multidimensional_of_schwartzMap_real
  (EuclideanSpace ℝ (Fin 8)) b'

theorem b_eq_sum_integrals_RadialFunctions : b =
    MagicFunction.b.RadialFunctions.J₁
  + MagicFunction.b.RadialFunctions.J₂
  + MagicFunction.b.RadialFunctions.J₃
  + MagicFunction.b.RadialFunctions.J₄
  + MagicFunction.b.RadialFunctions.J₅
  + MagicFunction.b.RadialFunctions.J₆ := rfl

theorem b_eq_sum_integrals_SchwartzIntegrals : b =
    MagicFunction.b.SchwartzIntegrals.J₁
  + MagicFunction.b.SchwartzIntegrals.J₂
  + MagicFunction.b.SchwartzIntegrals.J₃
  + MagicFunction.b.SchwartzIntegrals.J₄
  + MagicFunction.b.SchwartzIntegrals.J₅
  + MagicFunction.b.SchwartzIntegrals.J₆ := rfl

theorem b'_eq_sum_RealIntegrals : b' =
    MagicFunction.b.RealIntegrals.J₁'
  + MagicFunction.b.RealIntegrals.J₂'
  + MagicFunction.b.RealIntegrals.J₃'
  + MagicFunction.b.RealIntegrals.J₄'
  + MagicFunction.b.RealIntegrals.J₅'
  + MagicFunction.b.RealIntegrals.J₆' := rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap
