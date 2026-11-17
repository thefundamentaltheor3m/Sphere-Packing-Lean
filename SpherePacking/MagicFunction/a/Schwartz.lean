/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


-- import Mathlib

public import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
public import SpherePacking.MagicFunction.a.Basic

/-!
# `a` is a Schwartz Function

The purpose of this file is to prove that `a` is a Schwartz function. It collects results stated
elsewhere and presents them concisely.
-/

@[expose] public section

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

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

theorem I₁'_smooth' : ContDiffOn ℝ ∞ RealIntegrals.I₁' (Ici (-3 / 2)) := by
  sorry

theorem I₂'_smooth' : ContDiffOn ℝ ∞ RealIntegrals.I₂' (Ici (-3 / 2)) := by
  sorry

theorem I₃'_smooth' : ContDiffOn ℝ ∞ RealIntegrals.I₃' (Ici (-3 / 2)) := by
  have hI : RealIntegrals.I₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.I₁' x := by
    ext x
    have hEqOn : EqOn (Φ₃ x) (fun t => cexp (2 * π * I * x) * Φ₁ x t) (uIcc 0 1) := fun t ht => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have h1 := z₁'_eq_of_mem ht; have h3 := z₃'_eq_of_mem ht
      simp_rw [
        Φ₃_def, Φ₃'_def, Φ₁_def, Φ₁'_def,
        show z₃' t - 1 = I * t by simp [h3],
        show z₃' t = z₁' t + 2 by simp [h1, h3]; ring,
        show z₁' t + 1 = I * t by simp [h1],
        mul_add, Complex.exp_add, mul_comm, mul_left_comm, mul_assoc]
    simpa [I₃', I₁'] using (intervalIntegral.integral_congr (a := 0) (b := 1) hEqOn).trans
      (intervalIntegral.integral_const_mul (cexp (2 * π * I * x)) (f := Φ₁ x) (a := (0 : ℝ))
        (b := 1))
  simpa [hI] using ((contDiff_const.mul ofRealCLM.contDiff).cexp.contDiffOn).mul I₁'_smooth'

theorem I₄'_smooth' : ContDiffOn ℝ ∞ RealIntegrals.I₄' (Ici (-3 / 2)) := by
  sorry

theorem I₅'_smooth' : ContDiffOn ℝ ∞ RealIntegrals.I₅' (Ici (-3 / 2)) := by
  sorry

theorem I₆'_smooth' : ContDiffOn ℝ ∞ RealIntegrals.I₆' (Ici (-3 / 2)) := by
  sorry

end Smooth

section Decay

/-! # `a` decays faster than any inverse power of the norm squared.

We follow the proof of Proposition 7.8 in the blueprint.
-/

theorem I₁'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₁' x‖ ≤ C := by
  sorry

theorem I₂'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₂' x‖ ≤ C := by
  sorry

theorem I₃'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₃' x‖ ≤ C := by
  sorry

theorem I₄'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C := by
  sorry

theorem I₅'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₅' x‖ ≤ C := by
  sorry

theorem I₆'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C := by
  sorry

end Decay

end MagicFunction.a.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.a.RadialSchwartzIntegrals

def I₁' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 0) (δ := 1) (by norm_num) (by norm_num)
  MagicFunction.a.SchwartzProperties.I₁'_smooth'
  MagicFunction.a.SchwartzProperties.I₁'_decayOn

def I₂' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 0) (δ := 1) (by norm_num) (by norm_num)
  MagicFunction.a.SchwartzProperties.I₂'_smooth'
  MagicFunction.a.SchwartzProperties.I₂'_decayOn

def I₃' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 0) (δ := 1) (by norm_num) (by norm_num)
  MagicFunction.a.SchwartzProperties.I₃'_smooth'
  MagicFunction.a.SchwartzProperties.I₃'_decayOn

def I₄' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 0) (δ := 1) (by norm_num) (by norm_num)
  MagicFunction.a.SchwartzProperties.I₄'_smooth'
  MagicFunction.a.SchwartzProperties.I₄'_decayOn

def I₅' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 0) (δ := 1) (by norm_num) (by norm_num)
  MagicFunction.a.SchwartzProperties.I₅'_smooth'
  MagicFunction.a.SchwartzProperties.I₅'_decayOn

def I₆' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 0) (δ := 1) (by norm_num) (by norm_num)
  MagicFunction.a.SchwartzProperties.I₆'_smooth'
  MagicFunction.a.SchwartzProperties.I₆'_decayOn

/- As a sanity check, the `SchwartzMap` versions agree with the other versions on [0, ∞) - in
particular, on all norms. -/

lemma I₁'_eqOn : Set.EqOn I₁' RealIntegrals.I₁' (Set.Ici 0) :=
  (ofDecayOn_eqOn (δ := 1) (by norm_num) (by norm_num)
    MagicFunction.a.SchwartzProperties.I₁'_smooth'
    MagicFunction.a.SchwartzProperties.I₁'_decayOn).symm

lemma I₂'_eqOn : Set.EqOn I₂' RealIntegrals.I₂' (Set.Ici 0) :=
  (ofDecayOn_eqOn (δ := 1) (by norm_num) (by norm_num)
    MagicFunction.a.SchwartzProperties.I₂'_smooth'
    MagicFunction.a.SchwartzProperties.I₂'_decayOn).symm

lemma I₃'_eqOn : Set.EqOn I₃' RealIntegrals.I₃' (Set.Ici 0) :=
  (ofDecayOn_eqOn (δ := 1) (by norm_num) (by norm_num)
    MagicFunction.a.SchwartzProperties.I₃'_smooth'
    MagicFunction.a.SchwartzProperties.I₃'_decayOn).symm

lemma I₄'_eqOn : Set.EqOn I₄' RealIntegrals.I₄' (Set.Ici 0) :=
  (ofDecayOn_eqOn (δ := 1) (by norm_num) (by norm_num)
    MagicFunction.a.SchwartzProperties.I₄'_smooth'
    MagicFunction.a.SchwartzProperties.I₄'_decayOn).symm

lemma I₅'_eqOn : Set.EqOn I₅' RealIntegrals.I₅' (Set.Ici 0) :=
  (ofDecayOn_eqOn (δ := 1) (by norm_num) (by norm_num)
    MagicFunction.a.SchwartzProperties.I₅'_smooth'
    MagicFunction.a.SchwartzProperties.I₅'_decayOn).symm

lemma I₆'_eqOn : Set.EqOn I₆' RealIntegrals.I₆' (Set.Ici 0) :=
  (ofDecayOn_eqOn (δ := 1) (by norm_num) (by norm_num)
    MagicFunction.a.SchwartzProperties.I₆'_smooth'
    MagicFunction.a.SchwartzProperties.I₆'_decayOn).symm

def I₁ : RadialSchwartzMap ℂ ℝ⁸ ℂ := I₁'.toRadialSchwartzMap ℂ ℝ⁸

def I₂ : RadialSchwartzMap ℂ ℝ⁸ ℂ := I₂'.toRadialSchwartzMap ℂ ℝ⁸

def I₃ : RadialSchwartzMap ℂ ℝ⁸ ℂ := I₃'.toRadialSchwartzMap ℂ ℝ⁸

def I₄ : RadialSchwartzMap ℂ ℝ⁸ ℂ := I₄'.toRadialSchwartzMap ℂ ℝ⁸

def I₅ : RadialSchwartzMap ℂ ℝ⁸ ℂ := I₅'.toRadialSchwartzMap ℂ ℝ⁸

def I₆ : RadialSchwartzMap ℂ ℝ⁸ ℂ := I₆'.toRadialSchwartzMap ℂ ℝ⁸

/- As a sanity-check, the `RadialSchwartzMap` versions exactly equal the real integrals composed
with norm squared. -/

lemma I₁_eq_comp_normSq {x : ℝ⁸} : I₁ x = RealIntegrals.I₁' (‖x‖ ^ 2) := by apply I₁'_eqOn; simp

lemma I₂_eq_comp_normSq {x : ℝ⁸} : I₂ x = RealIntegrals.I₂' (‖x‖ ^ 2) := by apply I₂'_eqOn; simp

lemma I₃_eq_comp_normSq {x : ℝ⁸} : I₃ x = RealIntegrals.I₃' (‖x‖ ^ 2) := by apply I₃'_eqOn; simp

lemma I₄_eq_comp_normSq {x : ℝ⁸} : I₄ x = RealIntegrals.I₄' (‖x‖ ^ 2) := by apply I₄'_eqOn; simp

lemma I₅_eq_comp_normSq {x : ℝ⁸} : I₅ x = RealIntegrals.I₅' (‖x‖ ^ 2) := by apply I₅'_eqOn; simp

lemma I₆_eq_comp_normSq {x : ℝ⁸} : I₆ x = RealIntegrals.I₆' (‖x‖ ^ 2) := by apply I₆'_eqOn; simp

end MagicFunction.a.RadialSchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.a.RadialSchwartzIntegrals.I₁'
  + MagicFunction.a.RadialSchwartzIntegrals.I₂'
  + MagicFunction.a.RadialSchwartzIntegrals.I₃'
  + MagicFunction.a.RadialSchwartzIntegrals.I₄'
  + MagicFunction.a.RadialSchwartzIntegrals.I₅'
  + MagicFunction.a.RadialSchwartzIntegrals.I₆'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a : RadialSchwartzMap ℂ ℝ⁸ ℂ := a'.toRadialSchwartzMap ℂ ℝ⁸

-- TODO: we may want a `Set.EqOn` result equating these with the original integrals on `[0, ∞)`.
theorem a_eq_sum_RadialSchwartzIntegrals : a =
    MagicFunction.a.RadialSchwartzIntegrals.I₁
  + MagicFunction.a.RadialSchwartzIntegrals.I₂
  + MagicFunction.a.RadialSchwartzIntegrals.I₃
  + MagicFunction.a.RadialSchwartzIntegrals.I₄
  + MagicFunction.a.RadialSchwartzIntegrals.I₅
  + MagicFunction.a.RadialSchwartzIntegrals.I₆ := rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap
