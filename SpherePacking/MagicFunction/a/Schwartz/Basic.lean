/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module

public import SpherePacking.ForMathlib.DerivHelpers
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.ModularForms.FG.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import SpherePacking.Integration.Measure
public import SpherePacking.ModularForms.Eisenstein
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.Lv1Lv2Identities
import SpherePacking.ModularForms.PhiTransformLemmas
import SpherePacking.ModularForms.QExpansion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay

/-! Schwartz property for the magic function `a` via smooth cutoff of radial profiles.

Also includes the integral representation `MagicFunction.a.{ComplexIntegrands,RealIntegrands,
RealIntegrals,RadialFunctions}` (originally in `MagicFunction.a.Basic`):
Complex integrands and real reparametrizations for the scalar integrals `I₁'`, ..., `I₆'` and
their radial versions on `V = EuclideanSpace ℝ (Fin 8)`.

Also includes the `I₃` integrand bounds and the Schwartz decay estimate for `RealIntegrals.I₁'`
(inverse-power decay via the change-of-variables representation
`IntegralEstimates.I₁.Complete_Change_of_Variables`), originally in `Schwartz.DecayI1`.

Also packages bounds and Schwartz decay for `I₂'` and `I₄'`, the `I24Common` skeleton, and
auxiliary integral bounds (originally in `IntegralEstimates.I2`). -/

/-! ## Integral representation of the magic function `a` (originally in `a.Basic`) -/

local notation "V" => EuclideanSpace ℝ (Fin 8)

section a_Basic_section

open scoped UpperHalfPlane
open Set Complex Real MagicFunction.Parametrisations

noncomputable section

variable (r : ℝ)

namespace MagicFunction.a.ComplexIntegrands

/-- The complex integrands `Φ₁'`-`Φ₆'` for `a` (`Φ₂' := Φ₁'`, `Φ₄' := Φ₃'` for uniform indexing). -/
@[expose] public def Φ₁' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))
@[expose] public def Φ₂' : ℂ → ℂ := Φ₁' r
@[expose] public def Φ₃' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))
@[expose] public def Φ₄' : ℂ → ℂ := Φ₃' r
@[expose] public def Φ₅' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ))
@[expose] public def Φ₆' : ℂ → ℂ := fun z ↦ φ₀'' z * cexp (π * I * r * (z : ℂ))

end MagicFunction.a.ComplexIntegrands

namespace MagicFunction.a.RealIntegrands

open MagicFunction.a.ComplexIntegrands

/-- Real-variable integrand from `Φᵢ'` via `zᵢ'`. -/
@[expose] public def Φ₁ : ℝ → ℂ := fun t ↦ I * Φ₁' r (z₁' t)
@[expose] public def Φ₂ : ℝ → ℂ := fun t ↦ Φ₂' r (z₂' t)
@[expose] public def Φ₃ : ℝ → ℂ := fun t ↦ I * Φ₃' r (z₃' t)
@[expose] public def Φ₄ : ℝ → ℂ := fun t ↦ -1 * Φ₄' r (z₄' t)
@[expose] public def Φ₅ : ℝ → ℂ := fun t ↦ I * Φ₅' r (z₅' t)
@[expose] public def Φ₆ : ℝ → ℂ := fun t ↦ I * Φ₆' r (z₆' t)

@[simp] public lemma Φ₁_def : Φ₁ r = fun t ↦ I * Φ₁' r (z₁' t) := rfl
@[simp] public lemma Φ₂_def : Φ₂ r = fun t ↦ Φ₂' r (z₂' t) := rfl
@[simp] public lemma Φ₃_def : Φ₃ r = fun t ↦ I * Φ₃' r (z₃' t) := rfl
@[simp] public lemma Φ₄_def : Φ₄ r = fun t ↦ -1 * Φ₄' r (z₄' t) := rfl
@[simp] public lemma Φ₆_def : Φ₆ r = fun t ↦ I * Φ₆' r (z₆' t) := rfl

end MagicFunction.a.RealIntegrands

namespace MagicFunction.a.RealIntegrals

open MagicFunction.a.RealIntegrands

/-- Scalar integrals `Iᵢ'` for `a'`. -/
@[expose] public def I₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₁ x t
@[expose] public def I₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₂ x t
@[expose] public def I₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₃ x t
@[expose] public def I₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₄ x t
@[expose] public def I₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Φ₅ x t
@[expose] public def I₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Φ₆ x t

/-- Scalar `a'` as the sum of `I₁'`, ..., `I₆'`. -/
@[expose] public def a' : ℝ → ℂ := fun x ↦ I₁' x + I₂' x + I₃' x + I₄' x + I₅' x + I₆' x

end MagicFunction.a.RealIntegrals

open MagicFunction.a.RealIntegrals

namespace MagicFunction.a.RadialFunctions

/-- Radial functions on `V` from `Iᵢ'` via `r = ‖x‖^2`. -/
@[expose] public def I₁ : V → ℂ := fun x ↦ I₁' (‖x‖ ^ 2)
@[expose] public def I₂ : V → ℂ := fun x ↦ I₂' (‖x‖ ^ 2)
@[expose] public def I₃ : V → ℂ := fun x ↦ I₃' (‖x‖ ^ 2)
@[expose] public def I₄ : V → ℂ := fun x ↦ I₄' (‖x‖ ^ 2)
@[expose] public def I₅ : V → ℂ := fun x ↦ I₅' (‖x‖ ^ 2)
@[expose] public def I₆ : V → ℂ := fun x ↦ I₆' (‖x‖ ^ 2)

/-- Magic function `a` as a radial function on `V`. -/
@[expose] public def a : V → ℂ := fun x ↦ a' (‖x‖ ^ 2)

open intervalIntegral

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

@[simp] public lemma I₁_eq (x : V) : I₁ x = I₁' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₂_eq (x : V) : I₂ x = I₂' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₃_eq (x : V) : I₃ x = I₃' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₄_eq (x : V) : I₄ x = I₄' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₅_eq (x : V) : I₅ x = I₅' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₆_eq (x : V) : I₆ x = I₆' (‖x‖ ^ 2) := rfl

/-- Explicit integral expression for `I₁'`. -/
public lemma I₁'_eq (r : ℝ) : I₁' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * I * r) * cexp (-π * r * t) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₁, Φ₁', z₁'_eq_of_mem ht, show ((-1 : ℂ) + I * t + 1) = I * t by ring, mul_pow, I_sq,
    show ((π : ℂ) * I * r * (-1 + I * t)) = -π * I * r + -π * r * t by
      linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- `I₁'` as an integral over `Ioc 0 1`. -/
public lemma I₁'_eq_Ioc (r : ℝ) : I₁' r = ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * I * r) * cexp (-π * r * t) := by
  simp [I₁'_eq, intervalIntegral_eq_integral_uIoc]

/-- Explicit integral expression for `I₂'`. -/
public lemma I₂'_eq (r : ℝ) : I₂' r = ∫ t in (0 : ℝ)..1, φ₀'' (-1 / (t + I))
    * (t + I) ^ 2 * cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₂, Φ₂', Φ₁', z₂'_eq_of_mem ht, show (-1 + (t : ℂ) + I + 1) = t + I from by ring,
    show ((π : ℂ) * I * r * (-1 + t + I)) = -π * I * r + π * I * r * t + -π * r by
      linear_combination ↑π * r * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- Explicit integral expression for `I₃'`. -/
public lemma I₃'_eq (r : ℝ) : I₃' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (π * I * r) * cexp (-π * r * t) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₃, Φ₃', z₃'_eq_of_mem ht, show (1 + I * (t : ℂ) - 1) = I * t from by ring, mul_pow,
    I_sq, show ((π : ℂ) * I * r * (1 + I * t)) = π * I * r + -π * r * t by
      linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- Explicit integral expression for `I₄'`. -/
public lemma I₄'_eq (r : ℝ) : I₄' r = ∫ t in (0 : ℝ)..1, -1 * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2 * cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₄, Φ₄', Φ₃', z₄'_eq_of_mem ht, show ((1 : ℂ) - t + I - 1) = -t + I from by ring,
    show ((π : ℂ) * I * r * (1 - t + I)) = π * I * r + -π * I * r * t + -π * r by
      linear_combination ↑π * r * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- Explicit integral expression for `I₅'`. -/
public lemma I₅'_eq (r : ℝ) : I₅' r = -2 * ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * r * t) := by
  simp only [I₅', Φ₅, Φ₅']; congr 1
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  rw [z₅'_eq_of_mem ht, mul_pow, I_sq, show ((π : ℂ) * I * r * (I * t)) = -π * r * t by
    linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1)]; ring

/-- `I₅'` as an integral over `Ioc 0 1`. -/
public lemma I₅'_eq_Ioc (r : ℝ) : I₅' r = -2 * ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * r * t) := by
  simp [I₅'_eq, intervalIntegral_eq_integral_uIoc]

/-- Explicit integral expression for `I₆'`. -/
public lemma I₆'_eq (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), I
    * φ₀'' (I * t) * cexp (-π * r * t) := by
  simp only [I₆', Φ₆, Φ₆']; congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
  rw [z₆'_eq_of_mem ht, show ((π : ℂ) * I * r * (I * t)) = -π * r * t by
      linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1)]; ring

end MagicFunction.a.RadialFunctions

end

/-! ## Complex integrands Φ₁'–Φ₆' are holomorphic on the upper half-plane. -/

open scoped Function Manifold
open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands UpperHalfPlane ContDiff

local notation "ℍ₀" => upperHalfPlaneSet
local notation "Holo(" f ")" => DifferentiableOn ℂ f ℍ₀

namespace MagicFunction.a.ComplexIntegrands

variable {r : ℝ}

private lemma mapsTo_smulAux' (g : GL (Fin 2) ℝ) :
    MapsTo (UpperHalfPlane.smulAux' g) ℍ₀ ℍ₀ := fun z hz => by
  simpa [upperHalfPlaneSet, UpperHalfPlane.smulAux] using
    (UpperHalfPlane.smulAux g ⟨z, by simpa [upperHalfPlaneSet] using hz⟩).2

/-- `φ₀''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₀''_holo : Holo(φ₀'') := by
  have h_eq :
      EqOn φ₀'' (fun z => (F ∘ UpperHalfPlane.ofComplex) z / (Δ ∘ UpperHalfPlane.ofComplex) z) ℍ₀ :=
    fun z hz => by simp [φ₀''_def hz, F, φ₀, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine DifferentiableOn.congr ?_ h_eq
  exact (UpperHalfPlane.mdifferentiable_iff.mp F_holo).div
    (UpperHalfPlane.mdifferentiable_iff.mp Delta.holo') fun z hz => by
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Δ_ne_zero]

/-- `φ₂''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₂''_holo : Holo(φ₂'') := by
  have hE₄ := (mdifferentiable_iff (f := (E₄ : ℍ → ℂ))).1 E₄.holo'
  refine ((hE₄.mul (((mdifferentiable_iff (f := E₂)).1 E₂_holo').mul hE₄ |>.sub
      ((mdifferentiable_iff (f := (E₆ : ℍ → ℂ))).1 E₆.holo'))).div
    ((UpperHalfPlane.mdifferentiable_iff (f := (Δ : ℍ → ℂ))).1 <| by
      simpa [Delta_apply] using
        (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (Delta z : ℂ))))
    (fun z hz => by
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
        Δ_ne_zero (UpperHalfPlane.ofComplex z))).congr fun z hz => ?_
  have hz' : 0 < z.im := by simpa [upperHalfPlaneSet] using hz
  simp [φ₂'', φ₂', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']

/-- The integrand `Φ₁' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₁'_holo : Holo(Φ₁' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.add_const 1).pow 2
  refine φ₀''_holo.comp ((differentiableOn_const (-1)).div (differentiableOn_id.add_const 1)
    fun z hz h0 => (ne_of_gt hz) (by simpa using congrArg Complex.im h0)) ?_
  let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, 1]) (!![1, 1; -1, 0])
    (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
  exact MapsTo.congr (mapsTo_smulAux' g) fun _ _ ↦ by simp [smulAux', g, num, denom, σ]

/-- The integrand `Φ₁' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) ℍ₀ :=
  Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet

/-- The integrand `Φ₃' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₃'_holo : Holo(Φ₃' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.sub_const 1).pow 2
  refine φ₀''_holo.comp ((differentiableOn_const (-1)).div (differentiableOn_id.sub_const 1)
    fun z hz h0 => (ne_of_gt hz) (by simpa using congrArg Complex.im h0)) ?_
  let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, -1]) (!![-1, 1; -1, 0])
    (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
  exact MapsTo.congr (mapsTo_smulAux' g) fun _ _ ↦ by
    simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]

/-- The integrand `Φ₃' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₃' r) ℍ₀ :=
  Φ₃'_holo.contDiffOn isOpen_upperHalfPlaneSet

/-- The integrand `Φ₃' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn : ContDiffOn ℝ ∞ (Φ₃' r) ℍ₀ :=
  (Φ₃'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ

/-- The integrand `Φ₆' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₆'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₆' r) ℍ₀ :=
  ((by simpa [Φ₆'] using φ₀''_holo.mul (by fun_prop : DifferentiableOn ℂ
      (fun z : ℂ => cexp (π * (Complex.I : ℂ) * r * z)) ℍ₀)) : Holo(Φ₆' r)).contDiffOn
    isOpen_upperHalfPlaneSet

end MagicFunction.a.ComplexIntegrands

/-! ### Smoothness of the real integrands `Φ₂`, `Φ₄`, `Φ₆` -/

namespace MagicFunction.a.RealIntegrands

variable {r : ℝ}

/-- Smoothness of the real integrand `Φ₂ r` on `Icc (0, 1)`. -/
public theorem Φ₂_contDiffOn : ContDiffOn ℝ ∞ (Φ₂ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₂_def, Φ₂'] using ((Φ₁'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ).comp
    (((contDiffOn_const.add ofRealCLM.contDiff.contDiffOn).add contDiffOn_const).congr
      fun y hy ↦ by simpa [add_assoc] using z₂'_eq_of_mem (t := y) hy) z₂'_mapsto

/-- Smoothness of the real integrand `Φ₄ r` on `Icc (0, 1)`. -/
public theorem Φ₄_contDiffOn : ContDiffOn ℝ ∞ (Φ₄ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₄_def, Φ₄', smul_eq_mul] using ContDiffOn.const_smul (c := (-1 : ℂ))
    ((Φ₃'_contDiffOn (r := r)).comp
      (((contDiffOn_const.sub ofRealCLM.contDiff.contDiffOn).add contDiffOn_const).congr
        fun y hy ↦ by simpa [sub_eq_add_neg, add_assoc] using z₄'_eq_of_mem (t := y) hy)
      z₄'_mapsto)

/-- Smoothness of the real integrand `Φ₆ r` on `Ici 1`. -/
public theorem Φ₆_contDiffOn : ContDiffOn ℝ ∞ (Φ₆ r) (Ici (1 : ℝ)) := by
  simpa [Φ₆_def, smul_eq_mul] using ContDiffOn.const_smul (c := Complex.I)
    (((Φ₆'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ).comp
      ((contDiffOn_const.mul ofRealCLM.contDiff.contDiffOn).congr
        fun y hy ↦ by simpa using z₆'_eq_of_mem (t := y) hy)
      z₆'_mapsto)

end MagicFunction.a.RealIntegrands

end a_Basic_section

/-! ## Polynomial Fourier coefficient bounds (originally in `MagicFunction.PolyFourierCoeffBound`)

* Core lemma `DivDiscBoundOfPolyFourierCoeff` (Lemma 7.4 in the blueprint): explicit upper bound
  on `‖f / Δ‖` for `f : ℍ → ℂ` whose Fourier coefficients are polynomially bounded.
* Corollaries: Fourier coefficients of `(A_E)^2` via the Cauchy product, repackaged as `fouterm`,
  and concrete exponential decay estimates on `φ₀`.
-/

namespace MagicFunction.PolyFourierCoeffBound

noncomputable section

open scoped UpperHalfPlane ArithmeticFunction.sigma BigOperators

open Filter Complex Real Asymptotics ArithmeticFunction

/-- If `‖r‖ < 1` and `u n` grows at most polynomially, then `‖u n * r ^ n‖` is summable. -/
public theorem summable_real_norm_mul_geometric_of_norm_lt_one {k : ℕ} {r : ℂ}
    (hr : ‖r‖ < 1) {u : ℕ → ℂ} (hu : u =O[atTop] (fun n ↦ (↑(n ^ k) : ℝ))) :
    Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  refine summable_of_isBigO_nat (g := fun n ↦ ‖(↑(n ^ k) : ℂ) * r ^ n‖) ?_ ?_
  · simpa [Nat.cast_pow] using summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℂ) k (r := r) hr
  · simpa [norm_mul, Real.norm_eq_abs, Complex.norm_real, Nat.cast_pow] using
      (hu.norm_left.mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ ‖r ^ n‖) atTop))

/-- Summability of `(n+s)^k * exp(-2π n)` on `ℕ`, used to justify `q`-series limits. -/
public theorem summable_pow_shift_mul_exp (k s : ℕ) :
    Summable (fun n : ℕ => ((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * n)) := by
  have hs : Summable (fun n : ℕ => ((n + s : ℝ) ^ k) * Real.exp (-2 * Real.pi * (n + s : ℝ))) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff s (f := fun n : ℕ =>
        ((n : ℝ) ^ k) * Real.exp (-2 * Real.pi * (n : ℝ)))).2 (by
          simpa [mul_assoc] using
            Real.summable_pow_mul_exp_neg_nat_mul k (r := 2 * Real.pi) (by positivity))
  refine (hs.mul_left (Real.exp (2 * Real.pi * (s : ℝ)))).congr fun n => ?_
  rw [show (-2 * Real.pi * (n : ℝ)) = 2 * Real.pi * (s : ℝ) + -2 * Real.pi * (n + s : ℝ) by ring,
    Real.exp_add]; ring

/-- Monotonicity of `∏'` under pointwise inequalities, for nonnegative and multipliable families. -/
private lemma tprod_le_of_nonneg_of_multipliable {β : Type*} {f g : β → ℝ} (hfnn : 0 ≤ f)
    (hfg : f ≤ g) (hf : Multipliable f) (hg : Multipliable g) : ∏' b, f b ≤ ∏' b, g b :=
  le_of_tendsto_of_tendsto' hf.hasProd hg.hasProd fun _ ↦
    Finset.prod_le_prod (fun i _ ↦ hfnn i) fun i _ ↦ hfg i

/-- A single Fourier term in the `π i` convention. -/
@[expose] public def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
  (coeff i) * cexp (π * I * i * x)

variable (z : ℍ) (hz : 1 / 2 < z.im) (c : ℤ → ℂ) (n₀ : ℤ) (hcn₀ : c n₀ ≠ 0)
  (hcsum : Summable fun i : ℕ ↦ fouterm c z (i + n₀)) (k : ℕ)
  (hpoly : c =O[atTop] fun n ↦ (n ^ k : ℝ))
  (f : ℍ → ℂ) (hf : ∀ x : ℍ, f x = ∑' n : ℕ, fouterm c x (n + n₀))

/-- The explicit factor in `DivDiscBoundOfPolyFourierCoeff` bounding `f / Δ`. -/
public def DivDiscBound : ℝ :=
  (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

include hpoly in
lemma summable_norm_mul_rexp_neg_pi_div_two :
    Summable (fun n : ℕ => ‖c (n + n₀)‖ * rexp (-π * n / 2)) := by
  refine (summable_real_norm_mul_geometric_of_norm_lt_one (k := k) (r := cexp (-(π : ℂ) / 2))
    (by simp [Complex.norm_exp, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]) (by
    simpa using ((show (fun n : ℕ ↦ c (n + n₀)) =O[atTop]
        (fun n : ℕ ↦ ((n + n₀ : ℤ) : ℝ) ^ k) by
      simp only [isBigO_iff, eventually_atTop] at hpoly ⊢
      obtain ⟨C, m, hCa⟩ := hpoly
      exact ⟨C, (m - n₀).toNat, fun n _ ↦ hCa (n + n₀) (by grind)⟩).trans (by
      simp only [isBigO_iff, eventually_atTop]
      exact ⟨2 ^ k, n₀.natAbs, fun n _ ↦ by
        simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg, Nat.cast_nonneg, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (by
          norm_cast; cases abs_cases (n + n₀ : ℤ) <;> grind) _⟩)))).congr fun n => ?_
  rw [norm_mul, norm_pow, show ‖cexp (-(π : ℂ) / 2)‖ = rexp (-(π : ℝ) / 2) by
      simp [Complex.norm_exp, div_eq_mul_inv], ← Real.exp_nat_mul]
  congr 2; ring

include hcsum in
lemma aux_3 : Summable fun (i : ℕ) ↦ ‖c (i + n₀) * cexp (↑π * I * i * z)‖ :=
  summable_norm_iff.mpr <|
    (Summable.mul_right (cexp (↑π * I * (n₀ : ℂ) * z))⁻¹ hcsum).congr fun i => by
      simp only [fouterm, show cexp (↑π * I * (↑(↑i + n₀) : ℂ) * z) =
          cexp (↑π * I * (i : ℂ) * z) * cexp (↑π * I * (n₀ : ℂ) * z) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
      field_simp [Complex.exp_ne_zero]

lemma aux_5 (z : ℍ) : norm (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
    ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simpa [← norm_pow] using Multipliable.norm_tprod (MultipliableDeltaProductExpansion_pnat z)

lemma aux_6 (z : ℍ) : 0 ≤ ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 :=
  (aux_5 z).symm ▸ norm_nonneg _

private lemma summable_log_one_sub_rexp_pow_24 {c : ℝ} (hc : 0 < c) :
    Summable fun b : ℕ+ ↦ Real.log ((1 - rexp (-c * (b : ℝ))) ^ 24) := by
  simpa [log_pow, Nat.cast_ofNat, sub_eq_add_neg, smul_eq_mul] using Summable.const_smul (24 : ℝ)
    (Real.summable_log_one_add_of_summable ((by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((Real.summable_exp_nat_mul_iff (a := -c)).2 (by nlinarith)).comp_injective
          PNat.coe_injective :
      Summable fun b : ℕ+ ↦ Real.exp (-c * (b : ℝ))).neg))

lemma aux_tprod_one_sub_rexp_pow_24_pos (c : ℝ) (hc : 0 < c) :
    0 < ∏' (n : ℕ+), (1 - rexp (-c * (n : ℝ))) ^ 24 := by
  rw [← Real.rexp_tsum_eq_tprod (fun i ↦ by simp_all)]
  exacts [Real.exp_pos _, summable_log_one_sub_rexp_pow_24 hc]

lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    aux_tprod_one_sub_rexp_pow_24_pos (c := 2 * π * z.im) (by positivity)

include hcsum in
lemma aux_10 : Summable fun (n : ℕ) ↦ norm (c (n + n₀)) * rexp (-π * ↑n * z.im) := by
  refine (aux_3 z c n₀ hcsum).congr fun i => ?_
  rw [norm_mul, show (↑π * I * (i : ℂ) * z) = I * ((↑π * i) * z) by ring, Complex.norm_exp]; simp

lemma aux_11 : 0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
  simpa using aux_tprod_one_sub_rexp_pow_24_pos (c := π) pi_pos

lemma step_12a {r : ℝ} (hr : 0 < r) :
    Multipliable fun b : ℕ+ ↦ (1 - rexp (-r * (b : ℝ))) ^ 24 := by
  refine Real.multipliable_of_summable_log (fun i ↦ ?_) ?_
  · refine pow_pos (sub_pos.2 (Real.exp_lt_one_iff.2 ?_)) _
    nlinarith [show (0 : ℝ) < (i : ℝ) from mod_cast i.pos]
  exact summable_log_one_sub_rexp_pow_24 hr

include f hf z hz c n₀ hcsum k hpoly in
/-- A uniform bound on `‖(f z) / (Δ z)‖` for a function given by a Fourier series with polynomially
bounded coefficients, in terms of `DivDiscBound` and an exponential factor depending on `n₀`. -/
public theorem DivDiscBoundOfPolyFourierCoeff : norm ((f z) / (Δ z)) ≤
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        simp [DiscriminantProductFormula, hf, fouterm]
  _ = norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        congr; rw [← tsum_mul_left]; refine tsum_congr fun n => ?_
        rw [mul_left_comm, ← Complex.exp_add]; congr 2; ring
  _ = norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by field_simp
  _ = norm ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
        rw [mul_sub, sub_mul, ← Complex.exp_sub]; congr 6; ac_rfl
  _ = norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := by simp [← aux_5 z]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
        gcongr; exacts [aux_6 z, by simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
        gcongr
        exacts [aux_6 z, by simpa [norm_mul] using norm_tsum_le_tsum_norm (aux_3 z c n₀ hcsum)]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
        gcongr; exacts [aux_6 z, by simpa [norm_mul] using aux_3 z c n₀ hcsum,
          aux_10 z c n₀ hcsum, by simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]]
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
    have hpow : Multipliable fun b : ℕ+ ↦ ‖(1 - cexp (2 * ↑π * I * (b : ℂ) * z))‖ ^ 24 := by
      have h := (MultipliableEtaProductExpansion_pnat z).norm
      induction (24 : ℕ) with | zero => simp | succ n hn => simpa [pow_succ] using hn.mul h
    gcongr
    · exact aux_8 z
    refine tprod_le_of_nonneg_of_multipliable (fun n => by positivity) (fun n => ?_) ?_ hpow
    · simp only [neg_mul]; gcongr
      · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]; positivity
      · rw [show -(2 * π * n * z.im) = (2 * π * I * n * z).re by simp]
        exact (le_abs_self _).trans <| by
          simpa [Complex.norm_exp] using abs_norm_sub_norm_le (1 : ℂ) (cexp (2 * π * I * n * z))
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        step_12a (r := 2 * π * z.im) (mul_pos two_pi_pos (UpperHalfPlane.im_pos z))
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
    gcongr ?_ * ?_ / _
    · exact (aux_8 z).le
    refine Summable.tsum_le_tsum (fun n ↦ mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 ?_) (norm_nonneg _)) (aux_10 z c n₀ hcsum)
      (summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, neg_mul] using
      neg_le_neg (mul_le_mul_of_nonneg_left hz.le (by positivity : 0 ≤ (π : ℝ) * (n : ℝ)))
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
    have h0 (n : ℕ+) : 0 ≤ 1 - rexp (-π * (n : ℝ)) :=
      sub_nonneg.2 <| Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, n.pos])
    gcongr
    · exact aux_11
    refine tprod_le_of_nonneg_of_multipliable (fun n => pow_nonneg (h0 n) 24) (fun n =>
      pow_le_pow_left₀ (h0 n) (sub_le_sub_left (Real.exp_le_exp.2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm, mul_one] using
          neg_le_neg (mul_le_mul_of_nonneg_left (by nlinarith [hz] : (1 : ℝ) ≤ 2 * z.im)
            (by positivity : 0 ≤ (π : ℝ) * (n : ℝ))))) 1) 24)
      (step_12a pi_pos)
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using
        step_12a (r := 2 * π * z.im) (mul_pos two_pi_pos (UpperHalfPlane.im_pos z)))
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
      simp [DivDiscBound, mul_div_assoc, mul_comm, mul_assoc]

include hpoly hcn₀ in
public theorem DivDiscBound_pos : 0 < DivDiscBound c n₀ := by
  rw [DivDiscBound]
  refine div_pos (Summable.tsum_pos
    (summable_norm_mul_rexp_neg_pi_div_two (c := c) (n₀ := n₀) (k := k) hpoly)
    (fun _ => by positivity) 0 ?_) aux_11
  simpa using norm_pos_iff.2 hcn₀

/-! ### Corollaries: Fourier coefficients of `(A_E)^2` -/

public def A_E_sq_coeff (m : ℕ) : ℂ :=
  ∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2

public lemma norm_A_E_coeff_le (n : ℕ) :
    ‖A_E_coeff n‖ ≤ (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 := by
  nlinarith [show ‖A_E_coeff n‖ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) by
    simpa using norm_A_E_coeff n,
    show (σ 3 (n + 1) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 from mod_cast sigma_bound 3 (n + 1),
    Nat.zero_le n]

public lemma norm_A_E_sq_coeff_le (m : ℕ) :
    ‖A_E_sq_coeff m‖ ≤ (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by
  calc ‖A_E_sq_coeff m‖
      = ‖∑ p ∈ Finset.antidiagonal m, A_E_coeff p.1 * A_E_coeff p.2‖ := by simp [A_E_sq_coeff]
    _ ≤ ∑ p ∈ Finset.antidiagonal m, ‖A_E_coeff p.1 * A_E_coeff p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.antidiagonal m, (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 :=
        Finset.sum_le_sum fun p hp => by
          rw [Finset.mem_antidiagonal] at hp
          rw [norm_mul, show (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 10 =
            ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) * ((720 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 5) by ring]
          gcongr <;> exact (norm_A_E_coeff_le _).trans (by gcongr; omega)
    _ = (720 : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 11 := by simp [Finset.Nat.card_antidiagonal]; ring

public lemma A_E_sq_eq_tsum (z : ℍ) :
    (A_E z) ^ 2 =
      ∑' m : ℕ, A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
  have ht_norm : Summable (fun n : ℕ => ‖A_E_term z n‖) := by
    set r : ℝ := Real.exp (-2 * Real.pi * z.im)
    let g : ℕ → ℝ := fun n => (720 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (show Summable g by
        simpa [g, mul_assoc, mul_left_comm, mul_comm, Nat.cast_add, Nat.cast_one] using
          ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) 1).2
            (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 (by
              simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using Real.exp_lt_one_iff.2 (by
                nlinarith [Real.pi_pos, UpperHalfPlane.im_pos z] :
                  (-2 * Real.pi * z.im) < 0)))).mul_left (720 : ℝ))
    calc ‖A_E_term z n‖
        = ‖A_E_coeff n‖ * ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ := by simp [A_E_term]
      _ ≤ g n := by
          simpa [g, mul_assoc, mul_comm] using mul_le_mul (norm_A_E_coeff_le n)
            (show ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ ≤ r ^ (n + 1) by
              rw [show ‖cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))‖ =
                  rexp (((n + 1 : ℕ) : ℝ) * (-2 * π * z.im)) by
                simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm],
                Real.exp_nat_mul]) (norm_nonneg _) (by positivity)
  have hanti (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2) =
        A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
    rw [show (∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2) =
        ∑ p ∈ Finset.antidiagonal m, (A_E_coeff p.1 * A_E_coeff p.2) *
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) from Finset.sum_congr rfl fun p hp => by
      rw [Finset.mem_antidiagonal] at hp
      have hexp : cexp (2 * π * I * ((p.1 + 1 : ℕ) : ℂ) * (z : ℂ)) *
          cexp (2 * π * I * ((p.2 + 1 : ℕ) : ℂ) * (z : ℂ)) =
            cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (z : ℂ)) := by
        rw [← Complex.exp_add]; congr 1
        push_cast [← (show (p.1 + 1 : ℕ) + (p.2 + 1 : ℕ) = m + 2 by omega)]; ring
      dsimp [A_E_term]; exact CancelDenoms.mul_subst rfl hexp rfl]
    simp [Finset.sum_mul, A_E_sq_coeff, mul_assoc]
  rw [show (A_E z) ^ 2 = (∑' n : ℕ, A_E_term z n) * (∑' n : ℕ, A_E_term z n) by
    rw [← A_E_eq_tsum z]; ring,
    (by simpa using tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ht_norm ht_norm :
      (∑' n : ℕ, A_E_term z n) * (∑' n : ℕ, A_E_term z n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, A_E_term z p.1 * A_E_term z p.2)]
  exact tsum_congr hanti

/-! ### Converting to `fouterm` coefficients -/

public noncomputable def A_E_sq_fourierCoeff : ℤ → ℂ
  | (Int.ofNat j) => if 4 ≤ j ∧ Even j then A_E_sq_coeff (j / 2 - 2) else 0
  | (Int.negSucc _) => 0

public lemma A_E_sq_fourierCoeff_four_ne_zero : A_E_sq_fourierCoeff 4 ≠ 0 := by
  simp [A_E_sq_fourierCoeff, show 4 ≤ (4 : ℕ) ∧ Even (4 : ℕ) by decide, A_E_sq_coeff, A_E_coeff,
    show (720 : ℂ) ≠ 0 by norm_num]

public lemma norm_A_E_sq_fourierCoeff_ofNat_le (j : ℕ) (hj : 4 ≤ j) :
    ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 := by
  by_cases hjEven : Even j
  · refine ((show ‖A_E_sq_fourierCoeff (Int.ofNat j)‖ = ‖A_E_sq_coeff (j / 2 - 2)‖ by
        simp [A_E_sq_fourierCoeff, hj, hjEven]).trans_le <| by
      simpa using norm_A_E_sq_coeff_le (j / 2 - 2)).trans ?_
    gcongr; exact_mod_cast (by omega : j / 2 - 2 + 1 ≤ j)
  · simp [A_E_sq_fourierCoeff, show ¬(4 ≤ j ∧ Even j) from fun h => hjEven h.2,
      show 0 ≤ (720 : ℝ) ^ 2 * (j : ℝ) ^ 11 by positivity]

public lemma A_E_sq_fourierCoeff_isBigO :
    A_E_sq_fourierCoeff =O[atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  simp only [isBigO_iff, eventually_atTop, ge_iff_le]
  refine ⟨(720 : ℝ) ^ 2, (4 : ℤ), fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ n)
  simpa using norm_A_E_sq_fourierCoeff_ofNat_le j (mod_cast hn)

public lemma A_E_sq_fourierCoeff_summable (z : ℍ) (hz : 1 / 2 < z.im) :
    Summable (fun i : ℕ ↦ fouterm A_E_sq_fourierCoeff z (i + 4)) := by
  set r : ℝ := Real.exp (-Real.pi / 2)
  let g : ℕ → ℝ := fun m => ((m : ℝ) ^ 11) * r ^ m
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((show Summable (fun n : ℕ => g (n + 4)) by
      simpa [g] using (summable_nat_add_iff (f := g) 4).2
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 (by
          simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using
            Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos] :
              (-Real.pi / 2 : ℝ) < 0)))).mul_left ((720 : ℝ) ^ 2))
  have hexp : ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ ≤ r ^ (n + 4) := by
    rw [show ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ =
        Real.exp ((-Real.pi * ((n + 4 : ℕ) : ℝ)) * z.im) by
      simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]]
    refine (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hz.le
      (by nlinarith [Real.pi_pos]))).trans_eq ?_
    rw [show (-Real.pi * ((n + 4 : ℕ) : ℝ)) * (1 / 2 : ℝ) =
      ((n + 4 : ℕ) : ℝ) * (-Real.pi / 2 : ℝ) by ring, Real.exp_nat_mul]
  calc ‖fouterm A_E_sq_fourierCoeff z (n + 4)‖
      = ‖A_E_sq_fourierCoeff (Int.ofNat (n + 4))‖ *
          ‖cexp (↑π * I * (Int.ofNat (n + 4)) * z)‖ := by simp [fouterm]
    _ ≤ ((720 : ℝ) ^ 2 * ((n + 4 : ℕ) : ℝ) ^ 11) * (r ^ (n + 4)) := by
        gcongr; exact norm_A_E_sq_fourierCoeff_ofNat_le (j := n + 4) (by omega)
    _ = ((720 : ℝ) ^ 2) * g (n + 4) := by simp [g, mul_assoc, mul_left_comm, mul_comm]

public lemma A_E_sq_series_summable (x : ℍ) :
    Summable (fun m : ℕ => A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
  set r : ℝ := Real.exp (-2 * Real.pi * x.im)
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((show Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm, Nat.cast_add, Nat.cast_one] using
        ((summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ) ^ 11) * r ^ m) 1).2
          (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 11 (by
            simpa [r, Real.norm_of_nonneg (Real.exp_pos _).le] using Real.exp_lt_one_iff.2 (by
              nlinarith [Real.pi_pos, UpperHalfPlane.im_pos x] :
                (-2 * Real.pi * x.im) < 0)))).mul_right r).mul_left ((720 : ℝ) ^ 2))
  calc ‖A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖
      = ‖A_E_sq_coeff m‖ * ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ := by simp
    _ ≤ ((720 : ℝ) ^ 2) * (((m + 1 : ℕ) : ℝ) ^ 11 * r ^ (m + 2)) := by
        nlinarith [mul_le_mul (norm_A_E_sq_coeff_le m)
          (show ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ ≤ r ^ (m + 2) by
            rw [show ‖cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))‖ =
                Real.exp (((m + 2 : ℕ) : ℝ) * (-2 * Real.pi * x.im)) by
              simp [Complex.norm_exp, mul_re, mul_im, mul_assoc, mul_left_comm, mul_comm],
              Real.exp_nat_mul]) (norm_nonneg _) (by positivity)]

public lemma A_E_sq_fourierCoeff_hf (x : ℍ) :
    (A_E x) ^ 2 = ∑' (n : ℕ), fouterm A_E_sq_fourierCoeff x (n + 4) := by
  let f : ℕ → ℂ := fun n => fouterm A_E_sq_fourierCoeff x (n + 4)
  let g : ℕ → ℂ := fun m => A_E_sq_coeff m * cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ))
  have hodd_term (m : ℕ) : f (2 * m + 1) = 0 := by
    simp only [f, fouterm, show ((2 * m + 1 : ℕ) : ℤ) + (4 : ℤ) = (Int.ofNat (2 * m + 5)) by
      simpa [show (2 * m + 1) + 4 = 2 * m + 5 by omega] using Int.ofNat_add_ofNat (2 * m + 1) 4,
      A_E_sq_fourierCoeff, if_neg (show ¬(4 ≤ (2 * m + 5) ∧ Even (2 * m + 5)) by
        grind only [= Nat.even_iff]), zero_mul]
  have heven_term (m : ℕ) : f (2 * m) = g m := by
    have hc : A_E_sq_fourierCoeff (Int.ofNat (2 * m + 4)) = A_E_sq_coeff m := by
      simp [A_E_sq_fourierCoeff,
        show 4 ≤ (2 * m + 4) ∧ Even (2 * m + 4) from ⟨by omega, by simp [parity_simps]⟩,
        show (2 * m + 4) / 2 - 2 = m by rw [show 2 * m + 4 = 2 * (m + 2) by ring]; simp]
    have hexp : cexp (π * I * ((Int.ofNat (2 * m + 4) : ℂ)) * (x : ℂ)) =
        cexp (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) :=
      congrArg Complex.exp <| show (π * I * ((2 * m + 4 : ℕ) : ℂ) * (x : ℂ)) =
        (2 * π * I * ((m + 2 : ℕ) : ℂ) * (x : ℂ)) by push_cast; ring
    dsimp [f, g, fouterm]
    rw [show (2 * (m : ℤ) + 4 : ℤ) = Int.ofNat (2 * m + 4) by simp, hc, hexp]
  rw [show (∑' n : ℕ, f n) = (∑' m : ℕ, g m) by
    simpa [tsum_congr heven_term, tsum_congr hodd_term] using
      (tsum_even_add_odd (f := f)
        ((summable_congr heven_term).mpr (by simpa [g] using A_E_sq_series_summable x))
        (by simp [funext hodd_term] : Summable (fun m : ℕ => f (2 * m + 1)))).symm]
  exact A_E_sq_eq_tsum x

/-- Exponential decay for the magic function `φ₀` in the upper half-plane. -/
public theorem norm_φ₀_le : ∃ C₀ > 0, ∀ z : ℍ, 1 / 2 < z.im →
    norm (φ₀ z) ≤ C₀ * rexp (-2 * π * z.im) := by
  refine ⟨DivDiscBound A_E_sq_fourierCoeff 4, ?_, ?_⟩
  · simpa [gt_iff_lt] using
      DivDiscBound_pos (c := A_E_sq_fourierCoeff) (n₀ := (4 : ℤ))
        (hcn₀ := A_E_sq_fourierCoeff_four_ne_zero) (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO)
  · intro z hz
    have hmain :
        norm (((A_E z) ^ 2) / (Δ z)) ≤
          (DivDiscBound A_E_sq_fourierCoeff 4) * rexp (-π * ((4 : ℤ) - 2) * z.im) :=
      DivDiscBoundOfPolyFourierCoeff (z := z) (hz := hz) (c := A_E_sq_fourierCoeff)
        (n₀ := (4 : ℤ)) (hcsum := by simpa using A_E_sq_fourierCoeff_summable (z := z) hz)
        (k := 11) (hpoly := A_E_sq_fourierCoeff_isBigO) (f := fun z ↦ (A_E z) ^ 2)
        (hf := fun x => by simpa using A_E_sq_fourierCoeff_hf (x := x))
    have hrexp : rexp (-(π * (4 - 2) * z.im)) = rexp (-(2 * π * z.im)) := by congr 1; ring
    simpa [φ₀, A_E, hrexp] using hmain

/-- Uniform bound for `φ₀''` on `Im z > 1/2`, specialising `norm_φ₀_le`. -/
public lemma norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im {C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * rexp (-2 * π * z.im)) (z : ℍ)
    (hz : 1 / 2 < z.im) : ‖φ₀'' (z : ℂ)‖ ≤ C₀ * rexp (-π) := by
  have hzpos : 0 < (z : ℂ).im := by simpa using lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz
  calc
    ‖φ₀'' (z : ℂ)‖ = ‖φ₀ z‖ := by
      simp [φ₀''_def (z := (z : ℂ)) hzpos, show (⟨(z : ℂ), hzpos⟩ : ℍ) = z from by ext; rfl]
    _ ≤ C₀ * rexp (-2 * π * z.im) := hC₀ z hz
    _ ≤ C₀ * rexp (-π) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, hz])) hC₀_pos.le

end

end MagicFunction.PolyFourierCoeffBound

/-! ## Schwartz property and integral estimates (originally in `Schwartz.Basic`) -/

open scoped Topology
open Complex Real Set MeasureTheory Filter intervalIntegral

namespace MagicFunction.a.IntegralEstimates

/-- Bound `‖(coeff t) ^ n * g r t‖` from bounds on `‖coeff t‖` and `‖g r t‖`. -/
public lemma norm_pow_mul_mul_le {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {C G : ℝ} {n : ℕ} {r t : ℝ}
    (hC : 0 ≤ C) (hcoeff : ‖coeff t‖ ≤ C) (hg : ‖g r t‖ ≤ G) :
    ‖(coeff t) ^ n * g r t‖ ≤ C ^ n * G := by
  simpa [norm_mul, norm_pow] using
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hcoeff n) hg (norm_nonneg _) (pow_nonneg hC _)

/-- Bound `iteratedDeriv n I` from a set-integral representation with uniform bounds. -/
public lemma iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} (n : ℕ)
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hrepr : iteratedDeriv n I = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t) :
    ∃ C₁ > 0, ∀ r : ℝ, ‖iteratedDeriv n I r‖ ≤ C₁ * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg_bound
  refine ⟨(2 * π) ^ n * (C₀ * rexp (-π) * 2), by positivity, fun r ↦ ?_⟩
  simpa [congrArg (fun f : ℝ → ℂ ↦ f r) hrepr, volume_real_Ioo_of_le zero_le_one] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) 1)
      (f := fun t ↦ (coeff t) ^ n * g r t) measure_Ioo_lt_top fun t ht ↦ by
        simpa [mul_assoc, mul_left_comm, mul_comm] using norm_pow_mul_mul_le (n := n)
          (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (by positivity) (hcoeff t ht) (hC₀ r t ht)

/-- Integrability of `(coeff t) ^ n * g r t` from uniform bounds, on `volume.restrict
`Ioo (0, 1)`. -/
public lemma integrable_pow_mul_of_volume_restrict_Ioo01 {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    {n : ℕ} {r : ℝ}
    (hmeas : AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r)) :
    Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
  obtain ⟨C₀, _, hC₀⟩ := hg
  have hbd : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      ‖(coeff t) ^ n * g r t‖ ≤ (2 * π) ^ n * (C₀ * rexp (-π) * 2) * rexp (-π * r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa [mul_assoc, mul_left_comm, mul_comm] using norm_pow_mul_mul_le
      (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n) (by positivity) (hcoeff t ht) (hC₀ r t ht)
  simpa [IntegrableOn] using
    Measure.integrableOn_of_bounded (s := Set.univ) (measure_ne_top _ _) hmeas (by simpa using hbd)

/-- Differentiate `x ↦ ∫ (coeff t) ^ n * g x t` under the integral, given uniform bounds on `g` and
the representation `g x t = A t * cexp ((x : ℂ) * coeff t)`. -/
public lemma hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ} {n : ℕ} {x₀ : ℝ}
    (hμ : μ = (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t))
    (hmeas : ∀ n : ℕ, ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ)
    (hint : ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ ↦ (coeff t) ^ n * g x t) μ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t, (coeff t) ^ n * g x t ∂μ)
      (∫ t, (coeff t) ^ (n + 1) * g x₀ t ∂μ) x₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hg_bound
  let K : ℝ := (2 * π) ^ (n + 1) * (C₀ * rexp (-π) * 2) * rexp (π) * rexp (-π * x₀)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := x₀)
    (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos) (.of_forall (hmeas n))
    (hint n x₀) (hmeas (n + 1) x₀)
    (show ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ), ‖(coeff t) ^ (n + 1) * g x t‖ ≤ K from by
      rw [hμ]
      refine (ae_restrict_iff' measurableSet_Ioo).2 <| .of_forall fun t ht r hr ↦ ?_
      refine (norm_pow_mul_mul_le (G := C₀ * rexp (-π) * 2 * rexp (-π * r)) (n := n + 1)
        (by positivity) (hcoeff t ht) (hC₀ r t ht)).trans ?_
      simpa [K, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
        (show rexp (-π * r) ≤ rexp π * rexp (-π * x₀) by
          have : |r - x₀| < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hr
          simpa [Real.exp_add] using Real.exp_le_exp.2 (by
            nlinarith [Real.pi_pos, abs_lt.1 this |>.1] : (-π * r : ℝ) ≤ π + (-π * x₀)))
        (by positivity : (0 : ℝ) ≤ (2 * π) ^ (n + 1) * (C₀ * rexp (-π) * 2)))
    (integrable_const K) <| ae_of_all _ fun t x _hx ↦ by
      simpa [hg_repr, mul_assoc, mul_left_comm, mul_comm] using
        SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
          (a := A t) (c := coeff t) (n := n) (x := x)).2

/-- Express `iteratedDeriv n I` as a set integral of `(coeff t) ^ n * g r t` under suitable
uniform bounds. -/
public lemma iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ} {A : ℝ → ℂ}
    (hI : ∀ r : ℝ, I r = ∫ t in Ioo (0 : ℝ) 1, g r t)
    (hcoeff_cont : Continuous coeff)
    (hg_cont : ∀ r : ℝ, ContinuousOn (g r) (Ioo (0 : ℝ) 1))
    (hg_bound : ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hg_repr : ∀ r t, g r t = A t * cexp ((r : ℂ) * coeff t)) :
    ∀ n : ℕ, iteratedDeriv n I = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict_Ioo 0 1
  have hmeas (n : ℕ) (r : ℝ) : AEStronglyMeasurable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ := by
    simpa [μ] using ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ))
      ((hcoeff_cont.pow n).continuousOn.mul (hg_cont r)) measurableSet_Ioo
  have hint (n : ℕ) (r : ℝ) : Integrable (fun t : ℝ ↦ (coeff t) ^ n * g r t) μ :=
    integrable_pow_mul_of_volume_restrict_Ioo01 (hmeas n r) hcoeff hg_bound
  intro n
  induction n with
  | zero => funext r; simp [hI]
  | succ n hn => funext r; simp [iteratedDeriv_succ, hn,
      (show HasDerivAt (fun x : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g x t)
            (∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ (n + 1) * g r t) r from by
        simpa [μ] using hasDerivAt_integral_pow_mul_of_uniform_bound_ball_one (μ := μ)
          (n := n) (x₀ := r) rfl hg_bound hcoeff hg_repr hmeas hint).deriv]

/-- For each `k`, the function `x ↦ x ^ k * exp (-π * x)` is bounded on `[0, ∞)`. -/
public lemma pow_mul_exp_neg_pi_bounded (k : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * rexp (-π * x) ≤ C := by
  let f : ℝ → ℝ := fun x => x ^ k * rexp (-π * x)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (tendsto_id.const_mul_atTop Real.pi_pos)
    have hf : f = fun x : ℝ => (π ^ k)⁻¹ * ((π * x) ^ k * rexp (-(π * x))) := by
      funext x; simp [f, mul_assoc, mul_left_comm, mul_comm, mul_pow,
        pow_ne_zero k Real.pi_ne_zero]
    simpa [hf] using tendsto_const_nhds.mul h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
    (hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono fun _ => le_of_lt
  set N0 : ℝ := max N 0
  obtain ⟨x0, _, hxmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) N0)).exists_isMaxOn
      (nonempty_Icc.2 (le_max_right N 0)) (by fun_prop : Continuous f).continuousOn
  refine ⟨max 1 (f x0), fun x hx => ?_⟩
  by_cases hxN : x ≤ N0
  · exact (hxmax ⟨hx, hxN⟩).trans (le_max_right _ _)
  · exact (hN x ((le_max_left N 0).trans (le_of_not_ge hxN))).trans (le_max_left _ _)

/-- Variant for iterated derivatives: a uniform exponential bound on `‖iteratedDeriv n I x‖`
implies Schwartz inverse-power decay. -/
public lemma decay_of_bounding_uniform_norm_iteratedDeriv {I : ℝ → ℂ} (n : ℕ)
    (hI : ∃ C₁ > 0, ∀ x : ℝ, 0 ≤ x → ‖iteratedDeriv n I x‖ ≤ C₁ * rexp (-π * x)) (k : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖ ≤ C := by
  obtain ⟨C₁, _, hC₁⟩ := hI
  obtain ⟨Cpow, hCpow⟩ := pow_mul_exp_neg_pi_bounded (k := k)
  refine ⟨C₁ * Cpow, fun x hx => ?_⟩
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖
        ≤ ‖x‖ ^ k * (C₁ * rexp (-π * x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := I) (x := x)]
            using hC₁ x hx
    _ = C₁ * (x ^ k * rexp (-π * x)) := by
      simp [Real.norm_of_nonneg hx, mul_left_comm, mul_comm]
    _ ≤ C₁ * Cpow := by gcongr; exact hCpow x hx

/-- Schwartz decay from `iteratedDeriv n I = ∫ t ∈ (0,1), coeff t ^ n * g r t`. -/
public lemma decay_of_iteratedDeriv_eq_integral_pow_mul
    {I : ℝ → ℂ} {coeff : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    (hg_bound :
      ∃ C₀ > 0, ∀ r : ℝ, ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r))
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) 1, ‖coeff t‖ ≤ 2 * π)
    (hrepr :
      ∀ n : ℕ,
        iteratedDeriv n I = fun r : ℝ ↦ ∫ t in Ioo (0 : ℝ) 1, (coeff t) ^ n * g r t) (k n : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I x‖ ≤ C :=
  let ⟨C₁, hC₁_pos, hC₁⟩ :=
    iteratedDeriv_bound_of_iteratedDeriv_eq_integral_pow_mul (n := n) hg_bound hcoeff (hrepr n)
  decay_of_bounding_uniform_norm_iteratedDeriv (n := n) ⟨C₁, hC₁_pos, fun x _ => hC₁ x⟩ k

/-! ## Common skeleton for `I₂'`/`I₄'` integral estimates. -/

namespace I24Common

noncomputable section

open scoped Function UpperHalfPlane Topology Real Complex
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open MagicFunction.PolyFourierCoeffBound MagicFunction.a.ComplexIntegrands

/-- The common coefficient pattern `coeff t = (-π) + (π * I) * shift t`. -/
@[expose] public def coeff (shift : ℝ → ℂ) : ℝ → ℂ :=
  fun t : ℝ ↦ (-π : ℂ) + (π * I) * shift t

public lemma continuous_coeff {shift : ℝ → ℂ} (hshift : Continuous shift) :
    Continuous (coeff shift) :=
  continuous_const.add (continuous_const.mul hshift)

/-- Uniform bound `‖coeff t‖ ≤ 2π` on `Ioo (0, 1)` given `‖shift t‖ ≤ 1` there. -/
public lemma coeff_norm_le {shift : ℝ → ℂ} (hshift : ∀ t ∈ Ioo (0 : ℝ) 1, ‖shift t‖ ≤ 1) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : ‖coeff shift t‖ ≤ 2 * π := by
  have hnorm : ‖(π * I : ℂ)‖ = π := by simp [abs_of_nonneg Real.pi_pos.le]
  calc
    ‖coeff shift t‖
        ≤ ‖(-π : ℂ)‖ + ‖(π * I : ℂ) * shift t‖ := norm_add_le _ _
    _ = π + π * ‖shift t‖ := by rw [norm_mul, hnorm]; simp [abs_of_nonneg Real.pi_pos.le]
    _ ≤ π + π * 1 := by gcongr; exact hshift t ht
    _ = 2 * π := by ring

/-- Uniform `‖g r t‖ ≤ C₀ * exp(-π) * 2 * exp(-π * r)` bound on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform_of {g : ℝ → ℝ → ℂ} {mob : ℝ → ℂ}
    (haux : ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ ‖φ₀'' (mob t)‖ * 2 * rexp (-π * r))
    (hmob_im : ∀ t ∈ Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (mob t).im) :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun r t ht ↦ (haux r t ht).trans ?_⟩
  gcongr
  have hpos : 0 < (mob t).im := one_half_pos.trans (hmob_im t ht)
  simpa [φ₀'', hpos] using
    norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos) (hC₀ := hC₀)
      (z := ⟨mob t, hpos⟩) (by simpa using hmob_im t ht)

end

end I24Common

end MagicFunction.a.IntegralEstimates

namespace MagicFunction.a.IntegralEstimates.I₂

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ioo (0, 1)` whose set integral is `I₂'`. -/
@[expose] public noncomputable def g (r t : ℝ) : ℂ :=
  φ₀'' (-1 / (t + I)) * (t + I) ^ 2 * cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r)

/-- Rewrite `I₂' r` as a set integral of `g r` over `Ioo (0, 1)`. -/
public lemma I₂'_eq_integral_g_Ioo (r : ℝ) : I₂' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp [I₂'_eq, intervalIntegral_eq_integral_uIoc, zero_le_one, g, integral_Ioc_eq_integral_Ioo]

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (↑t + I)).im :=
  fun t ht => by
    simpa [show (-1 / (↑t + I)).im = 1 / (t ^ 2 + 1) by
        simpa using SpherePacking.Integration.im_neg_one_div_ofReal_add_I (t := t)] using
      SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) :=
  I24Common.g_norm_bound_uniform_of (fun r t ht => by
    rw [g, norm_mul, norm_mul, norm_mul, mul_assoc, mul_assoc, norm_mul]
    gcongr
    · rw [norm_pow, ← normSq_eq_norm_sq, normSq_apply, add_re, ofReal_re, I_re, add_zero, add_im,
        ofReal_im, I_im, zero_add, mul_one]
      nlinarith [ht.1, ht.2]
    · conv_rhs => rw [← one_mul (rexp _), ← one_mul (rexp _)]
      gcongr <;> apply le_of_eq
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (-π * r)
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (π * r * t)
      · rw [norm_exp]; norm_cast) im_parametrisation_lower

noncomputable section Schwartz_Decay

open SchwartzMap

/-- Specialization of `I24Common.coeff` to `shift = fun t => (t : ℂ) - 1`. -/
@[expose] public def coeff : ℝ → ℂ := I24Common.coeff (fun t => (t : ℂ) - 1)

public lemma continuous_coeff : Continuous coeff :=
  I24Common.continuous_coeff (Complex.continuous_ofReal.sub continuous_const)

public lemma coeff_eq_sum (t : ℝ) :
    coeff t = (-π * I : ℂ) + (π * I * (t : ℂ)) + (-π : ℂ) := by
  simp [coeff, I24Common.coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm]

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖coeff t‖ ≤ 2 * π :=
  I24Common.coeff_norm_le (shift := fun t => (t : ℂ) - 1)
    (fun t ht => by
      change ‖((t : ℂ) - 1)‖ ≤ 1
      rw [show ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
      exact (by grind only [= mem_Ioo, = abs.eq_1, = max_def] : |t - 1| ≤ 1)) t ht

public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [coeff_eq_sum, Complex.exp_add, add_assoc, mul_assoc, mul_add, mul_left_comm, mul_comm]

/-- Schwartz-style decay estimate for the auxiliary integral `I₂'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₂' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.decay_of_iteratedDeriv_eq_integral_pow_mul
    g_norm_bound_uniform coeff_norm_le
    (fun n => iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₂') (coeff := coeff) (g := g) (A := fun t => φ₀'' (-1 / (t + I)) * (t + I) ^ 2)
      (hI := I₂'_eq_integral_g_Ioo) (hcoeff_cont := continuous_coeff)
      (hg_cont := fun r => by
        refine ((MagicFunction.a.RealIntegrands.Φ₂_contDiffOn (r := r)).continuousOn.mono
          fun _ hx => mem_Icc_of_Ioo hx).congr fun t ht => ?_
        have hz : z₂' t = (-1 : ℂ) + t + I := z₂'_eq_of_mem (mem_Icc_of_Ioo ht)
        have hexp' : cexp (π * I * r * (z₂' t : ℂ)) =
            cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r : ℂ) := by
          rw [show π * I * r * (z₂' t : ℂ) =
              (-π * I * r : ℂ) + (π * I * r * t : ℂ) + (-π * r : ℂ) by
            rw [hz]; ring_nf; rw [I_sq]; ring, Complex.exp_add, Complex.exp_add]
        simp [MagicFunction.a.RealIntegrands.Φ₂, MagicFunction.a.ComplexIntegrands.Φ₂',
          MagicFunction.a.ComplexIntegrands.Φ₁', g,
          show z₂' t + 1 = t + I by simp [hz, add_left_comm, add_comm], hexp']
        ac_rfl)
      (hg_bound := g_norm_bound_uniform) (hcoeff := coeff_norm_le)
      (hg_repr := fun r t => by rw [exp_r_mul_coeff]; simp [g]; ring) n)

end Schwartz_Decay
end I₂

end MagicFunction.a.IntegralEstimates

namespace MagicFunction.a.IntegralEstimates.I₄

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ioo (0, 1)` whose set integral is `I₄'`. -/
@[expose] public noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦
  -1 * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2 * cexp (π * I * r) * cexp (-π * I * r * t) *
    cexp (-π * r)

/-- Rewrite `I₄' r` as a set integral of `g r` over `Ioo (0, 1)`. -/
public lemma I₄'_eq_integral_g_Ioo (r : ℝ) : I₄' r = ∫ t in Ioo (0 : ℝ) 1, g r t := by
  simp [I₄'_eq, intervalIntegral_eq_integral_uIoc, zero_le_one, g, integral_Ioc_eq_integral_Ioo]

/-- A uniform lower bound on the imaginary part of the parametrisation `t ↦ -1 / (-t + I)`. -/
public lemma im_parametrisation_lower : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / 2 < (-1 / (-↑t + I)).im :=
  fun t ht => by
    simpa [show (-1 / (-↑t + I)).im = 1 / (t ^ 2 + 1) from by
      simpa using SpherePacking.Integration.im_neg_one_div_neg_ofReal_add_I (t := t)]
      using SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) :=
  I24Common.g_norm_bound_uniform_of (fun r t ht => by
    rw [g, norm_mul, norm_mul, norm_mul, mul_assoc, mul_assoc, norm_mul, norm_mul, norm_neg,
      norm_one, one_mul]
    gcongr
    · rw [norm_pow, ← normSq_eq_norm_sq, normSq_apply, add_re, neg_re, ofReal_re, I_re, add_zero,
        mul_neg, neg_mul, neg_neg, add_im, neg_im, ofReal_im, neg_zero, I_im, zero_add, mul_one]
      nlinarith [ht.1, ht.2]
    · conv_rhs => rw [← one_mul (rexp _), ← one_mul (rexp _)]
      gcongr <;> apply le_of_eq
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (π * r)
      · simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (-π * r * t)
      · simp [norm_exp]) im_parametrisation_lower

noncomputable section Schwartz_Decay

open SchwartzMap

/-- Specialization of `I24Common.coeff` to `shift = fun t => (1 : ℂ) - (t : ℂ)`. -/
@[expose] public def coeff : ℝ → ℂ := I24Common.coeff (fun t => (1 : ℂ) - (t : ℂ))

/-- The integrand for the `n`-th derivative, obtained by multiplying `g` by `(coeff t) ^ n`. -/
@[expose] public def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

/-- Uniform bound `‖coeff t‖ ≤ 2 * π` for `t ∈ Ioo (0, 1)`. -/
public lemma coeff_norm_le (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : ‖coeff t‖ ≤ 2 * π :=
  I24Common.coeff_norm_le (shift := fun t => (1 : ℂ) - (t : ℂ)) (fun t ht => by
    change ‖((1 : ℂ) - (t : ℂ))‖ ≤ 1
    rw [show ((1 : ℂ) - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    exact (by grind only [= mem_Ioo, = abs.eq_1, = max_def] : |1 - t| ≤ 1)) t ht

/-- Expand `cexp ((r : ℂ) * coeff t)` into the product of exponentials used in `g`. -/
public lemma exp_r_mul_coeff (r t : ℝ) :
    cexp ((r : ℂ) * coeff t) =
      cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) := by
  simp [show coeff t = (π * I : ℂ) + (-π * I * (t : ℂ)) + (-π : ℂ) by
    simp [coeff, I24Common.coeff, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm, add_comm],
    Complex.exp_add, add_assoc, mul_add, mul_left_comm, mul_comm]

/-- Schwartz-style decay estimate for the auxiliary integral `I₄'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.decay_of_iteratedDeriv_eq_integral_pow_mul
    g_norm_bound_uniform coeff_norm_le
    (fun n => iteratedDeriv_eq_setIntegral_pow_mul_of_uniform_bound_ball_one
      (I := I₄') (coeff := coeff) (g := g)
      (A := fun t : ℝ => (-1 : ℂ) * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2)
      (hI := I₄'_eq_integral_g_Ioo) (hg_cont := fun r => by
        refine ((MagicFunction.a.RealIntegrands.Φ₄_contDiffOn (r := r)).continuousOn.mono
          fun _ hx => mem_Icc_of_Ioo hx).congr fun t ht => ?_
        have hz : z₄' t = (1 : ℂ) - t + I := z₄'_eq_of_mem (mem_Icc_of_Ioo ht)
        have hz_coeff : (π * I : ℂ) * (z₄' t : ℂ) = coeff t := by
          simp [coeff, I24Common.coeff, hz, sub_eq_add_neg, mul_add, mul_assoc, add_left_comm,
            add_comm]
        simp [MagicFunction.a.RealIntegrands.Φ₄, MagicFunction.a.ComplexIntegrands.Φ₄',
          MagicFunction.a.ComplexIntegrands.Φ₃', g,
          show z₄' t - 1 = (-t : ℂ) + I by simp [hz, sub_eq_add_neg, add_assoc, add_comm],
          show cexp (π * I * r * (z₄' t : ℂ)) =
              cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r : ℂ) by
            simpa [mul_assoc, show (r : ℂ) * coeff t = (π * I * r : ℂ) * (z₄' t : ℂ) by
              rw [← hz_coeff]; ring] using exp_r_mul_coeff (r := r) (t := t)]
        ac_rfl)
      (hcoeff_cont := I24Common.continuous_coeff (continuous_const.sub Complex.continuous_ofReal))
      (hg_bound := g_norm_bound_uniform) (hcoeff := coeff_norm_le)
      (hg_repr := fun r t => by rw [exp_r_mul_coeff]; simp [g]; ring) n)

end Schwartz_Decay
end MagicFunction.a.IntegralEstimates.I₄

namespace MagicFunction.a.IntegralEstimates.I₃

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

noncomputable section

variable (r : ℝ)

/-- The integrand on `Ici 1` obtained from `I₃'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (π * I * r) * cexp (-π * r / s)

/-- Algebraic identity relating the `I₃'` integrand under the inversion `t ↦ 1 / t`. -/
public lemma inv_integrand_eq_integrand {t : ℝ} (ht₀ : 0 < t) (r : ℝ) (phase : ℂ) :
    (-I : ℂ) * φ₀'' (-1 / (I * t)) * t ^ 2 * phase * cexp (-π * r * t) =
      |(-1 / t ^ 2)| •
        ((-I : ℂ) * φ₀'' (I * (1 / t)) * (1 / t) ^ (-4 : ℤ) * phase * cexp (-π * r / (1 / t))) := by
  simp only [Int.reduceNeg, zpow_neg, real_smul]
  rw [show |-1 / t ^ 2| = 1 / t ^ 2 by simp [neg_div],
    show -1 / (I * t) = I / t by rw [div_mul_eq_div_div_swap, div_I]; ring]
  simp only [neg_mul, ofReal_div, ofReal_one, ofReal_pow, mul_div_assoc', mul_one, div_zpow,
    one_zpow, inv_div, div_one, div_div_eq_mul_div, mul_neg, div_mul_eq_mul_div, one_mul, neg_div']
  rw [eq_div_iff (pow_ne_zero 2 (mod_cast ht₀.ne')), neg_mul, neg_inj]
  ring_nf; ac_rfl

/-- Pointwise bound on `‖g r s‖` on `Ici 1` in terms of `‖φ₀'' (I * s)‖`. -/
public lemma I₃'_bounding_aux_1 (r : ℝ) :
    ∀ x ∈ Ici 1, ‖g r x‖ ≤ ‖φ₀'' (I * ↑x)‖ * rexp (-π * r / x) := by
  intro s hs
  simp only [g, neg_mul, Int.reduceNeg, zpow_neg, norm_neg, norm_mul, norm_I, one_mul, norm_inv,
    norm_zpow, norm_real, norm_eq_abs, norm_exp, neg_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, zero_mul, mul_im, add_zero, Real.exp_zero, div_ofReal_re, sub_zero]
  conv_rhs => rw [← mul_one ‖φ₀'' (I * ↑s)‖]
  gcongr
  have hs1 : (1 : ℝ) ≤ s := hs
  simpa [abs_of_nonneg (zero_le_one.trans hs1)] using
    inv_le_one_of_one_le₀ (one_le_zpow₀ hs1 <| Int.zero_le_ofNat 4)

/-- The model bound integrand is integrable on `Ici 1`. -/
public lemma Bound_integrableOn (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  set μ := volume.restrict (Ici (1 : ℝ))
  have h_g : Integrable (fun s ↦ C₀ * rexp (-2 * π * s)) μ :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (by linarith [pi_pos]) 1)).const_mul C₀
  have hφ : AEStronglyMeasurable (fun s ↦ rexp (-π * r / s)) μ := by fun_prop
  have hb : ∀ᵐ s ∂μ, ‖rexp (-π * r / s)‖ ≤ rexp (π * |r|) :=
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s (hs : 1 ≤ s) ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
      refine exp_le_exp.mpr <| (le_abs_self _).trans ?_
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg pi_pos.le, abs_of_nonneg (zero_le_one.trans hs)]
      exact div_le_self (by positivity) hs
  simpa [IntegrableOn, μ, mul_assoc] using h_g.mul_bdd hφ hb

end

end MagicFunction.a.IntegralEstimates.I₃

namespace MagicFunction.a.IntegralEstimates.I₁

noncomputable section

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ici 1` obtained from `I₁'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦
  -I * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * I * r) * cexp (-π * r / s)

lemma Reconciling_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
  simp only [I₁'_eq_Ioc, g]
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht => ?_)
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r
      (cexp (-π * I * r)))

/-- Rewrite `I₁' r` as an integral of `g r` over `Ici 1`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₁' r = ∫ s in Ici (1 : ℝ), (g r s) :=
  (Reconciling_Change_of_Variables (r := r)).trans <| by
    simpa using
      (SpherePacking.Integration.InvChangeOfVariables.integral_Ici_one_eq_integral_abs_deriv_smul
        (g := g r)).symm

end

end MagicFunction.a.IntegralEstimates.I₁

namespace MagicFunction.a.Schwartz.I1Decay

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter
open SpherePacking.Integration (μIciOne)

open MagicFunction.a.RealIntegrals
open MagicFunction.a.IntegralEstimates.I₁

def μ : Measure ℝ := μIciOne

def coeff (s : ℝ) : ℂ := (-π : ℂ) * (I + (1 / (s : ℂ)))

def gN (n : ℕ) (r s : ℝ) : ℂ := (coeff s) ^ n * g r s

/-- Constant bounding `‖φ₀ z‖` for `im z ≥ 1 / 2`, from `PolyFourierCoeffBound.norm_φ₀_le`. -/
public noncomputable def Cφ : ℝ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le.choose

public lemma Cφ_pos : 0 < Cφ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le.choose_spec.1

/-- Bound `‖φ₀'' (I * s)‖` for `s ≥ 1`. -/
public lemma norm_φ₀''_le (s : ℝ) (hs : 1 ≤ s) :
    ‖φ₀'' (I * (s : ℂ))‖ ≤ Cφ * rexp (-2 * π * s) := by
  have hpos : 0 < (I * (s : ℂ)).im := by simpa using lt_of_lt_of_le (by norm_num) hs
  let z : ℍ := ⟨I * (s : ℂ), hpos⟩
  have hz_im : z.im = s := by simp [z, UpperHalfPlane.im]
  simpa [Cφ, hz_im, show φ₀'' (I * (s : ℂ)) = φ₀ z by simpa [z] using φ₀''_def hpos] using
    (MagicFunction.PolyFourierCoeffBound.norm_φ₀_le).choose_spec.2 z
      (hz_im ▸ lt_of_lt_of_le (by norm_num : (1/2 : ℝ) < 1) hs)

lemma g_norm_bound (r s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    ‖g r s‖ ≤ Cφ * rexp (-2 * π * s) * rexp (-π * r / s) := by
  have hnorm : ‖MagicFunction.a.IntegralEstimates.I₃.g r s‖ = ‖g r s‖ := by
    let A : ℂ := (-I) * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * r / s)
    simp [show ‖cexp (π * I * r)‖ = (1 : ℝ) by
        simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (π * r),
      show ‖cexp (-(π * I * r))‖ = (1 : ℝ) by
        simpa [mul_assoc, mul_left_comm, mul_comm] using norm_exp_ofReal_mul_I (-π * r),
      show MagicFunction.a.IntegralEstimates.I₃.g r s = A * cexp (π * I * r) by
        simp [MagicFunction.a.IntegralEstimates.I₃.g, A, mul_assoc, mul_left_comm, mul_comm],
      show g r s = A * cexp (-π * I * r) by simp [g, A, mul_assoc, mul_left_comm, mul_comm]]
  refine ((by simpa [hnorm] using
    MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding_aux_1 (r := r) s hs :
    ‖g r s‖ ≤ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * r / s))).trans ?_
  gcongr; exact norm_φ₀''_le (s := s) hs

lemma coeff_norm_le (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) : ‖coeff s‖ ≤ 2 * π := by
  have hs1 : (1 : ℝ) ≤ s := hs
  calc ‖coeff s‖ ≤ (π : ℝ) * (‖I‖ + ‖(1 / (s : ℂ))‖) := by
        rw [coeff, norm_mul, show ‖(-π : ℂ)‖ = (π : ℝ) by
          simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]]
        gcongr; exact norm_add_le _ _
    _ ≤ (π : ℝ) * (1 + 1) := by
        gcongr <;> [simp; simpa [one_div, Complex.norm_real] using inv_le_one_of_one_le₀
          (by simpa [abs_of_nonneg (zero_le_one.trans hs1)] using hs1)]
    _ = 2 * π := by ring

lemma gN_norm_bound (n : ℕ) (r s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    ‖gN n r s‖ ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * r / s)) := by
  simpa [gN, norm_pow, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le (s := s) hs) n)
      (g_norm_bound (r := r) (s := s) hs) (norm_nonneg _) (by positivity)

/-- Continuity of `s ↦ φ₀'' (I * s)` on `Ici 1`. -/
public lemma φ₀''_I_mul_continuousOn :
    ContinuousOn (fun s : ℝ ↦ φ₀'' (I * (s : ℂ))) (Ici (1 : ℝ)) :=
  (continuousOn_const.mul
    (MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := (0 : ℝ))).continuousOn :
    ContinuousOn (fun s : ℝ ↦ (-I) * MagicFunction.a.RealIntegrands.Φ₆ (r := (0 : ℝ)) s)
      (Ici (1 : ℝ))).congr fun s hs => by
    simp [MagicFunction.a.ComplexIntegrands.Φ₆',
      MagicFunction.Parametrisations.z₆'_eq_of_mem hs, ← mul_assoc, mul_comm]

/-- Continuity of `s ↦ (s : ℂ) ^ (-4 : ℤ)` on `Ici 1`. -/
public lemma zpow_neg_four_continuousOn :
    ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-4 : ℤ)) (Ici (1 : ℝ)) :=
  Complex.continuous_ofReal.continuousOn.zpow₀ (-4 : ℤ) fun s hs =>
    Or.inl (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hs).ne')

lemma gN_measurable (n : ℕ) (r : ℝ) : AEStronglyMeasurable (gN n r) μ := by
  have hinv : ContinuousOn (fun s : ℝ ↦ (s : ℂ)⁻¹) (Ici (1 : ℝ)) :=
    Complex.continuous_ofReal.continuousOn.inv₀ fun s hs => by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hs).ne'
  have hcoeff : ContinuousOn coeff (Ici (1 : ℝ)) :=
    (continuousOn_const.mul (continuousOn_const.add hinv) :
      ContinuousOn (fun s : ℝ ↦ (-π : ℂ) * ((I : ℂ) + (s : ℂ)⁻¹)) (Ici (1 : ℝ))).congr
      fun s _ => by simp [coeff, one_div]
  have hg : ContinuousOn (fun s : ℝ ↦ g r s) (Ici (1 : ℝ)) :=
    (((continuousOn_const.mul φ₀''_I_mul_continuousOn).mul zpow_neg_four_continuousOn).mul
      continuousOn_const).mul <| by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (continuousOn_const.mul hinv :
          ContinuousOn (fun s : ℝ ↦ ((-π : ℂ) * (r : ℂ)) * (s : ℂ)⁻¹) (Ici (1 : ℝ))).cexp
  simpa [μ, SpherePacking.Integration.μIciOne] using
    ((by simpa [gN] using (hcoeff.pow n).mul hg :
      ContinuousOn (fun s : ℝ ↦ gN n r s) (Ici (1 : ℝ))).aestronglyMeasurable measurableSet_Ici)

lemma integrable_exp_neg_two_pi : Integrable (fun s : ℝ ↦ rexp (-(2 * π) * s)) μ := by
  simpa [IntegrableOn, SpherePacking.Integration.μIciOne, mul_assoc, mul_left_comm, mul_comm] using
    (MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn (r := (0 : ℝ)) (C₀ := (1 : ℝ)))

lemma exp_neg_pi_mul_div_le_exp_pi_abs (r s : ℝ) (hs : 1 ≤ s) :
    rexp (-π * r / s) ≤ rexp (π * |r|) :=
  Real.exp_le_exp.2 <| by
    have : (-r / s : ℝ) ≤ |r| / s := by
      simpa [abs_div, abs_neg, abs_of_nonneg (zero_le_one.trans hs)] using le_abs_self (-r / s)
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (this.trans (div_le_self (abs_nonneg r) hs)) Real.pi_pos.le

lemma integrable_gN (n : ℕ) (r : ℝ) : Integrable (gN n r) μ := by
  refine (integrable_exp_neg_two_pi.const_mul ((2 * π) ^ n * (Cφ * rexp (π * |r|)))).mono'
    (gN_measurable (n := n) (r := r)) ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs => ?_
  refine (gN_norm_bound (n := n) (r := r) (s := s) hs).trans ?_
  have hExp : rexp (-π * r / s) ≤ rexp (π * |r|) :=
    exp_neg_pi_mul_div_le_exp_pi_abs (r := r) (s := s) hs
  have hmul := mul_le_mul_of_nonneg_left hExp (show 0 ≤ (2 * π) ^ n * (Cφ * rexp (-2 * π * s)) from
    mul_nonneg (by positivity) (mul_nonneg Cφ_pos.le (Real.exp_pos _).le))
  grind only

lemma hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) :
    HasDerivAt (fun r : ℝ ↦ ∫ s, gN n r s ∂μ) (∫ s, gN (n + 1) r₀ s ∂μ) r₀ := by
  let R : ℝ := |r₀| + 1
  let bound : ℝ → ℝ := fun s ↦ (2 * π) ^ (n + 1) * (Cφ * rexp (π * R)) * rexp (-(2 * π) * s)
  have hbound_int : Integrable bound μ := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      integrable_exp_neg_two_pi.const_mul ((2 * π) ^ (n + 1) * (Cφ * rexp (π * R)))
  have h_bound :
      ∀ᵐ s ∂μ, ∀ r ∈ Metric.ball r₀ (1 : ℝ), ‖gN (n + 1) r s‖ ≤ bound s := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs r hr => ?_
    refine (gN_norm_bound (n := n + 1) (r := r) (s := s) hs).trans ?_
    have hExp : rexp (-π * r / s) ≤ rexp (π * R) :=
      (exp_neg_pi_mul_div_le_exp_pi_abs (r := r) (s := s) hs).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left
          (SpherePacking.ForMathlib.abs_le_abs_add_of_mem_ball hr) Real.pi_pos.le))
    have hmul := mul_le_mul_of_nonneg_left hExp
      (show 0 ≤ (2 * π) ^ (n + 1) * (Cφ * rexp (-2 * π * s)) from
        mul_nonneg (by positivity) (mul_nonneg Cφ_pos.le (Real.exp_pos _).le))
    grind only
  simpa [μ, SpherePacking.Integration.μIciOne] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun r s ↦ gN n r s) (x₀ := r₀) (s := Metric.ball r₀ (1 : ℝ))
      (hs := by simpa using Metric.ball_mem_nhds r₀ (by norm_num))
      (hF_meas := Filter.Eventually.of_forall fun r => gN_measurable (n := n) (r := r))
      (hF_int := integrable_gN (n := n) (r := r₀))
      (hF'_meas := gN_measurable (n := n + 1) (r := r₀))
      (h_bound := h_bound) (bound_integrable := hbound_int)
      (h_diff := (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s _ r _ => by
        have hg : HasDerivAt (fun r : ℝ ↦ g r s) (coeff s * g r s) r := by
          simpa [g, show ∀ r : ℝ, cexp ((r : ℂ) * coeff s) =
              cexp ((-π : ℂ) * I * (r : ℂ)) * cexp ((-π : ℂ) * (r : ℂ) / (s : ℂ)) from fun r => by
              rw [← Complex.exp_add]; congr 1; simp [coeff]; ring,
            mul_assoc, mul_left_comm, mul_comm]
            using SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const
              (a := (-I) * φ₀'' (I * (s : ℂ)) * (s ^ (-4 : ℤ) : ℂ)) (c := coeff s) (x := r)
        simpa [gN, pow_succ, mul_assoc] using hg.const_mul (coeff s ^ n))).2

lemma norm_iteratedDeriv_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n I₁' x‖ ≤
      ∫ s in Ici (1 : ℝ), (2 * π) ^ n * (Cφ * rexp (-2 * π * s) * rexp (-π * x / s)) := calc
    ‖iteratedDeriv n I₁' x‖ ≤ ∫ s in Ici (1 : ℝ), ‖gN n x s‖ := by
      have iteratedDeriv_eq_integral_gN :
          iteratedDeriv n I₁' = fun r : ℝ ↦ ∫ s, gN n r s ∂μ := by
        induction n with
        | zero => funext r; simp [iteratedDeriv_zero, gN, μ, μIciOne, Complete_Change_of_Variables]
        | succ n ih => funext r; simpa [iteratedDeriv_succ, ih] using
            (hasDerivAt_integral_gN (n := n) (r₀ := r)).deriv
      simpa [iteratedDeriv_eq_integral_gN, μ, SpherePacking.Integration.μIciOne] using
        norm_integral_le_integral_norm (gN n x)
    _ ≤ _ := setIntegral_mono_on
        (by simpa [IntegrableOn, μIciOne] using (integrable_gN (n := n) (r := x)).norm)
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn
            (r := x) (C₀ := Cφ)).const_mul ((2 * π) ^ n)))
        measurableSet_Ici fun s hs => gN_norm_bound (n := n) (r := x) (s := s) hs

lemma xpow_integral_le_of_Cpow (k : ℕ) {Cpow : ℝ}
    (hCpow : ∀ u : ℝ, 0 ≤ u → u ^ k * rexp (-u) ≤ Cpow) :
    ∀ x : ℝ, 0 ≤ x →
      x ^ k * (∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * x / s)) ≤
        ((π ^ k)⁻¹ * Cpow) * (∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)) := by
  intro x hx
  let f : ℝ → ℝ := fun s ↦ x ^ k * (rexp (-2 * π * s) * rexp (-π * x / s))
  let g : ℝ → ℝ := fun s ↦ ((π ^ k)⁻¹ * Cpow) * (s ^ k * rexp (-2 * π * s))
  have hf_int : IntegrableOn f (Ici (1 : ℝ)) volume := by
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using
      (MagicFunction.a.IntegralEstimates.I₃.Bound_integrableOn (r := x) (C₀ := (1 : ℝ))).const_mul
        (x ^ k)
  have hg_int : IntegrableOn g (Ici (1 : ℝ)) volume := by
    simpa [g, mul_assoc, mul_left_comm, mul_comm] using
      ((show IntegrableOn (fun s : ℝ ↦ s ^ k * rexp (-2 * π * s)) (Ici (1 : ℝ)) volume by
        simpa [mul_assoc] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := k) (b := 2 * π)
            (by positivity))).const_mul ((π ^ k)⁻¹ * Cpow)
  have hmono : ∀ s ∈ Ici (1 : ℝ), f s ≤ g s := fun s hs => by
    have hs1 : (1 : ℝ) ≤ s := hs
    have hpt : x ^ k * rexp (-π * x / s) ≤ (π ^ k)⁻¹ * Cpow * s ^ k := by
      set u : ℝ := (π * x) / s
      have hxpow : x ^ k = (π ^ k)⁻¹ * s ^ k * u ^ k := by
        simp [show x = u * s / π from CancelDenoms.cancel_factors_eq_div
          (id (div_mul_cancel₀ (π * x)
            (lt_of_lt_of_le (by norm_num) hs1).ne').symm) Real.pi_ne_zero,
          mul_pow, div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm]
      calc x ^ k * rexp (-π * x / s)
          = (π ^ k)⁻¹ * s ^ k * (u ^ k * rexp (-u)) := by
            rw [congrArg rexp (show -π * x / s = -u by ring), hxpow]; ring
        _ ≤ (π ^ k)⁻¹ * s ^ k * Cpow := by
            gcongr; exact hCpow u (div_nonneg (by positivity) (zero_le_one.trans hs1))
        _ = (π ^ k)⁻¹ * Cpow * s ^ k := by ring
    calc f s = rexp (-2 * π * s) * (x ^ k * rexp (-π * x / s)) := by simp [f, mul_assoc, mul_comm]
      _ ≤ rexp (-2 * π * s) * (((π ^ k)⁻¹ * Cpow) * s ^ k) := by gcongr
      _ = g s := by simp [g, mul_assoc, mul_left_comm, mul_comm]
  simpa [show (∫ s in Ici (1 : ℝ), f s) =
      x ^ k * (∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * x / s)) from
      integral_const_mul (x ^ k) fun a => rexp (-2 * π * a) * rexp (-π * x / a),
    show (∫ s in Ici (1 : ℝ), g s) =
      ((π ^ k)⁻¹ * Cpow) * (∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)) from
      integral_const_mul ((π ^ k)⁻¹ * Cpow) fun a => a ^ k * rexp (-2 * π * a),
    mul_assoc, mul_left_comm, mul_comm] using
    setIntegral_mono_on hf_int hg_int measurableSet_Ici hmono

/-- Schwartz-style decay estimate for `RealIntegrals.I₁'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₁' x‖ ≤ C := by
  intro k n
  obtain ⟨Cpow, hCpow⟩ : ∃ C, ∀ u : ℝ, 0 ≤ u → u ^ k * rexp (-u) ≤ C := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ => le_of_lt)
    obtain ⟨u0, _, hu0max⟩ := isCompact_Icc.exists_isMaxOn (s := Icc 0 (max N 0))
      ⟨0, le_refl _, le_max_right _ _⟩
      (show Continuous fun u : ℝ ↦ u ^ k * rexp (-u) by fun_prop).continuousOn
    refine ⟨max 1 (u0 ^ k * rexp (-u0)), fun u hu => ?_⟩
    by_cases huN : u ≤ max N 0
    exacts [(hu0max ⟨hu, huN⟩).trans (le_max_right _ _),
      (hN u ((le_max_left N 0).trans (le_of_not_ge huN))).trans (le_max_left _ _)]
  let I : ℝ := ∫ s in Ici (1 : ℝ), s ^ k * rexp (-2 * π * s)
  refine ⟨(2 * π) ^ n * (Cφ * ((π ^ k)⁻¹ * Cpow) * I), fun x hx => ?_⟩
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₁' x‖
        = x ^ k * ‖iteratedDeriv n I₁' x‖ := by
          simp [Real.norm_of_nonneg hx,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := I₁') (x := x)]
    _ ≤ x ^ k * (∫ s in Ici (1:ℝ), (2*π) ^ n * (Cφ * rexp (-2*π*s) * rexp (-π*x/s))) :=
        mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le (n := n) (x := x)) (by positivity)
    _ = ((2*π) ^ n * Cφ) * (x ^ k * (∫ s in Ici (1:ℝ), rexp (-2*π*s) * rexp (-π*x/s))) := by
        rw [show (∫ s in Ici (1:ℝ), (2*π) ^ n * (Cφ * rexp (-2*π*s) * rexp (-π*x/s))) =
          ((2 * π) ^ n * Cφ) * (∫ s in Ici (1:ℝ), rexp (-2*π*s) * rexp (-π*x/s)) by
          simpa [mul_assoc, mul_left_comm, mul_comm] using MeasureTheory.integral_const_mul
            (μ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))) ((2 * π) ^ n * Cφ)
            (fun s : ℝ ↦ rexp (-2 * π * s) * rexp (-π * x / s))]; ring
    _ ≤ ((2 * π) ^ n * Cφ) * (((π ^ k)⁻¹ * Cpow) * I) := mul_le_mul_of_nonneg_left
        (xpow_integral_le_of_Cpow (k := k) (Cpow := Cpow) hCpow x hx)
        (mul_nonneg (by positivity) Cφ_pos.le)
    _ = (2 * π) ^ n * (Cφ * ((π ^ k)⁻¹ * Cpow) * I) := by ring

end

end MagicFunction.a.Schwartz.I1Decay

namespace MagicFunction.a.IntegralEstimates.I₆

open scoped Function UpperHalfPlane Topology Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

variable (r : ℝ)

/-- The integrand on `Ici 1` whose set integral is `I₆'`. -/
@[expose] public noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦ I * φ₀'' (I * t) * cexp (-π * r * t)

/-- Rewrite `I₆' r` as a set integral of `g r` over `Ici 1` (up to the factor `2`). -/
public lemma I₆'_eq_integral_g_Ioo (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), g r t := by
  simp [I₆'_eq, g]

noncomputable section Schwartz_Decay

open SchwartzMap
open scoped Topology
open SpherePacking.Integration (μIciOne)

def coeff (t : ℝ) : ℂ := (-π * t : ℂ)

def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

lemma coeff_norm_pow_of_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖coeff t‖ ^ n = (π * t) ^ n := by
  simp [coeff, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht]

private lemma aestronglyMeasurable_gN (n : ℕ) (r : ℝ) :
    AEStronglyMeasurable (gN n r) μIciOne := by
  simpa [gN, μIciOne] using ContinuousOn.aestronglyMeasurable
    (((by unfold coeff; fun_prop : Continuous coeff).pow n).continuousOn.mul
      ((MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := r)).continuousOn.congr fun t ht ↦ by
        dsimp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆', g]
        rw [z₆'_eq_of_mem ht, show (π : ℂ) * I * (r : ℂ) * (I * (t : ℂ)) = -π * r * t by
          ring_nf; simp [I_sq]]; ac_rfl))
    measurableSet_Ici

/-- A uniform-in-`r` bound on the integrand `g r t` on `Ici 1`. -/
public lemma g_norm_bound_uniform :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ici (1 : ℝ),
      ‖g r t‖ ≤ C₀ * rexp (-2 * π * t) * rexp (-π * r * t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun r t ht ↦ ?_⟩
  have ht1 : (1 : ℝ) ≤ t := ht
  have hpos : 0 < (I * t).im := by simpa using one_pos.trans_le ht1
  rw [show ‖g r t‖ = ‖φ₀'' (I * t)‖ * rexp (-π * r * t) by simp [g, norm_exp]]
  gcongr
  simpa [φ₀'', hpos, one_pos.trans_le ht1] using hC₀ ⟨I * t, hpos⟩ (by simpa using by linarith)

private lemma integrable_gN (n : ℕ) (r : ℝ) (hr : -1 < r) : Integrable (gN n r) μIciOne := by
  obtain ⟨C₀, -, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ := fun t ↦ (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀
  have hbound_int : Integrable bound μIciOne := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (show Integrable (fun t : ℝ ↦ t ^ n * rexp (-(π * (r + 2)) * t)) μIciOne by
        simpa [IntegrableOn, μIciOne] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := π * (r + 2))
            (mul_pos Real.pi_pos (by linarith))).const_mul ((π ^ n) * C₀)
  refine Integrable.mono' hbound_int (aestronglyMeasurable_gN (n := n) (r := r)) <|
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hcoeff : ‖coeff t‖ ^ n ≤ (π * t) ^ n := by
    simpa using (coeff_norm_pow_of_nonneg (n := n) (t := t) ht0).le
  calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN]
    _ ≤ (π * t) ^ n * (C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) := by gcongr; exact hC₀ r t ht
    _ = bound t := by
      simp only [bound, mul_pow, ← show rexp (-2 * π * t) * rexp (-π * r * t) =
        rexp (-(π * (r + 2)) * t) by rw [← Real.exp_add]; ring_nf]; ring

private lemma hasDerivAt_integral_gN (n : ℕ) (r₀ : ℝ) (hr₀ : -1 < r₀) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ici (1 : ℝ), gN n r t)
      (∫ t in Ici (1 : ℝ), gN (n + 1) r₀ t) r₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let bound : ℝ → ℝ := fun t ↦ (π ^ (n + 1)) * (t ^ (n + 1) * rexp (-(π * (r₀ + 1)) * t)) * C₀
  have h_bound : ∀ᵐ t ∂μIciOne, ∀ r ∈ Metric.ball r₀ (1 : ℝ), ‖gN (n + 1) r t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht r hr ↦ ?_
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hr_lower : r₀ - 1 ≤ r := by
      nlinarith [abs_lt.1 (by simpa [Metric.mem_ball, dist_eq_norm] using hr : |r - r₀| < 1) |>.1]
    calc ‖gN (n + 1) r t‖ = ‖coeff t‖ ^ (n + 1) * ‖g r t‖ := by simp [gN]
      _ ≤ (π * t) ^ (n + 1) * (C₀ * rexp (-2 * π * t) * rexp (-π * (r₀ - 1) * t)) :=
        mul_le_mul (by simpa using (coeff_norm_pow_of_nonneg (n := n + 1) (t := t) ht0).le)
          (le_mul_of_le_mul_of_nonneg_left (hC₀ r t ht) (Real.exp_le_exp.2 <| by
            simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using
              mul_le_mul_of_nonpos_left
                (mul_le_mul_of_nonneg_right hr_lower ht0 : (r₀ - 1) * t ≤ r * t)
                (by nlinarith [Real.pi_pos] : (-π : ℝ) ≤ 0)) (by positivity))
          (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le ht0) (n + 1))
      _ = bound t := by
        simp only [bound, mul_pow, ← show rexp (-2 * π * t) * rexp (-π * (r₀ - 1) * t) =
          rexp (-(π * (r₀ + 1)) * t) by rw [← Real.exp_add]; ring_nf]; ring
  have bound_integrable : Integrable bound μIciOne := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (show Integrable (fun t : ℝ ↦ t ^ (n + 1) * rexp (-(π * (r₀ + 1)) * t)) μIciOne by
        simpa [IntegrableOn, μIciOne] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1)
            (b := π * (r₀ + 1)) (mul_pos Real.pi_pos (by linarith))).const_mul ((π ^ (n + 1)) * C₀)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μIciOne)
    (F := fun r t ↦ gN n r t) (x₀ := r₀) (s := Metric.ball r₀ (1 : ℝ))
    (hs := by simpa using Metric.ball_mem_nhds r₀ (by norm_num))
    (hF_meas := .of_forall fun r ↦ aestronglyMeasurable_gN (n := n) (r := r))
    (hF_int := integrable_gN (n := n) (r := r₀) hr₀)
    (hF'_meas := aestronglyMeasurable_gN (n := n + 1) (r := r₀))
    (h_bound := h_bound) (bound_integrable := bound_integrable)
    (h_diff := ae_of_all _ fun t r _ ↦ by
      simpa [gN, show ∀ y : ℝ, g y t = (I * φ₀'' (I * t)) * cexp ((y : ℂ) * coeff t) by
        intro y; simp [g, coeff, mul_assoc, mul_left_comm, mul_comm], pow_succ,
        mul_assoc, mul_left_comm, mul_comm] using
        SpherePacking.ForMathlib.hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const
          (a := I * φ₀'' (I * t)) (c := coeff t) (n := n) (x := r))).2

lemma iteratedDeriv_bound (n : ℕ) :
    ∃ C₁ > 0, ∀ r : ℝ, 0 ≤ r → ‖iteratedDeriv n I₆' r‖ ≤ C₁ * rexp (-π * r) := by
  have iteratedDeriv_eq : ∀ n : ℕ, ∀ r : ℝ, -1 < r →
      iteratedDeriv n I₆' r = 2 * ∫ t in Ici (1 : ℝ), gN n r t := by
    intro n
    induction n with
    | zero => intro r _; simp [gN, I₆'_eq_integral_g_Ioo]
    | succ n hn =>
      intro r hr
      calc iteratedDeriv (n + 1) I₆' r = deriv (iteratedDeriv n I₆') r := by
            simp [iteratedDeriv_succ]
        _ = deriv (fun x : ℝ ↦ 2 * ∫ t in Ici (1 : ℝ), gN n x t) r :=
          Filter.EventuallyEq.deriv_eq
            (by filter_upwards [Ioi_mem_nhds hr] with x hx using hn x hx)
        _ = 2 * ∫ t in Ici (1 : ℝ), gN (n + 1) r t := by
          simpa using ((hasDerivAt_integral_gN (n := n) (r₀ := r) hr).const_mul (2 : ℂ)).deriv
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := g_norm_bound_uniform
  let B : ℝ → ℝ := fun t ↦ C₀ * (π ^ n) * (t ^ n * rexp (-(2 * π) * t))
  have hB_int : IntegrableOn B (Ici (1 : ℝ)) volume := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      (show IntegrableOn (fun t : ℝ ↦ t ^ n * rexp (-(2 * π) * t)) (Ici (1 : ℝ)) volume by
        simpa using SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
          (n := n) (b := 2 * π) (by positivity)).const_mul (C₀ * (π ^ n))
  let A : ℝ := ∫ t in Ici (1 : ℝ), B t
  have hA_nonneg : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg (μ := volume) (s := Ici (1 : ℝ)) measurableSet_Ici
      fun t ht ↦ by have : 0 ≤ t := zero_le_one.trans ht; simp only [B]; positivity
  refine ⟨2 * (A + 1), by nlinarith [hA_nonneg], fun r hr ↦ ?_⟩
  have hr' : (-1 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  simpa [mul_assoc, mul_left_comm, mul_comm] using calc
    ‖iteratedDeriv n I₆' r‖ = 2 * ‖∫ t in Ici (1 : ℝ), gN n r t‖ := by
      rw [iteratedDeriv_eq n r hr']; simp
    _ ≤ 2 * ∫ t in Ici (1 : ℝ), B t * rexp (-π * r) := by
      gcongr
      refine (norm_integral_le_integral_norm (gN n r)).trans <| setIntegral_mono_on
        (by simpa [IntegrableOn, μIciOne] using (integrable_gN (n := n) (r := r) hr').norm)
        (by simpa [mul_assoc] using hB_int.mul_const (rexp (-π * r)))
        measurableSet_Ici fun t ht ↦ by
        have ht0 : 0 ≤ t := zero_le_one.trans ht
        calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN]
          _ ≤ ((π ^ n) * (t ^ n)) * (C₀ * rexp (-2 * π * t) * rexp (-π * r)) :=
            mul_le_mul (by simpa [mul_pow] using
                (coeff_norm_pow_of_nonneg (n := n) (t := t) ht0).le)
              (le_mul_of_le_mul_of_nonneg_left (hC₀ r t ht) (Real.exp_le_exp.2 <| by
                nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left (ht : (1 : ℝ) ≤ t) hr])
                (by positivity)) (by positivity) (by positivity)
          _ = B t * rexp (-π * r) := by simp [B, mul_assoc, mul_left_comm, mul_comm]
    _ = 2 * (A * rexp (-π * r)) := by
      rw [MeasureTheory.integral_mul_const (μ := volume.restrict (Ici (1 : ℝ)))]
    _ ≤ (2 * (A + 1)) * rexp (-π * r) := by nlinarith [hA_nonneg, Real.exp_pos (-π * r)]

/-- Schwartz-style decay estimate for `I₆'`. -/
public theorem decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C := fun k n ↦ by
  simpa using MagicFunction.a.IntegralEstimates.decay_of_bounding_uniform_norm_iteratedDeriv
    (I := I₆') (n := n) (iteratedDeriv_bound (n := n)) k

end Schwartz_Decay

end MagicFunction.a.IntegralEstimates.I₆

noncomputable section

open scoped ContDiff SchwartzMap
open SchwartzMap

namespace MagicFunction.a.Schwartz.SmoothI24Common

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.PolyFourierCoeffBound
open MagicFunction.a.ComplexIntegrands
open SpherePacking.Integration
open SpherePacking.ForMathlib

/-- The coefficient function `t ↦ (π * I) * z t` shared by `I₂'` and `I₄'`. -/
@[expose] public def coeff (z : ℝ → ℂ) : ℝ → ℂ := fun t : ℝ => ((π : ℂ) * I) * z t

/-- The Mobius argument `t ↦ -1 / (z t + shift)` used to feed `φ₀''`. -/
@[expose] public def arg (z : ℝ → ℂ) (shift : ℂ) : ℝ → ℂ :=
    fun t : ℝ => (-1 : ℂ) / (z t + shift)

/-- The integrand `t ↦ prefactor * (φ₀''(arg t) * (z t + shift)^2)`. -/
@[expose] public def hf (z : ℝ → ℂ) (shift prefactor : ℂ) : ℝ → ℂ :=
    fun t : ℝ => prefactor * (φ₀'' (arg z shift t) * (z t + shift) ^ (2 : ℕ))

public lemma coeff_norm_le {z : ℝ → ℂ} (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (t : ℝ) :
    ‖coeff z t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using norm_mul_pi_I_le_two_pi (z := z t) (hz := hnorm t)

public lemma continuous_coeff {z : ℝ → ℂ} (hz : Continuous z) : Continuous (coeff z) := by
  simpa [coeff, mul_assoc] using continuous_const.mul hz

/-- Continuity of `hf` on `Ioo 0 1` given the continuity of `z`, non-vanishing of
`z + shift`, and the geometric fact that `arg` lands in the upper half-plane. -/
public lemma continuousOn_hf {z : ℝ → ℂ} (shift prefactor : ℂ)
    (hz : Continuous z)
    (hden : ∀ t, t ∈ Ioo (0 : ℝ) 1 → z t + shift ≠ 0)
    (harg_im_pos : ∀ t, t ∈ Ioo (0 : ℝ) 1 → 0 < (arg z shift t).im) :
    ContinuousOn (hf z shift prefactor) (Ioo (0 : ℝ) 1) := by
  have harg : ContinuousOn (arg z shift) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.div (hz.continuousOn.add continuousOn_const) hden
  simpa [hf, mul_assoc] using continuousOn_const.mul
    ((φ₀''_holo.continuousOn.comp harg harg_im_pos).mul
      ((hz.add continuous_const).pow 2).continuousOn)

/-- Uniform bound on `hf` over `Ioo 0 1` given `‖z t‖ ≤ 2` and `Im(arg t) > 1/2`. -/
public lemma exists_bound_norm_hf {z : ℝ → ℂ} (shift prefactor : ℂ)
    (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (hshift : ‖shift‖ ≤ 1)
    (harg_im_half : ∀ t, t ∈ Ioo (0 : ℝ) 1 → (1 / 2 : ℝ) < (arg z shift t).im) :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf z shift prefactor t‖ ≤ M := by
  rcases norm_φ₀_le with ⟨C₀, hC₀_pos, hC₀⟩
  refine ⟨‖prefactor‖ * (C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ))), fun t ht => ?_⟩
  have hpos : 0 < (arg z shift t).im :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (harg_im_half t ht)
  have hφle : ‖φ₀'' (arg z shift t)‖ ≤ C₀ * rexp (-π) :=
    norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos)
      (hC₀ := hC₀) (z := ⟨arg z shift t, hpos⟩) (harg_im_half t ht)
  have hpow : ‖(z t + shift) ^ (2 : ℕ)‖ ≤ (3 : ℝ) ^ (2 : ℕ) := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((norm_add_le _ _).trans <| by linarith [hnorm t, hshift]) 2
  calc ‖hf z shift prefactor t‖
      = ‖prefactor‖ * (‖φ₀'' (arg z shift t)‖ * ‖(z t + shift) ^ (2 : ℕ)‖) := by simp [hf]
    _ ≤ ‖prefactor‖ * ((C₀ * rexp (-π)) * ((3 : ℝ) ^ (2 : ℕ))) := by gcongr
    _ = ‖prefactor‖ * (C₀ * rexp (-π) * ((3 : ℝ) ^ (2 : ℕ))) := by ring

/-- Smoothness of the integral `f` expressed via `DifferentiationUnderIntegral.g`
with kernel `coeff z` and integrand `hf z shift prefactor`. -/
public theorem contDiff_of_eq_integral_g_Ioo {z : ℝ → ℂ} {shift prefactor : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ, f x = ∫ t in Ioo (0 : ℝ) 1,
        DifferentiationUnderIntegral.g (coeff := coeff z) (hf := hf z shift prefactor) x t)
    (hz : Continuous z)
    (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (hshift : ‖shift‖ ≤ 1)
    (hden : ∀ t, t ∈ Ioo (0 : ℝ) 1 → z t + shift ≠ 0)
    (harg_im_pos : ∀ t, t ∈ Ioo (0 : ℝ) 1 → 0 < (arg z shift t).im)
    (harg_im_half : ∀ t, t ∈ Ioo (0 : ℝ) 1 → (1 / 2 : ℝ) < (arg z shift t).im) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  simpa [funext hfEq] using
    (DifferentiationUnderIntegral.contDiff_integral_g_Ioo
      (coeff := coeff z) (hf := hf z shift prefactor)
      (continuousOn_hf shift prefactor hz hden harg_im_pos)
      (continuous_coeff hz)
      (exists_bound_norm_hf shift prefactor hnorm hshift harg_im_half)
      (coeff_norm_le hnorm))

end MagicFunction.a.Schwartz.SmoothI24Common

namespace MagicFunction.a.Schwartz.I1Smooth

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma arg_z₁'_eq_I_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg z₁' (1 : ℂ) t = I / t := by
  have htne : (t : ℂ) ≠ 0 := mod_cast ht.1.ne'
  change (-1 : ℂ) / (z₁' t + 1) = I / t
  rw [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)]
  field_simp; ring_nf; simp [Complex.I_sq]

/-- Smoothness of `RealIntegrals.I₁'` as a function `ℝ → ℂ`. -/
public theorem I₁'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₁' :=
  contDiff_of_eq_integral_g_Ioo (z := z₁') (shift := (1 : ℂ)) (prefactor := I)
    (f := I₁') (fun x => by
      simp [RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁_def,
        DifferentiationUnderIntegral.g, Φ₁', coeff, hf, SmoothI24Common.arg,
        intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
        mul_assoc, mul_left_comm, mul_comm])
    continuous_z₁' norm_z₁'_le_two (by norm_num)
    (fun t ht h0 => by
      have h1 := congrArg Complex.im h0
      simp [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)] at h1; exact ht.1.ne' h1)
    (fun t ht => by simpa [arg_z₁'_eq_I_div (t := t) ht] using one_div_pos.2 ht.1)
    (fun t ht => by linarith [(one_lt_one_div ht.1) ht.2,
      show (arg z₁' (1 : ℂ) t).im = 1 / t from by simp [arg_z₁'_eq_I_div (t := t) ht]])

end MagicFunction.a.Schwartz.I1Smooth

namespace MagicFunction.a.Schwartz.I2Smooth

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma arg_z₂'_im_eq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (arg z₂' (1 : ℂ) t).im = 1 / (t ^ 2 + 1) := by
  have harg : arg z₂' (1 : ℂ) t = (-1 : ℂ) / ((t : ℂ) + I) := by
    change (-1 : ℂ) / (z₂' t + 1) = (-1 : ℂ) / ((t : ℂ) + I)
    simpa [add_left_comm, add_comm, add_assoc] using
      congrArg (fun z : ℂ => (-1 : ℂ) / (z + 1)) (z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))
  simpa [harg] using im_neg_one_div_ofReal_add_I (t := t)

/-- Smoothness of `RealIntegrals.I₂'` as a function `ℝ → ℂ`. -/
public theorem I₂'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₂' :=
  contDiff_of_eq_integral_g_Ioo (z := z₂') (shift := (1 : ℂ)) (prefactor := (1 : ℂ))
    (f := I₂') (fun x => by
      simp [RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂_def,
        DifferentiationUnderIntegral.g, Φ₂', Φ₁', coeff, hf, SmoothI24Common.arg,
        intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
        mul_assoc, mul_left_comm, mul_comm])
    continuous_z₂' norm_z₂'_le_two (by norm_num)
    (fun t ht h0 => by
      simpa [z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht), add_left_comm, add_comm] using
        congrArg Complex.im h0)
    (fun t ht => by rw [arg_z₂'_im_eq t ht]; positivity)
    (fun t ht => by
      simpa [arg_z₂'_im_eq (t := t) ht] using one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)

end MagicFunction.a.Schwartz.I2Smooth

namespace MagicFunction.a.Schwartz.I4Smooth

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations
open MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands
open MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma arg_z₄'_im_eq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (arg z₄' (-1 : ℂ) t).im = 1 / (t ^ 2 + 1) := by
  have harg : arg z₄' (-1 : ℂ) t = (-1 : ℂ) / ((-t : ℂ) + I) := by
    change (-1 : ℂ) / (z₄' t + (-1 : ℂ)) = (-1 : ℂ) / ((-t : ℂ) + I)
    simpa [sub_eq_add_neg, add_left_comm, add_comm, add_assoc] using
      congrArg (fun z : ℂ => (-1 : ℂ) / (z - 1)) (z₄'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht))
  simpa [harg] using im_neg_one_div_neg_ofReal_add_I (t := t)

/-- Smoothness of `RealIntegrals.I₄'` as a function `ℝ → ℂ`. -/
public theorem I₄'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₄' :=
  contDiff_of_eq_integral_g_Ioo (z := z₄') (shift := (-1 : ℂ)) (prefactor := (-1 : ℂ))
    (f := I₄') (fun x => by
      simp [RealIntegrals.I₄', MagicFunction.a.RealIntegrands.Φ₄_def,
        DifferentiationUnderIntegral.g, Φ₄', Φ₃', coeff, hf, SmoothI24Common.arg, sub_eq_add_neg,
        intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
        mul_assoc, mul_left_comm, mul_comm])
    continuous_z₄' norm_z₄'_le_two (by norm_num)
    (fun t ht h0 => by
      simpa [z₄'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht), sub_eq_add_neg,
        add_left_comm, add_comm, add_assoc] using congrArg Complex.im h0)
    (fun t ht => by rw [arg_z₄'_im_eq t ht]; positivity)
    (fun t ht => by
      simpa [arg_z₄'_im_eq (t := t) ht] using one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ht)

end MagicFunction.a.Schwartz.I4Smooth

namespace MagicFunction.a.SchwartzProperties

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
open Set Complex Real MeasureTheory

public theorem I₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₁' :=
  MagicFunction.a.Schwartz.I1Smooth.I₁'_contDiff

public theorem I₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₂' :=
  MagicFunction.a.Schwartz.I2Smooth.I₂'_contDiff

private lemma I₃'_eq_exp_mul_I₁' :
    RealIntegrals.I₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.I₁' x := by
  ext x; rw [I₃'_eq, I₁'_eq, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => by
    rw [show cexp (↑π * I * ↑x) = cexp (2 * ↑π * I * ↑x) * cexp (-↑π * I * ↑x) by
      rw [← Complex.exp_add]; ring_nf]; ring

public theorem I₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₃' :=
  I₃'_eq_exp_mul_I₁' ▸ (contDiff_const.mul ofRealCLM.contDiff).cexp.mul I₁'_smooth'

public theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' :=
  MagicFunction.a.Schwartz.I4Smooth.I₄'_contDiff

private lemma I₅'_eq_mul_exp_mul_I₁' :
    RealIntegrals.I₅' = fun x : ℝ ↦ (-2 : ℂ) * cexp (π * I * x) * RealIntegrals.I₁' x := by
  ext x; let f : ℝ → ℂ := fun t => (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)
  rw [show RealIntegrals.I₁' x = (∫ t in (0 : ℝ)..1, f t) * cexp (-π * I * x) by
    rw [show RealIntegrals.I₁' x = ∫ t in (0 : ℝ)..1, f t * cexp (-π * I * x) by
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using (I₁'_eq (r := x))]
    simp [intervalIntegral.integral_mul_const],
    show RealIntegrals.I₅' x = (-2 : ℂ) * ∫ t in (0 : ℝ)..1, f t by
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using (I₅'_eq (r := x))]
  linear_combination (2 * ∫ t in (0 : ℝ)..1, f t) *
    (by simp [← Complex.exp_add] : cexp (π * I * x) * cexp (-π * I * x) = 1)

public theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := I₅'_eq_mul_exp_mul_I₁' ▸
  (contDiff_const.mul (contDiff_const.mul ofRealCLM.contDiff).cexp).mul I₁'_smooth'

namespace MagicFunction.a.Schwartz.I6Smooth

open scoped Topology
open Complex Real Set MeasureTheory Filter
open MagicFunction.a.RealIntegrals MagicFunction.a.IntegralEstimates.I₆ RadialSchwartz

local notation "μ" => SpherePacking.Integration.μIciOne

/-- The coefficient capturing the `r`-dependence of the exponential factor. -/
private def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

private def gN (n : ℕ) (r t : ℝ) : ℂ := (coeff t) ^ n * g r t

private lemma gN_measurable (n : ℕ) (r : ℝ) : AEStronglyMeasurable (gN n r) μ := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ici
  simpa [gN] using
    (show Continuous fun t : ℝ ↦ (coeff t) ^ n by unfold coeff; fun_prop).continuousOn.mul
      ((MagicFunction.a.RealIntegrands.Φ₆_contDiffOn (r := r)).continuousOn.congr fun t ht ↦ by
        dsimp [MagicFunction.a.RealIntegrands.Φ₆, MagicFunction.a.ComplexIntegrands.Φ₆', g]
        rw [MagicFunction.Parametrisations.z₆'_eq_of_mem ht, show (π : ℂ) * I * (r : ℂ) *
          (I * (t : ℂ)) = (-π : ℂ) * (r : ℂ) * (t : ℂ) by ring_nf; simp [I_sq]]
        ac_rfl)

private lemma gN_integrable (n : ℕ) (r : ℝ) (hr : -2 < r) : Integrable (gN n r) μ := by
  obtain ⟨C₀, _, hC₀⟩ := g_norm_bound_uniform
  refine Integrable.mono' (g := fun t : ℝ ↦ (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀)
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using
      (show Integrable (fun t : ℝ ↦ t ^ n * rexp (-(π * (r + 2)) * t)) μ by
        simpa [IntegrableOn, SpherePacking.Integration.μIciOne] using
          SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := π * (r + 2))
            (mul_pos Real.pi_pos (by linarith))).const_mul ((π ^ n) * C₀))
    (gN_measurable n r) <| (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  calc ‖gN n r t‖ = ‖coeff t‖ ^ n * ‖g r t‖ := by simp [gN, norm_pow]
    _ ≤ (π * t) ^ n * (C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) := by
          gcongr ?_ * ?_
          · simp [coeff, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht0]
          · exact hC₀ r t ht
    _ = (π ^ n) * (t ^ n * rexp (-(π * (r + 2)) * t)) * C₀ := by
          rw [show rexp (-(π * (r + 2)) * t) = rexp (-2 * π * t) * rexp (-π * r * t) by
            rw [← Real.exp_add]; ring_nf]; ring

/-- The `hf` specialising `SmoothIntegralIciOne.gN` to the a-side `gN`. -/
private abbrev hφ : ℝ → ℂ := fun t : ℝ ↦ φ₀'' (I * t)

private lemma gN_eq_sharedGN (n : ℕ) (r t : ℝ) :
    gN n r t = SpherePacking.Integration.SmoothIntegralIciOne.gN (hf := hφ) n r t := by
  simp [gN, coeff, SpherePacking.Integration.SmoothIntegralIciOne.gN,
    SpherePacking.Integration.SmoothIntegralIciOne.g,
    SpherePacking.Integration.SmoothIntegralIciOne.coeff,
    MagicFunction.a.IntegralEstimates.I₆.g, hφ, mul_assoc, mul_left_comm, mul_comm]

private theorem I₆'_contDiffOn_Ioi_neg2 :
    ContDiffOn ℝ ∞ MagicFunction.a.RealIntegrals.I₆' (Ioi (-2 : ℝ)) := by
  obtain ⟨C₀, _, hC₀⟩ := MagicFunction.a.IntegralEstimates.I₆.g_norm_bound_uniform
  have hF0 : ContDiffOn ℝ ∞ (fun r => ∫ t in Ici (1 : ℝ), gN 0 r t) (Ioi (-2 : ℝ)) :=
    SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt
      (F := fun n r => ∫ t in Ici (1 : ℝ), gN n r t) (s := Ioi (-2 : ℝ))
      isOpen_Ioi (fun n r₀ hr₀ => by
        convert SpherePacking.Integration.SmoothIntegralIciOne.hasDerivAt_integral_gN
          (hf := hφ) (shift := (2 : ℝ))
          (exists_bound_norm_hf := ⟨C₀, fun t ht ↦ by
            simpa [MagicFunction.a.IntegralEstimates.I₆.g, hφ, mul_assoc, mul_comm,
              show rexp (-2 * π * t) * rexp (-π * 0 * t) = rexp (-(π * 2) * t) by
                rw [← Real.exp_add]; ring_nf] using hC₀ 0 t (by simpa using ht)⟩)
          (gN_measurable := fun n x =>
            (aestronglyMeasurable_congr (.of_forall (gN_eq_sharedGN n x))).mp (gN_measurable n x))
          (n := n) (x := r₀) hr₀
          (hF_int :=
            (integrable_congr (.of_forall (gN_eq_sharedGN n r₀))).mp
              (gN_integrable n r₀ hr₀)) using 1
        · exact funext fun r => integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <|
            .of_forall fun t _ ↦ gN_eq_sharedGN n r t)
        · exact integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <|
            .of_forall fun t _ ↦ gN_eq_sharedGN (n + 1) r₀ t)) 0
  refine ((contDiff_const (c := (2 : ℂ))).contDiffOn.mul hF0).congr fun r _ ↦ ?_
  simpa [gN, coeff] using MagicFunction.a.IntegralEstimates.I₆.I₆'_eq_integral_g_Ioo (r := r)

/-- Smoothness of the cutoff radial profile `r ↦ cutoffC r * RealIntegrals.I₆' r`. -/
public theorem cutoffC_mul_I₆'_contDiff :
    ContDiff ℝ ∞ (fun r : ℝ ↦ cutoffC r * RealIntegrals.I₆' r) :=
  contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 <| I₆'_contDiffOn_Ioi_neg2.mono fun x hx => by
    simpa [Set.mem_Ioi] using lt_trans (by norm_num : (-2 : ℝ) < -1) hx

end MagicFunction.a.Schwartz.I6Smooth

public theorem I₆'_smooth' : ContDiff ℝ ∞ (fun r : ℝ ↦
    RadialSchwartz.cutoffC r * RealIntegrals.I₆' r) :=
  MagicFunction.a.Schwartz.I6Smooth.cutoffC_mul_I₆'_contDiff

public theorem I₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ ≤ C :=
  MagicFunction.a.Schwartz.I1Decay.decay'

public theorem I₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₂' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₂.decay'

public theorem I₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤ C := fun k n ↦ by
  let g3 : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * ((2 * π : ℂ) * I))
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left (f := g3)
    (g := RealIntegrals.I₁') (k := k) (n := n) (B := fun m ↦ (2 * π) ^ m)
    (ofRealCLM.contDiff.mul contDiff_const).cexp I₁'_smooth' (fun m x => by
      simpa [g3, mul_assoc, mul_left_comm, mul_comm, abs_of_nonneg Real.pi_pos.le] using
        SpherePacking.ForMathlib.norm_iteratedFDeriv_cexp_mul_ofReal_mul_I_le (a := 2 * π) m x)
    (I₁'_decay' (k := k))
  exact ⟨C, fun x hx => by simpa [I₃'_eq_exp_mul_I₁', g3, mul_comm, mul_left_comm] using hC x hx⟩

public theorem I₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₄.decay'

public theorem I₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₅' x‖ ≤ C := fun k n ↦ by
  let g5 : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * ((π : ℂ) * I))
  let f5 : ℝ → ℂ := fun x ↦ (-2 : ℂ) * g5 x
  have hg5_smooth : ContDiff ℝ ∞ g5 := (ofRealCLM.contDiff.mul contDiff_const).cexp
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left (f := f5)
    (g := RealIntegrals.I₁') (k := k) (n := n) (B := fun m ↦ 2 * π ^ m)
    (contDiff_const.mul hg5_smooth) I₁'_smooth' (fun m x => by
      rw [show iteratedFDeriv ℝ m f5 x = (-2 : ℂ) • iteratedFDeriv ℝ m g5 x by
        simpa [f5, smul_eq_mul] using iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := m)
          (a := (-2 : ℂ)) (f := g5) (hg5_smooth.contDiffAt.of_le (by exact_mod_cast le_top)),
        norm_smul, show ‖(-2 : ℂ)‖ = (2 : ℝ) from by simp]
      exact mul_le_mul_of_nonneg_left
        (SpherePacking.ForMathlib.norm_iteratedFDeriv_cexp_mul_pi_I_le m x) (by norm_num))
    (I₁'_decay' (k := k))
  exact ⟨C, fun x hx => by
    simpa [I₅'_eq_mul_exp_mul_I₁', f5, g5, mul_comm, mul_left_comm] using hC x hx⟩

public theorem I₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₆.decay'

end MagicFunction.a.SchwartzProperties

namespace MagicFunction.a.SchwartzIntegrals

open RadialSchwartz.Bridge MagicFunction.a.SchwartzProperties

/-- Schwartz function on `ℝ` from primed radial integral `I₁'`. -/
@[expose] public def I₁' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₁') I₁'_smooth' I₁'_decay'
@[expose] public def I₂' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₂') I₂'_smooth' I₂'_decay'
@[expose] public def I₃' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₃') I₃'_smooth' I₃'_decay'
@[expose] public def I₄' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₄') I₄'_smooth' I₄'_decay'
@[expose] public def I₅' : 𝓢(ℝ, ℂ) :=
  fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₅') I₅'_smooth' I₅'_decay'

/-- Schwartz function on `ℝ` from primed radial integral `I₆'` (cutoff variant). -/
@[expose] public def I₆' : 𝓢(ℝ, ℂ) where
  toFun := RadialSchwartz.Bridge.fCut MagicFunction.a.RealIntegrals.I₆'
  smooth' := by simpa [RadialSchwartz.Bridge.fCut] using I₆'_smooth'
  decay' := by
    simpa using RadialSchwartz.cutoffC_mul_decay_of_nonneg_of_contDiff
      (f := MagicFunction.a.RealIntegrals.I₆') (hg_smooth := I₆'_smooth') I₆'_decay'

public abbrev liftSchwartz (f : 𝓢(ℝ, ℂ)) : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) f

/-- Schwartz function on `EuclideanSpace ℝ (Fin 8)` from radial profile `I₁'`. -/
@[expose] public def I₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₁'
@[expose] public def I₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₂'
@[expose] public def I₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₃'
@[expose] public def I₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₄'
@[expose] public def I₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₅'
@[expose] public def I₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := liftSchwartz I₆'

@[simp] public lemma I₁'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₁' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₁' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₂'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₂' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₂' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₃'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₃' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₃' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₄'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₄' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₄' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₅'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₅' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₅' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma I₆'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₆' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₆' r := fCut_apply_of_nonneg _ hr

end MagicFunction.a.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

open SchwartzMap

/-- The radial profile of the `+1` Fourier eigenfunction `a`. -/
@[expose] public def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.a.SchwartzIntegrals.I₁'
  + MagicFunction.a.SchwartzIntegrals.I₂'
  + MagicFunction.a.SchwartzIntegrals.I₃'
  + MagicFunction.a.SchwartzIntegrals.I₄'
  + MagicFunction.a.SchwartzIntegrals.I₅'
  + MagicFunction.a.SchwartzIntegrals.I₆'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[expose] public def a : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) a'

/-- Expand `a` as the sum of the six defining integrals from `MagicFunction.a.RadialFunctions`. -/
public theorem a_eq_sum_integrals_RadialFunctions :
    a = MagicFunction.a.RadialFunctions.I₁ + MagicFunction.a.RadialFunctions.I₂
      + MagicFunction.a.RadialFunctions.I₃ + MagicFunction.a.RadialFunctions.I₄
      + MagicFunction.a.RadialFunctions.I₅ + MagicFunction.a.RadialFunctions.I₆ := by
  ext x
  open MagicFunction.a.RadialFunctions in
  simp [a, a', I₁, I₂, I₃, I₄, I₅, I₆, sq_nonneg ‖x‖, add_assoc]

end MagicFunction.FourierEigenfunctions

end

/-!
# The special value `a 0`

This section proves the explicit special value of the magic function at the origin,
`a 0 = -8640 * I / π` (blueprint Proposition `prop:a0`).

## Main statements
* `φ₀_finite_difference`
* `φ₀''_add_one`
* `a_zero`
-/

namespace MagicFunction.a.SpecialValues

noncomputable section

open Real Complex UpperHalfPlane ModularGroup
open MagicFunction.FourierEigenfunctions RealIntegrals MagicFunction.a.RadialFunctions
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Zero

/-- A second-order finite difference identity for `φ₀` obtained from its modular transformation
under `S`, together with periodicity. -/
public theorem φ₀_finite_difference (z : ℍ) :
    φ₀ (S • ((1 : ℝ) +ᵥ z)) * (((1 : ℝ) +ᵥ z : ℍ) : ℂ) ^ (2 : ℕ)
      - 2 * (φ₀ (S • z) * (z : ℂ) ^ (2 : ℕ))
      + φ₀ (S • ((-1 : ℝ) +ᵥ z)) * (((-1 : ℝ) +ᵥ z : ℍ) : ℂ) ^ (2 : ℕ)
      = 2 * φ₀ z := by
  rw [φ₀_S_transform_mul_sq ((1 : ℝ) +ᵥ z), φ₀_S_transform_mul_sq z,
    φ₀_S_transform_mul_sq ((-1 : ℝ) +ᵥ z)]
  simp [φ₀_periodic, φ₂'_periodic, φ₄'_periodic, φ₀_periodic_neg_one, φ₂'_periodic_neg_one,
    φ₄'_periodic_neg_one, pow_two]; ring_nf

/-! ## Evaluating `a(0)` via the strip contour. -/

section StripContour

open scoped Real Topology Interval BigOperators ArithmeticFunction.sigma
open Filter intervalIntegral

def zI (x : ℝ) : ℂ := (x : ℂ) + Complex.I

@[simp] lemma zI_im (x : ℝ) : (zI x).im = 1 := by simp [zI]

def F (z : ℂ) : ℂ := φ₀'' (-1 / z) * z ^ (2 : ℕ)

private lemma integral_neg_x_add_I_eq_integral_F_zI_sub_one :
    (∫ x in (0 : ℝ)..1,
        φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
      ∫ x in (0 : ℝ)..1, F (zI x - 1) := by
  have hrew : (fun x : ℝ =>
        φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
      fun x : ℝ => F (zI (1 - x) - 1) :=
    funext fun x => by simp [F, zI, sub_eq_add_neg, add_assoc, add_comm]
  simpa [hrew] using intervalIntegral.integral_comp_sub_left
    (f := fun x : ℝ => F (zI x - 1)) (a := (0 : ℝ)) (b := (1 : ℝ)) (d := (1 : ℝ))

lemma I₄'_zero :
    I₄' (0 : ℝ) = -∫ x in (0 : ℝ)..1, F (zI x - 1) := by
  rw [show I₄' (0 : ℝ) = ∫ x in (0 : ℝ)..1, (-1 : ℂ) *
      (φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) from by
    simp [MagicFunction.a.RadialFunctions.I₄'_eq, pow_two],
    intervalIntegral.integral_const_mul, integral_neg_x_add_I_eq_integral_F_zI_sub_one]; ring

lemma φ₂''_def (z : ℂ) (hz : 0 < z.im) : φ₂'' z = φ₂' ⟨z, hz⟩ := by simp [φ₂'', hz]
lemma φ₄''_def (z : ℂ) (hz : 0 < z.im) : φ₄'' z = φ₄' ⟨z, hz⟩ := by simp [φ₄'', hz]

lemma F_eq_phi0_phi2_phi4 (z : ℂ) (hz : 0 < z.im) :
    F z =
      φ₀'' z * (z : ℂ) ^ (2 : ℕ) - (12 * Complex.I) / π * (z : ℂ) * φ₂'' z -
        36 / (π ^ 2) * φ₄'' z := by
  let zH : ℍ := ⟨z, hz⟩
  have hφ₀S : φ₀ (ModularGroup.S • zH) = φ₀'' (-1 / z) := by
    rw [← (φ₀''_coe_upperHalfPlane (ModularGroup.S • zH)),
      show ((ModularGroup.S • zH : ℍ) : ℂ) = -1 / (z : ℂ) by
        simpa [zH] using (ModularGroup.coe_S_smul (z := zH))]
  have h' := φ₀_S_transform_mul_sq zH
  rw [hφ₀S] at h'
  simpa [F, zH, φ₀''_def (z := z) hz, φ₂'', φ₄'', hz] using h'

private lemma vadd_neg_one_eq (z : ℂ) (hz : 0 < z.im) (hz1 : 0 < (z - 1).im) :
    ((-1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) : ℍ) = ⟨z - 1, hz1⟩ := by ext1; simp [sub_eq_add_neg, add_comm]

lemma F_sub_one (z : ℂ) (hz : 0 < z.im) :
    F z - F (z - 1) =
      φ₀'' z * ((2 : ℂ) * z - 1) - (12 * Complex.I) / π * φ₂'' z := by
  have hzm : 0 < (z - 1).im := by simpa using hz
  have hvadd := vadd_neg_one_eq z hz hzm
  have hφ₀ : φ₀'' (z - 1) = φ₀'' z := by
    rw [φ₀''_def (z := z - 1) hzm, φ₀''_def (z := z) hz, ← hvadd, φ₀_periodic_neg_one]
  have hφ₂ : φ₂'' (z - 1) = φ₂'' z := by
    rw [φ₂''_def (z := z - 1) hzm, φ₂''_def (z := z) hz, ← hvadd, φ₂'_periodic_neg_one]
  have hφ₄ : φ₄'' (z - 1) = φ₄'' z := by
    rw [φ₄''_def (z := z - 1) hzm, φ₄''_def (z := z) hz, ← hvadd, φ₄'_periodic_neg_one]
  simp [F_eq_phi0_phi2_phi4 (z := z) hz, F_eq_phi0_phi2_phi4 (z := z - 1) hzm,
    hφ₀, hφ₂, hφ₄, pow_two]
  ring_nf

lemma I₂'_zero_add_I₄'_zero_eq_integral_phi0_phi2 :
    IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 →
    IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 →
    I₂' (0 : ℝ) + I₄' 0 =
      ∫ x in (0 : ℝ)..1,
        (φ₀'' (zI x) * ((2 : ℂ) * (zI x) - 1) - (12 * Complex.I) / π * φ₂'' (zI x))
          ∂MeasureTheory.volume := fun hF hG => by
  have hI2 : I₂' (0 : ℝ) = ∫ x in (0 : ℝ)..1, F (zI x) := by
    simp [F, zI, MagicFunction.a.RadialFunctions.I₂'_eq]
  rw [show I₂' (0 : ℝ) + I₄' 0 =
      ∫ x in (0 : ℝ)..1, (F (zI x) - F (zI x - 1)) ∂MeasureTheory.volume from by
    simpa [hI2, I₄'_zero, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) hF hG).symm]
  exact intervalIntegral.integral_congr (μ := MeasureTheory.volume) fun x _ => by
    simpa [zI] using F_sub_one (z := zI x) (by simp [zI])

def f0 (z : ℂ) : ℂ := φ₀'' z * ((2 : ℂ) * z - 1)

lemma f0_differentiableOn : DifferentiableOn ℂ f0 {z : ℂ | 0 < z.im} := by
  simpa [f0] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.mul
    (by fun_prop : Differentiable ℂ fun z : ℂ => (2:ℂ) * z - 1).differentiableOn
lemma f0_continuousOn : ContinuousOn f0 {z : ℂ | 0 < z.im} := f0_differentiableOn.continuousOn

lemma f0_norm_bound_on_strip :
    ∃ C₀ > 0, ∀ {z : ℂ}, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
      ‖f0 z‖ ≤ C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun {z} hzIm hzRe0 hzRe1 => ?_⟩
  have hzIm_pos : 0 < z.im := lt_of_lt_of_le (by norm_num) hzIm
  have hφ : ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := by
    simpa [UpperHalfPlane.im, φ₀''_def (z := z) hzIm_pos] using hC₀ ⟨z, hzIm_pos⟩
      (by simpa [UpperHalfPlane.im] using lt_of_lt_of_le (by norm_num) hzIm)
  have hnorm : ‖(2 : ℂ) * z - 1‖ ≤ 2 * z.im + 1 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [show ((2:ℂ) * z - 1).re = 2 * z.re - 1 by simp,
      show ((2:ℂ) * z - 1).im = 2 * z.im by simp,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * z.im)]
    linarith [abs_le.2 (⟨by linarith, by linarith⟩ : -1 ≤ 2 * z.re - 1 ∧ 2 * z.re - 1 ≤ 1)]
  simpa [f0, mul_comm, mul_left_comm, mul_assoc] using
    (norm_mul_le _ _).trans (mul_le_mul hφ hnorm (norm_nonneg _) (by positivity))

private lemma vadd_one_eq (z : ℂ) (hz : 0 < z.im) (hz1 : 0 < (z + 1).im) :
    ((1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) : ℍ) = ⟨z + 1, hz1⟩ := by ext1; simp [add_comm]

/-- Periodicity of `φ₀''` under translation by `1`. -/
public lemma φ₀''_add_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z + 1) = φ₀'' z := by
  rw [φ₀''_def (z := z + 1) (by simpa using hz), φ₀''_def (z := z) hz,
    ← vadd_one_eq z hz (by simpa using hz), φ₀_periodic]

private lemma strip_uIcc_subset {m : ℝ} (hm : 1 ≤ m) :
    (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) ⊆ {z : ℂ | 0 < z.im} := fun _ hz =>
  lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (Set.uIcc_of_le hm ▸ (mem_reProdIm.1 hz).2).1

private lemma strip_Ioo_subset {m : ℝ} :
    (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) ⊆ {z : ℂ | 0 < z.im} :=
  fun _ hz => lt_trans (by norm_num) (mem_reProdIm.1 hz).2.1

lemma rect_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I)) = 0 := by
  simpa using Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (f := f0) (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I)
    (Hc := by simpa using f0_continuousOn.mono (strip_uIcc_subset hm))
    (Hd := by simpa [hm] using f0_differentiableOn.mono strip_Ioo_subset)

lemma integrableOn_phi0_imag :
    MeasureTheory.IntegrableOn (fun t : ℝ => φ₀'' ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨C₀, _, hC₀⟩
  refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => C₀ * Real.exp (-2 * π * t))
    (by simpa [MeasureTheory.IntegrableOn, mul_assoc] using
      (exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := (2 * Real.pi))
        (by positivity)).integrable.const_mul C₀)
    (((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
      (continuous_ofReal.mul continuous_const).continuousOn fun t ht => by
        simpa [mul_assoc] using
          (lt_of_lt_of_le (by norm_num) ht.le : (0:ℝ) < t)).aestronglyMeasurable measurableSet_Ioi)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa [mul_assoc] using lt_of_lt_of_le (by norm_num) ht.le⟩
  simpa [zH, UpperHalfPlane.im] using (show ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * zH.im) by
    simpa [φ₀''_coe_upperHalfPlane] using hC₀ zH
      (by simpa [zH, UpperHalfPlane.im] using lt_of_lt_of_le (by norm_num) ht.le))

private lemma norm_integral_f0_strip_le {C₀ : ℝ}
    (hC₀ : ∀ {z : ℂ}, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
              ‖f0 z‖ ≤ C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im)) :
    ∀ᶠ m : ℝ in atTop,
      ‖∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)‖ ≤
        C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (1 : ℝ)) fun x hx => by
      simpa using hC₀ (z := (x + m * Complex.I : ℂ)) (by simpa using hm)
        (by simpa using le_of_lt (by simpa using hx.1)) (by simpa using hx.2)

private lemma tendsto_two_m_plus_one_mul_exp_decay (C₀ : ℝ) :
    Tendsto (fun m : ℝ => C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m)) atTop (𝓝 (0 : ℝ)) := by
  have hmul : Tendsto (fun m : ℝ => m * Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by
    simpa [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (s := (1 : ℝ)) (b := (2 * Real.pi)) (by positivity)
  have hu : Tendsto (fun m : ℝ => (2 * Real.pi) * m) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hexp : Tendsto (fun m : ℝ => Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by simpa
  have hmain : Tendsto (fun m : ℝ => (2 * m + 1) * Real.exp (-2 * Real.pi * m))
      atTop (𝓝 (0 : ℝ)) := by
    have := (hmul.const_mul 2).add hexp
    simpa using this.congr' (Eventually.of_forall fun m => by ring_nf)
  simpa [mul_assoc] using hmain.const_mul C₀

private lemma intervalIntegrable_f0_vert {m : ℝ} (hm : 1 ≤ m) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => f0 ((x : ℝ) + y * Complex.I)) MeasureTheory.volume 1 m := by
  simpa using (f0_continuousOn.comp
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn)
    (fun y hy => by
      simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        ((Set.uIcc_of_le hm ▸ hy).1))).intervalIntegrable

lemma strip_identity_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I) := by
  have hVertTerm : Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I)) =
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) := by
    rw [← smul_sub,
      (integral_sub (intervalIntegrable_f0_vert hm 1) (intervalIntegrable_f0_vert hm 0)).symm]
    exact congrArg (Complex.I • ·) <|
      intervalIntegral.integral_congr (μ := MeasureTheory.volume) fun y hy => by
        have hy_pos : (0 : ℝ) < y :=
          lt_of_lt_of_le (by norm_num) ((Set.uIcc_of_le hm ▸ hy).1)
        have : f0 ((1 : ℂ) + (y : ℂ) * Complex.I) - f0 ((y : ℂ) * Complex.I) =
            (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) := by
          simp [f0, show φ₀'' ((1 : ℂ) + (y : ℂ) * Complex.I) = φ₀'' ((y : ℂ) * Complex.I) from by
            simpa [add_assoc, add_comm, add_left_comm] using φ₀''_add_one ((y : ℂ) * Complex.I)
              (by simpa [mul_assoc] using hy_pos)]
          ring
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  linear_combination rect_f0 m hm - hVertTerm

private lemma I6_zero_eq_I_smul_integral :
    I₆' (0 : ℝ) =
      Complex.I • (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
        ∂MeasureTheory.volume) := by
  rw [show I₆' (0 : ℝ) = 2 * ∫ t in Set.Ici (1 : ℝ),
      (Complex.I : ℂ) * φ₀'' ((t : ℂ) * Complex.I) ∂MeasureTheory.volume from by
    simp [MagicFunction.a.RadialFunctions.I₆'_eq (r := (0 : ℝ)), mul_comm],
    MeasureTheory.integral_Ici_eq_integral_Ioi]
  simp only [smul_eq_mul, MeasureTheory.integral_const_mul]; ring

lemma integral_f0_height_one_eq_neg_I6 :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) = -I₆' (0 : ℝ) := by
  set J : ℂ := ∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) ∂MeasureTheory.volume
  set bottom : ℂ := ∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)
  have hVert := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := MeasureTheory.volume)
    (f := fun y : ℝ => (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) (a := (1 : ℝ))
    (hfi := by simpa [MeasureTheory.IntegrableOn] using
      integrableOn_phi0_imag.const_mul (2 : ℂ)) (hb := tendsto_id)
  have hA0 : bottom + Complex.I • J = 0 := by
    obtain ⟨C₀, _, hC₀⟩ := f0_norm_bound_on_strip
    exact tendsto_nhds_unique
      ((tendsto_const_nhds.add (tendsto_const_nhds.smul hVert)).congr' <| by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm using strip_identity_f0 m hm)
      (squeeze_zero_norm' (norm_integral_f0_strip_le hC₀)
        (tendsto_two_m_plus_one_mul_exp_decay C₀))
  rw [I6_zero_eq_I_smul_integral]; linear_combination hA0

lemma rect_phi2 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + (1 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((0 : ℝ) + y * Complex.I)) = 0 := by
  simpa using
    (Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (f := φ₂'') (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I)
      (Hc := by
        simpa using MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn.mono
          (strip_uIcc_subset hm))
      (Hd := by
        simpa [hm] using
          (MagicFunction.a.ComplexIntegrands.φ₂''_holo :
              DifferentiableOn ℂ φ₂'' {z : ℂ | 0 < z.im}).mono strip_Ioo_subset))

lemma strip_identity_phi2 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + (1 : ℝ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I) := by
  have hVert : ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((1 : ℝ) + y * Complex.I) =
      ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((0 : ℝ) + y * Complex.I) :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) fun y hy => by
      have hyim : (0 : ℝ) < ((y : ℂ) * Complex.I).im := by
        simpa [mul_assoc] using
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((Set.uIcc_of_le hm ▸ hy).1)
      simpa [add_assoc, add_comm, add_left_comm, mul_assoc,
        φ₂''_def (z := (y : ℂ) * Complex.I + 1) (by simpa using hyim),
        φ₂''_def (z := (y : ℂ) * Complex.I) hyim,
        ← vadd_one_eq ((y : ℂ) * Complex.I) hyim (by simpa using hyim)] using
          φ₂'_periodic ((⟨(y : ℂ) * Complex.I, hyim⟩ : ℍ))
  have hrect := rect_phi2 m hm; grind only

private lemma tsum_pnat_div_q_eq_nat_tsum (z : ℍ) (a : ℕ → ℂ)
    (hrel : ∀ n : ℕ, a n = (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))) :
    (∑' (n : ℕ+),
        ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
          cexp (2 * π * Complex.I * (z : ℂ))) =
      ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
  rw [show (∑' (n : ℕ+),
        ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
          cexp (2 * π * Complex.I * (z : ℂ))) =
      ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
            cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) /
          cexp (2 * π * Complex.I * (z : ℂ)) from by
    simpa using tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
      ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
        cexp (2 * π * Complex.I * (z : ℂ)))]
  refine tsum_congr fun n => ?_
  rw [show cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) =
      cexp (2 * π * Complex.I * (z : ℂ)) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) from by
    rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring,
      mul_add, mul_one, Complex.exp_add]; ring, hrel]
  field_simp

lemma tendsto_A_div_q :
    Tendsto (fun z : ℍ =>
        ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z))
      atImInfty (𝓝 (720 : ℂ)) := by
  let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))
  have hsigma : ∀ n : ℕ, (σ 3 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 4 := fun n => by
    exact_mod_cast sigma_bound 3 (n + 1)
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
      (by simpa using MagicFunction.PolyFourierCoeffBound.summable_pow_shift_mul_exp (4 + 1) 1)
    have hnorm : ‖a n‖ ≤ (n + 1 : ℝ) ^ (4 + 1) := calc
      ‖a n‖ = (n + 1 : ℝ) * (σ 3 (n + 1) : ℝ) := by
              simp only [a, Complex.norm_mul, Complex.norm_natCast]; push_cast; ring
      _ ≤ (n + 1 : ℝ) * (n + 1 : ℝ) ^ 4 := by gcongr; exact hsigma n
      _ = (n + 1 : ℝ) ^ (4 + 1) := by ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right hnorm (by positivity : (0 : ℝ) ≤ Real.exp (-2 * Real.pi * n)))
  refine (tendsto_congr (f₂ := fun z : ℍ =>
    (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n)) fun z => ?_).mpr ?_
  · rw [show (E₂ z) * (E₄ z) - (E₆ z) = (720 : ℂ) *
        ∑' (n : ℕ+), (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) from by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ z),
      mul_div_assoc, ← tsum_div_const, tsum_pnat_div_q_eq_nat_tsum z a fun _ => rfl]
  simpa [a] using tendsto_const_nhds.mul (QExp.tendsto_nat (a := a) (ha := ha))

private lemma tendsto_A_over_Delta :
    Tendsto (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z))
      atImInfty (𝓝 (720 : ℂ)) := by
  have hrew : (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)) =
      fun z : ℍ => (((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z)) /
        ((Δ z) / cexp (2 * π * Complex.I * z)) :=
    funext fun z => by
      field_simp [(by simp : (cexp (2 * π * Complex.I * z) : ℂ) ≠ 0), Δ_ne_zero z]
  have hΔrew : (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) =
      fun z : ℍ => ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 :=
    funext fun z => by simp [Δ, div_eq_mul_inv, mul_left_comm, mul_comm]
  have hΔ : Tendsto (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa [hΔrew] using (Delta_boundedfactor : Tendsto _ atImInfty (𝓝 (1 : ℂ)))
  rw [hrew]
  simpa using tendsto_A_div_q.div hΔ (by norm_num : (1 : ℂ) ≠ 0)

lemma tendsto_top_phi2 :
    Tendsto (fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) atTop (𝓝 (720 : ℂ)) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  rcases (UpperHalfPlane.atImInfty_mem _).1
    ((show Tendsto (fun z : ℍ => φ₂' z) atImInfty (𝓝 (720 : ℂ)) by
      simpa [φ₂', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using
        SpherePacking.ModularForms.tendsto_E₄_atImInfty.mul tendsto_A_over_Delta)
      (Metric.ball_mem_nhds (720 : ℂ) (half_pos hε))) with ⟨A, hA⟩
  refine ⟨max A 1, fun m hm => ?_⟩
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hm)
  have hII : IntervalIntegrable (fun x : ℝ => φ₂'' (x + m * Complex.I))
      MeasureTheory.volume 0 1 := by
    simpa using (MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn.comp
      (continuous_ofReal.add continuous_const).continuousOn
      (fun x _ => by simpa [Complex.add_im] using hm0)).intervalIntegrable
  have hsub : (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ) =
      ∫ x : ℝ in (0 : ℝ)..1, (φ₂'' (x + m * Complex.I) - (720 : ℂ)) := by
    simpa using (intervalIntegral.integral_sub (μ := MeasureTheory.volume) hII
      (intervalIntegrable_const (c := (720 : ℂ)))).symm
  have hbound : ∀ x ∈ Ι (0 : ℝ) 1,
      ‖φ₂'' (x + m * Complex.I) - (720 : ℂ)‖ ≤ ε / 2 := fun x _ => by
    let zH : ℍ := ⟨(x : ℂ) + (m : ℂ) * Complex.I, by simpa using hm0⟩
    simpa [zH, mul_assoc, show φ₂'' ((x : ℂ) + (m : ℂ) * Complex.I) = φ₂' zH from by
      simpa [zH] using (φ₂''_def (z := (x : ℂ) + (m : ℂ) * Complex.I) (by simpa using hm0))]
      using le_of_lt (hA zH (by simpa [zH, UpperHalfPlane.im, Complex.add_im] using
        ((le_max_left _ _).trans hm)))
  simpa [Metric.ball, dist_eq_norm] using lt_of_le_of_lt
    (show ‖(∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ)‖ ≤ ε / 2 by
      simpa [hsub] using
        intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) hbound)
    (half_lt_self hε)

private lemma intervalIntegrable_F_comp
    (w : ℝ → ℂ) (hw : ContinuousOn w (Set.uIcc (0 : ℝ) 1)) (hwim : ∀ x, 0 < (w x).im) :
    IntervalIntegrable (fun x : ℝ => F (w x)) MeasureTheory.volume (0 : ℝ) 1 := by
  have hwne : Set.MapsTo w (Set.uIcc (0 : ℝ) 1) ({0}ᶜ) := fun x _ h0 =>
    (ne_of_gt (hwim x)) (by simpa using congrArg Complex.im h0)
  have hinv : ContinuousOn (fun z : ℂ => (-1 : ℂ) / z) ({0}ᶜ) := by
    convert (continuousOn_const.mul (continuousOn_inv₀ (G₀ := ℂ)) :
      ContinuousOn ((fun _ : ℂ => (-1 : ℂ)) * (Inv.inv : ℂ → ℂ)) ({0}ᶜ)) using 1
  simpa [F] using ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
    (hinv.comp hw hwne) fun x _ => by
      simpa [div_eq_mul_inv] using UpperHalfPlane.im_inv_neg_coe_pos ⟨w x, hwim x⟩).mul
    (by simpa using hw.pow 2)).intervalIntegrable

private lemma intervalIntegrable_comp_zI {g : ℂ → ℂ} (hg : ContinuousOn g {z : ℂ | 0 < z.im}) :
    IntervalIntegrable (fun x : ℝ => g (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
  simpa using (hg.comp (continuous_ofReal.add continuous_const).continuousOn
    fun x _ => by simp).intervalIntegrable

private lemma hI246_eq :
    I₂' (0 : ℝ) + I₄' 0 + I₆' 0 = -8640 * Complex.I / π := by
  have hzI : IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [zI] using intervalIntegrable_F_comp (fun x : ℝ => zI x)
      (continuous_ofReal.add continuous_const).continuousOn fun x => by simp [zI]
  have hzIs : IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      intervalIntegrable_F_comp (fun x : ℝ => zI x - 1)
        ((continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
        fun x => by simp [zI]
  have hI24 := I₂'_zero_add_I₄'_zero_eq_integral_phi0_phi2 hzI hzIs
  have hIntf0 : IntervalIntegrable (fun x : ℝ => f0 (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [f0] using intervalIntegrable_comp_zI f0_continuousOn
  have hIntphi2 : IntervalIntegrable (fun x : ℝ => φ₂'' (zI x)) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_comp_zI MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn
  rw [show I₂' (0 : ℝ) + I₄' 0 =
      (∫ x : ℝ in (0 : ℝ)..1, (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x))) from by
    simpa [f0, zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_left_comm, mul_comm] using hI24,
    show (∫ x : ℝ in (0 : ℝ)..1, (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x))) =
        (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) -
          ∫ x : ℝ in (0 : ℝ)..1, (12 * Complex.I) / π * φ₂'' (zI x) from by
      simpa using (intervalIntegral.integral_sub (μ := MeasureTheory.volume)
        hIntf0 (hIntphi2.const_mul _)),
    show (∫ x : ℝ in (0 : ℝ)..1, (12 * Complex.I) / π * φ₂'' (zI x)) =
        ((12 : ℂ) * Complex.I) / π * (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) from by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm],
    show (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) = -I₆' (0 : ℝ) by
      simpa [zI] using integral_f0_height_one_eq_neg_I6,
    show (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) = (720 : ℂ) by
      simpa using tendsto_const_nhds_iff.mp (tendsto_top_phi2.congr' <| by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
        simpa [zI] using (strip_identity_phi2 m hm).symm)]
  field_simp; ring

end StripContour

/-- The special value at the origin: `a 0 = -8640 * I / π`. -/
public theorem a_zero :
    FourierEigenfunctions.a (0 : ℝ⁸) = -8640 * Complex.I / π := by
  have h135 : (I₁' (0 : ℝ) + I₃' 0 + I₅' 0 : ℂ) = 0 := by
    simp [I₁'_eq, I₃'_eq, I₅'_eq]; ring
  have h_red : FourierEigenfunctions.a (0 : ℝ⁸) =
      I₁' (0 : ℝ) + I₂' 0 + I₃' 0 + I₄' 0 + I₅' 0 + I₆' 0 := by
    simpa using congrArg (fun f : ℝ⁸ → ℂ => f (0 : ℝ⁸))
      FourierEigenfunctions.a_eq_sum_integrals_RadialFunctions
  linear_combination h_red + h135 + hI246_eq

end Zero

end

end MagicFunction.a.SpecialValues
