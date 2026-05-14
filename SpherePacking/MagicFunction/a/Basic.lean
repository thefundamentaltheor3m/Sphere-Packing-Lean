/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.ModularForms.FG.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import SpherePacking.ModularForms.Derivative

/-!
# Integral representation of the magic function `a`

Complex integrands and real reparametrizations for the scalar integrals `I₁'`, ..., `I₆'` and
their radial versions on `V = EuclideanSpace ℝ (Fin 8)`. Primed names take a scalar; unprimed
names are radial: `‖x‖^2 ↦ Iᵢ' (‖x‖^2)`.
-/

local notation "V" => EuclideanSpace ℝ (Fin 8)

open scoped UpperHalfPlane
open Set Complex Real MagicFunction.Parametrisations

noncomputable section

variable (r : ℝ)

namespace MagicFunction.a.ComplexIntegrands

/-- First complex integrand for `a`. -/
@[expose] public def Φ₁' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))

/-- A copy of `Φ₁'` used for uniform indexing. -/
@[expose] public def Φ₂' : ℂ → ℂ := Φ₁' r

/-- Third complex integrand for `a`. -/
@[expose] public def Φ₃' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))

/-- A copy of `Φ₃'` used for uniform indexing. -/
@[expose] public def Φ₄' : ℂ → ℂ := Φ₃' r

/-- Fifth complex integrand for `a`. -/
@[expose] public def Φ₅' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ))

/-- Sixth complex integrand for `a`. -/
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
