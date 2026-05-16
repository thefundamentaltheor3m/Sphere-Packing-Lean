module
public import SpherePacking.ModularForms.Derivative.Basic

@[expose] public section

/-!
# The Serre derivative

This file re-exports the Serre derivative `serre_D k F z = D F z - (k/12) · E₂(z) · F(z)` of
weight `k` and its basic algebraic properties (linearity, Leibniz rule, preservation of
MDifferentiability) from mathlib's `Mathlib.NumberTheory.ModularForms.Derivative`, and additionally
shows it preserves boundedness at imaginary infinity for bounded holomorphic inputs.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function
open scoped Derivative

/-- Serre derivative of weight `k` for functions `F : ℍ → ℂ`.
Re-exports mathlib's `Derivative.serreDerivative`. -/
@[expose] public noncomputable def serre_D : ℂ → (ℍ → ℂ) → (ℍ → ℂ) := Derivative.serreDerivative

@[simp]
lemma serre_D_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serre_D k F z = D F z - k * 12⁻¹ * E₂ z * F z := rfl

public lemma serre_D_eq (k : ℂ) (F : ℍ → ℂ) :
    serre_D k F = fun z => D F z - k * 12⁻¹ * E₂ z * F z := rfl

/-- Compatibility of `serre_D` with addition. -/
public theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F + G) = serre_D k F + serre_D k G :=
  Derivative.serreDerivative_add k F G hF hG

/-- Compatibility of `serre_D` with subtraction. -/
public theorem serre_D_sub (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F - G) = serre_D k F - serre_D k G :=
  Derivative.serreDerivative_sub k F G hF hG

/-- Compatibility of `serre_D` with scalar multiplication. -/
public theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F := by fun_prop) :
    serre_D k (c • F) = c • serre_D k F :=
  Derivative.serreDerivative_smul k c F hF

/-- Leibniz rule for the Serre derivative, with weights `k₁` and `k₂`. -/
public theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D (k₁ + k₂) (F * G) = (serre_D k₁ F) * G + F * (serre_D k₂ G) := by
  simpa using Derivative.serreDerivative_mul (k₁ : ℂ) (k₂ : ℂ) F G hF hG

/-- The Serre derivative preserves MDifferentiability. -/
public theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDiff F) : MDiff (serre_D k F) :=
  Derivative.serreDerivative_mdifferentiable k hF

/-- The Serre derivative of a bounded holomorphic function is bounded at infinity.

serre_D k f = D f - (k/12)·E₂·f. Both terms are bounded:
- D f is bounded by `D_isBoundedAtImInfty_of_bounded`
- (k/12)·E₂·f is bounded since E₂ and f are bounded -/
public theorem serre_D_isBoundedAtImInfty {f : ℍ → ℂ} (k : ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) : IsBoundedAtImInfty (serre_D k f) := by
  have hD : IsBoundedAtImInfty (D f) := D_isBoundedAtImInfty_of_bounded hf hbdd
  have hE₂f : IsBoundedAtImInfty (fun z => k * 12⁻¹ * E₂ z * f z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => k * 12⁻¹) := Filter.const_boundedAtFilter _ _
    convert hconst.mul (E₂_isBoundedAtImInfty.mul hbdd) using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact hD.sub hE₂f
