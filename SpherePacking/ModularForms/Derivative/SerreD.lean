module
public import SpherePacking.ModularForms.Derivative.Basic

@[expose] public section

/-!
# The Serre derivative

This file defines the Serre derivative `serre_D k F z = D F z - (k/12) · E₂(z) · F(z)` of weight
`k`, proves its basic algebraic properties (linearity, Leibniz rule, preservation of
MDifferentiability) and shows it preserves boundedness at imaginary infinity for bounded
holomorphic inputs.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function

/-- Serre derivative of weight `k` for functions `F : ℍ → ℂ`. -/
@[expose] public noncomputable def serre_D (k : ℂ) : (ℍ → ℂ) → (ℍ → ℂ) :=
  fun (F : ℍ → ℂ) => (fun z => D F z - k * 12⁻¹ * E₂ z * F z)

@[simp]
lemma serre_D_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serre_D k F z = D F z - k * 12⁻¹ * E₂ z * F z := rfl

public lemma serre_D_eq (k : ℂ) (F : ℍ → ℂ) :
    serre_D k F = fun z => D F z - k * 12⁻¹ * E₂ z * F z := rfl

/-- Basic properties of Serre derivative. -/
public theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp [serre_D, D_add F G hF hG]
  ring

/-- Compatibility of `serre_D` with subtraction. -/
public theorem serre_D_sub (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F - G) = serre_D k F - serre_D k G := by
  ext z
  simp [serre_D, D_sub F G hF hG]
  ring

/-- Compatibility of `serre_D` with scalar multiplication. -/
public theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) :
    serre_D k (c • F) = c • serre_D k F := by
  ext z
  simp [serre_D, D_smul c F]
  ring

/-- Leibniz rule for the Serre derivative, with weights `k₁` and `k₂`. -/
public theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D (k₁ + k₂) (F * G) = (serre_D k₁ F) * G + F * (serre_D k₂ G) := by
  ext z
  simp [serre_D, D_mul F G hF hG]
  ring

/-- The Serre derivative preserves MDifferentiability. -/
public theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDiff F) : MDiff (serre_D k F) := by
  refine (D_differentiable hF).sub ?_
  have hterm0 : MDiff (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
    (mdifferentiable_const : MDiff fun _ : ℍ => k * 12⁻¹).mul (E₂_holo'.mul hF)
  simpa [mul_assoc] using hterm0

/-- The Serre derivative of a bounded holomorphic function is bounded at infinity.

serre_D k f = D f - (k/12)·E₂·f. Both terms are bounded:
- D f is bounded by `D_isBoundedAtImInfty_of_bounded`
- (k/12)·E₂·f is bounded since E₂ and f are bounded -/
public theorem serre_D_isBoundedAtImInfty {f : ℍ → ℂ} (k : ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) : IsBoundedAtImInfty (serre_D k f) := by
  unfold serre_D
  have hD : IsBoundedAtImInfty (D f) := D_isBoundedAtImInfty_of_bounded hf hbdd
  have hE₂f : IsBoundedAtImInfty (fun z => k * 12⁻¹ * E₂ z * f z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => k * 12⁻¹) := Filter.const_boundedAtFilter _ _
    convert hconst.mul (E₂_isBoundedAtImInfty.mul hbdd) using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact hD.sub hE₂f
