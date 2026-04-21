module

public import SpherePacking.ForMathlib.FunctionsBoundedAtInfty
public import SpherePacking.ForMathlib.MDifferentiableFunProp
public import SpherePacking.ForMathlib.SlashActions
public import SpherePacking.ForMathlib.UpperHalfPlane
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.Tactic.TendstoCont

@[expose] public section

/-!
# Jacobi theta definitions

Define Jacobi theta functions `Θ₂`, `Θ₃`, `Θ₄` and their fourth powers `H₂`, `H₃`, `H₄`.
Also record their realization as specializations of `jacobiTheta₂`.
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

/-- Define Θ₂, Θ₃, Θ₄ as series. -/
noncomputable def Θ₂_term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)
noncomputable def Θ₃_term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n : ℂ) ^ 2 * τ)
noncomputable def Θ₄_term (n : ℤ) (τ : ℍ) : ℂ := (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)
noncomputable def Θ₂ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₂_term n τ
noncomputable def Θ₃ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₃_term n τ
noncomputable def Θ₄ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₄_term n τ
noncomputable def H₂ (τ : ℍ) : ℂ := (Θ₂ τ) ^ 4
noncomputable def H₃ (τ : ℍ) : ℂ := (Θ₃ τ) ^ 4
noncomputable def H₄ (τ : ℍ) : ℂ := (Θ₄ τ) ^ 4

/-- Theta functions as specializations of `jacobiTheta₂`. -/
theorem Θ₂_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₂_term n τ = cexp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ := by
  rw [Θ₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

theorem Θ₂_as_jacobiTheta₂ (τ : ℍ) : Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  simp_rw [Θ₂, Θ₂_term_as_jacobiTheta₂_term, tsum_mul_left, jacobiTheta₂]

theorem Θ₃_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₃_term n τ = jacobiTheta₂_term n 0 τ := by
  simp [Θ₃_term, jacobiTheta₂_term]

theorem Θ₃_as_jacobiTheta₂ (τ : ℍ) : Θ₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [Θ₃, Θ₃_term_as_jacobiTheta₂_term, jacobiTheta₂]

theorem Θ₄_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₄_term n τ = jacobiTheta₂_term n (1 / 2 : ℂ) τ := by
  rw [Θ₄_term, jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]
  ring_nf

theorem Θ₄_as_jacobiTheta₂ (τ : ℍ) : Θ₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [Θ₄, Θ₄_term_as_jacobiTheta₂_term, jacobiTheta₂]
