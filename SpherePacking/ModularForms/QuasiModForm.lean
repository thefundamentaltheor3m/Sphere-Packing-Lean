import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic


open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm MatrixGroups SlashAction CongruenceSubgroup

#check MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
#check 𝓘(ℂ)

local notation "E[" k "]" => @eisensteinSeries_MF k 1 (by decide) 0
noncomputable def E₄ : ModularForm (Gamma 1) 4 := (1/2) • E[4]
noncomputable def E₆ : ModularForm (Gamma 1) 6 := (1/2) • E[6]

/-- Normalized derivative -/
-- noncomputable def D (f : ℂ → ℂ) := λ z ↦ (1 / (2 * π * I)) • (deriv f z)
noncomputable def D (f : ℍ → ℂ) : (ℍ → ℂ) := sorry

noncomputable def E₂_term (n : ℕ) (τ : ℍ) : ℂ := (-24) * cexp (2 * π * I * n * τ)
-- noncomputable def E₂ (z : ℂ) : ℂ := 1 - 24 * ∑' k : ℕ, ↑(σ k) * q z ^ k

noncomputable def E₂ (τ : ℍ) : ℂ := sorry




/-- Ramanujan's formula -/

-- Serre derivatives, which are slash invariant forms
noncomputable def SE₂ : ℍ → ℂ := (D E₂) - E₂^2 / 12
noncomputable def SE₄ : ℍ → ℂ := (D E₄) - E₂ * E₄ / 3
noncomputable def SE₆ : ℍ → ℂ := (D E₆) - E₂ * E₆ / 2


theorem Ramanujan_E₂ : D E₂ = (E₂^2 - E₄) / 12 := sorry
theorem Ramanujan_E₄ : D E₄ = (E₂ * E₄ - E₆) / 3 := sorry
theorem Ramanujan_E₆ : D E₆ = (E₂ * E₆ - E₄^2) / 2 := sorry
