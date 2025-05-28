import SpherePacking.ModularForms.Eisenstein

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm

open scoped ModularForm MatrixGroups

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/

noncomputable def E₄_fun : ℍ → ℂ := E₄.toFun

noncomputable def E₆_fun : ℍ → ℂ := E₆.toFun

noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ := λ (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

noncomputable def serre_D (k : ℂ) (F : ℍ → ℂ) : ℍ → ℂ := λ (z : ℍ) => D F z - k * 12⁻¹ * E₂ z * F z

/--
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant under the slash action
of weight `k`, then `serre_D k F` is invariant under the slash action of weight `k + 2`.
-/
theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) :
    ∀ γ : SL(2,ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ)
  := by sorry

theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (γ : SL(2,ℤ)) (h : F ∣[k] γ = F) :
    serre_D k F ∣[k + 2] γ = serre_D k F := by
  rw [serre_D_slash_equivariant, h]

/--
Serre derivative of Eisenstein series. Use `serre_D_slash_invariant` and compare constant terms.
Note that the dimensions of the spaces of modular forms are all 1.
-/
theorem ramanujan_E₂' (z : ℍ) : serre_D 1 E₂ z = - 12⁻¹ * E₄_fun z := by sorry

theorem ramanujan_E₄' (z : ℍ) : serre_D 4 E₄_fun z = - 3⁻¹ * E₆_fun z := by sorry

theorem ramanujan_E₆' (z : ℍ) : serre_D 6 E₆_fun z = - 2⁻¹ * E₄_fun z * E₄_fun z := by sorry

theorem ramanujan_E₂ (z : ℍ) : D E₂ z = 12⁻¹ * (E₂ z * E₂ z - E₄_fun z) := by
  have h := ramanujan_E₂' z
  rw [serre_D] at h
  ring_nf
  ring_nf at h
  rw [add_comm, ←sub_eq_iff_eq_add]
  ring_nf
  exact h

theorem ramanujan_E₄ (z : ℍ) : D E₄_fun z = 3⁻¹ * (E₂ z * E₄_fun z - E₆_fun z) := by
  have h := ramanujan_E₄' z
  rw [serre_D] at h
  ring_nf
  ring_nf at h
  rw [add_comm, ←sub_eq_iff_eq_add]
  ring_nf
  exact h

theorem ramanujan_E₆ (z : ℍ) : D E₆_fun z = 2⁻¹ * (E₂ z * E₆_fun z - E₄_fun z * E₄_fun z) := by
  have h := ramanujan_E₆' z
  rw [serre_D] at h
  ring_nf
  ring_nf at h
  rw [add_comm, ←sub_eq_iff_eq_add]
  ring_nf
  exact h
