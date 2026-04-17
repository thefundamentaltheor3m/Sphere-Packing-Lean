module
public import SpherePacking.ModularForms.Derivative.SlashFormula

@[expose] public section

/-!
# Slash equivariance of the Serre derivative

This file proves the Serre derivative `serre_D k F` is equivariant under the weight-`k` slash
action: if `F ∣[k] γ = F` then `serre_D k F ∣[k+2] γ = serre_D k F`. As an application, for a
level-one weight-`k` modular form `f`, we package `serre_D k f` as a modular form of weight
`k + 2`.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function

/-- Serre derivative is equivariant under the slash action. -/
public theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by
  intro γ
  ext z
  let c : ℂ := (k : ℂ) * 12⁻¹
  let corr : ℍ → ℂ := fun w : ℍ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ w)
  have h12 : (12 : ℂ) ≠ 0 := by norm_num
  have hD := congrFun (D_slash k F hF γ) z
  have hE : (E₂ ∣[(2 : ℤ)] γ) z = E₂ z + corr z := by
    simpa [corr] using congrFun (E₂_slash γ) z
  have hserre : serre_D k F = D F - c • (E₂ * F) := by
    ext w
    simp [serre_D, c, smul_eq_mul, mul_assoc]
  have hmul : (E₂ * F) ∣[k + 2] γ = (E₂ ∣[(2 : ℤ)] γ) * (F ∣[k] γ) := by
    -- Mathlib's lemma is stated for weight `2 + k`; rewrite to `k + 2`.
    simpa [add_comm, add_left_comm, add_assoc] using
      (ModularForm.mul_slash_SL2 (k1 := (2 : ℤ)) (k2 := k) (A := γ) (f := E₂) (g := F))
  -- Main computation, pointwise at `z`.
  calc
    (serre_D k F ∣[k + 2] γ) z
        = ((D F - c • (E₂ * F)) ∣[k + 2] γ) z := by simp [hserre]
    _ = (D F ∣[k + 2] γ) z - (c • ((E₂ * F) ∣[k + 2] γ)) z := by
          simp [sub_eq_add_neg, SlashAction.neg_slash]
    _ = (D F ∣[k + 2] γ) z - c * ((E₂ * F) ∣[k + 2] γ) z := by
          simp [Pi.smul_apply, smul_eq_mul]
    _ = (D F ∣[k + 2] γ) z - c * ((E₂ ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z) := by
          simp [hmul, Pi.mul_apply]
    _ = (D F ∣[k + 2] γ) z - c * ((E₂ z + corr z) * (F ∣[k] γ) z) := by
          rw [hE]
    _ = (D F ∣[k + 2] γ) z
          - c * (corr z * (F ∣[k] γ) z)
          - c * (E₂ z * (F ∣[k] γ) z) := by
          ring
    _ = (D F ∣[k + 2] γ) z
          - (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z
          - c * (E₂ z * (F ∣[k] γ) z) := by
          ring
    _ = serre_D k (F ∣[k] γ) z := by
          -- Substitute the `D_slash` anomaly and unfold the Serre derivative.
          have hD' :
              D (F ∣[k] γ) z =
                (D F ∣[k + 2] γ) z -
                  (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z := by
            simpa [Pi.sub_apply] using hD
          -- Unfold `serre_D`, rewrite `D (F ∣[k] γ) z` using `hD'`, and reassociate.
          simp [serre_D, c, hD', mul_assoc]

public theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ))
    (h : F ∣[k] γ = F) : serre_D k F ∣[k + 2] γ = serre_D k F := by
  simpa [h] using serre_D_slash_equivariant (k := k) (F := F) hF γ

/-- A level-1 modular form is invariant under slash action by any element of SL(2,ℤ). -/
lemma ModularForm.slash_eq_self {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] γ = f := by
  simpa using f.slash_action_eq' _ ⟨γ, mem_Gamma_one γ, rfl⟩

/-- The Serre derivative of a weight-k level-1 modular form is a weight-(k+2) modular form. -/
@[expose] public noncomputable def serre_D_ModularForm (k : ℤ) (f : ModularForm (Gamma 1) k) :
    ModularForm (Gamma 1) (k + 2) where
  toSlashInvariantForm := {
    toFun := serre_D k f
    slash_action_eq' := fun _ hγ => by
      obtain ⟨γ', -, rfl⟩ := Subgroup.mem_map.mp hγ
      simpa using serre_D_slash_invariant k f f.holo' γ' (f.slash_eq_self γ')
  }
  holo' := serre_D_differentiable f.holo'
  bdd_at_cusps' := fun hc => bounded_at_cusps_of_bounded_at_infty hc fun _ hA => by
    obtain ⟨A', rfl⟩ := MonoidHom.mem_range.mp hA
    exact (serre_D_slash_invariant k f f.holo' A' (f.slash_eq_self A')).symm ▸
      serre_D_isBoundedAtImInfty k f.holo' (ModularFormClass.bdd_at_infty f)
