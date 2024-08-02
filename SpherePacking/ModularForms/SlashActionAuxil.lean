import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

/-!
# Auxiliary theorems for the slash actions groups SL(2, ℤ) and Γ(2)

Define special generators S, T, -I (resp. α, β, -I) for SL(2,ℤ) (resp. Γ(2)) and prove that
they are indeed generators.
As a corollary, we only need to check the invariance under these special elements to check
the invariance under the whole group.
These theorems will be used to prove that 4-th powers of Jacobi theta functions Θ_2^4, Θ_3^4, Θ_4^4
are modular forms of weight 2 and level Γ(2).
-/

open Matrix UpperHalfPlane

open scoped ModularForm

local notation "SL(" n ", " R ")" => SpecialLinearGroup (Fin n) R
local notation "Γ(" n ")" => CongruenceSubgroup.Gamma n


def S : SL(2, ℤ) := ⟨!![0, -1; 1, 0], by simp⟩
def T : SL(2, ℤ) := ⟨!![1, 1; 0, 1], by simp⟩
def negI : SL(2, ℤ) := ⟨!![-1, 0; 0, -1], by simp⟩
-- TODO: better naming for these generators?
def α : Γ(2) := sorry  -- 1 2 // 0 1
def β : Γ(2) := sorry  -- 1 0 // 2 1
def negI_Γ2 : Γ(2) := sorry


theorem even_weight_negI_action (f : ℍ → ℂ) (k : ℤ) (hk : Even k) : (f ∣[k] negI = f) := by sorry
theorem even_weight_negI_Γ2_action (f : ℍ → ℂ) (k : ℤ) (hk : Even k) : (f ∣[k] negI_Γ2 = f) := by sorry

theorem SL2Z_generate : (Set.univ : Set SL(2, ℤ)) = Subgroup.closure {S, T, negI} := by
  ext ⟨x, hx_det⟩
  simp only [Set.mem_univ, SetLike.mem_coe, true_iff]
  -- now prove that all 2x2 matrices with det 1 is in closure of S, T, and -I
  sorry

theorem Γ2_generate : (Set.univ : Set Γ(2)) = Subgroup.closure {α, β, negI_Γ2} := by
  ext ⟨x, hx_det⟩
  simp only [Set.mem_univ, SetLike.mem_coe, true_iff]
  -- now prove that all 2x2 matrices with det 1 and equivalent to I modulo 2
  -- is in closure of α, β, and -I
  sorry

theorem slashaction_generators
    (f : ℍ → ℂ) (G : Subgroup SL(2, ℤ)) {s : Set SL(2, ℤ)} (hG : G = Subgroup.closure s) (k : ℤ) :
    (∀ γ : G, f ∣[k] γ = f) ↔ (∀ γ ∈ s, f ∣[k] γ = f) := by
  subst hG
  constructor <;> intro h
  · intro γ hγ
    convert h ⟨γ, Subgroup.subset_closure hγ⟩
  · intro ⟨γ, hγ⟩
    -- key idea: this lemma allows induction on the "words" of the group
    apply Subgroup.closure_induction (G := SL(2, ℤ)) (p := fun γ ↦ f ∣[k] γ = f) hγ h
    · exact SlashAction.slash_one _ _
    · intro x y hx hy
      rw [SlashAction.slash_mul, hx, hy]
    · intro x hx
      rw [← hx, ← SlashAction.slash_mul, mul_inv_self, SlashAction.slash_one, hx]


theorem slashaction_generators_SL2Z
    (f : ℍ → ℂ) (k : ℤ) (hS : f ∣[k] S = f) (hT : f ∣[k] T = f)
    (hnegI : f ∣[k] negI = f) : (∀ γ : SL(2, ℤ), f ∣[k] γ = f) := by
  sorry

theorem slashaction_generators_Γ2
    (f : ℍ → ℂ) (k : ℤ) (hα : f ∣[k] α = f) (hβ : f ∣[k] β = f)
    (hnegI_Γ2 : f ∣[k] negI_Γ2 = f) : (∀ γ : Γ(2), f ∣[k] γ = f) := by
  sorry
