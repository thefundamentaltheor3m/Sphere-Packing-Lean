import SpherePacking.ModularForms.ThetaDerivSlashActions

/-!
# Theta Derivative Identities - Level-1 Invariants

This file constructs level-1 invariants from the theta error terms, continuing the
proof of the Serre derivative identities for Jacobi theta functions (Blueprint Prop 6.52).

## Contents

* Level-1 invariant `theta_g` (weight 6): g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
* Level-1 invariant `theta_h` (weight 8): h = f₂² + f₂f₄ + f₄²
* S/T invariance: `theta_g_S_action`, `theta_g_T_action`, `theta_h_S_action`, `theta_h_T_action`

## Strategy

Using the S/T transformation rules from `ThetaDerivSlashActions`:
- f₂|S = -f₄, f₂|T = -f₂, f₄|S = -f₂, f₄|T = f₃

We construct g and h such that g|S = g, g|T = g, h|S = h, h|T = h.
This makes g and h into level-1 (SL(2,ℤ)-invariant) modular forms.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

/-!
## Phase 6: Level-1 Invariants g, h
-/

/-- Level-1 invariant of weight 6: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ -/
noncomputable def theta_g : ℍ → ℂ := fun z =>
  (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z

/-- Level-1 invariant of weight 8: h = f₂² + f₂f₄ + f₄² -/
noncomputable def theta_h : ℍ → ℂ := fun z =>
  f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2

/-- g is invariant under S.

Proof: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
Under S: H₂ ↦ -H₄, H₄ ↦ -H₂, f₂ ↦ -f₄, f₄ ↦ -f₂
g|S = (2(-H₄) + (-H₂))(-f₄) + ((-H₄) + 2(-H₂))(-f₂)
    = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂
    = g -/
lemma theta_g_S_action : (theta_g ∣[(6 : ℤ)] S) = theta_g := by
  have hf₂ := f₂_S_action
  have hf₄ := f₄_S_action
  have hH₂ := H₂_S_action
  have hH₄ := H₄_S_action
  -- First, prove the transformations for the linear combinations
  have h_2H₂_H₄ : ((fun z => 2 * H₂ z + H₄ z) ∣[(2 : ℤ)] S) =
      fun z => -(2 * H₄ z + H₂ z) := by
    have h_smul := SL_smul_slash (2 : ℤ) S H₂ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) S ((2 : ℂ) • H₂) H₄
    have hfun1 : (fun z => 2 * H₂ z + H₄ z) = ((2 : ℂ) • H₂) + H₄ := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  have h_H₂_2H₄ : ((fun z => H₂ z + 2 * H₄ z) ∣[(2 : ℤ)] S) =
      fun z => -(H₄ z + 2 * H₂ z) := by
    have h_smul := SL_smul_slash (2 : ℤ) S H₄ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) S H₂ ((2 : ℂ) • H₄)
    have hfun1 : (fun z => H₂ z + 2 * H₄ z) = H₂ + ((2 : ℂ) • H₄) := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Now prove the product transformations using mul_slash_SL2
  have h_term1 : ((fun z => (2 * H₂ z + H₄ z) * f₂ z) ∣[(6 : ℤ)] S) =
      fun z => (2 * H₄ z + H₂ z) * f₄ z := by
    have hmul := mul_slash_SL2 2 4 S (fun z => 2 * H₂ z + H₄ z) f₂
    have hfun : (fun z => (2 * H₂ z + H₄ z) * f₂ z) =
        (fun z => 2 * H₂ z + H₄ z) * f₂ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_2H₂_H₄, hf₂]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]; ring
  have h_term2 : ((fun z => (H₂ z + 2 * H₄ z) * f₄ z) ∣[(6 : ℤ)] S) =
      fun z => (H₄ z + 2 * H₂ z) * f₂ z := by
    have hmul := mul_slash_SL2 2 4 S (fun z => H₂ z + 2 * H₄ z) f₄
    have hfun : (fun z => (H₂ z + 2 * H₄ z) * f₄ z) =
        (fun z => H₂ z + 2 * H₄ z) * f₄ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_H₂_2H₄, hf₄]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]; ring
  -- Combine: g|S = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂ = g
  have hfun_g : theta_g =
      (fun z => (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z) := by
    funext z; unfold theta_g; ring
  rw [hfun_g]
  have hfun_sum : (fun z => (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z) =
      (fun z => (2 * H₂ z + H₄ z) * f₂ z) + (fun z => (H₂ z + 2 * H₄ z) * f₄ z) := by
    funext; simp [Pi.add_apply]
  have h_add := SlashAction.add_slash (6 : ℤ) S
    (fun z => (2 * H₂ z + H₄ z) * f₂ z) (fun z => (H₂ z + 2 * H₄ z) * f₄ z)
  rw [hfun_sum, h_add, h_term1, h_term2]
  funext z; simp only [Pi.add_apply]; ring

/-- g is invariant under T.

Proof: Under T: H₂ ↦ -H₂, H₄ ↦ H₃, f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
g|T = (2(-H₂) + H₃)(-f₂) + ((-H₂) + 2H₃)(f₂ + f₄)
Using Jacobi: H₃ = H₂ + H₄, simplifies to g. -/
lemma theta_g_T_action : (theta_g ∣[(6 : ℤ)] T) = theta_g := by
  have hf₂ := f₂_T_action
  have hf₄ := f₄_T_action
  have hH₂ := H₂_T_action
  have hH₄ := H₄_T_action
  have h_jacobi := fun z => jacobi_identity' z
  -- Under T: H₂ → -H₂, H₄ → H₃ = H₂ + H₄, f₂ → -f₂, f₄ → f₃
  -- Transform linear combinations
  have h_2H₂_H₄ : ((fun z => 2 * H₂ z + H₄ z) ∣[(2 : ℤ)] T) =
      fun z => -2 * H₂ z + H₃ z := by
    have h_smul := SL_smul_slash (2 : ℤ) T H₂ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) T ((2 : ℂ) • H₂) H₄
    have hfun1 : (fun z => 2 * H₂ z + H₄ z) = ((2 : ℂ) • H₂) + H₄ := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
  have h_H₂_2H₄ : ((fun z => H₂ z + 2 * H₄ z) ∣[(2 : ℤ)] T) =
      fun z => -H₂ z + 2 * H₃ z := by
    have h_smul := SL_smul_slash (2 : ℤ) T H₄ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) T H₂ ((2 : ℂ) • H₄)
    have hfun1 : (fun z => H₂ z + 2 * H₄ z) = H₂ + ((2 : ℂ) • H₄) := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
  -- Product transformations
  have h_term1 : ((fun z => (2 * H₂ z + H₄ z) * f₂ z) ∣[(6 : ℤ)] T) =
      fun z => (-2 * H₂ z + H₃ z) * (-f₂ z) := by
    have hmul := mul_slash_SL2 2 4 T (fun z => 2 * H₂ z + H₄ z) f₂
    have hfun : (fun z => (2 * H₂ z + H₄ z) * f₂ z) =
        (fun z => 2 * H₂ z + H₄ z) * f₂ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_2H₂_H₄, hf₂]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]
  have h_term2 : ((fun z => (H₂ z + 2 * H₄ z) * f₄ z) ∣[(6 : ℤ)] T) =
      fun z => (-H₂ z + 2 * H₃ z) * f₃ z := by
    have hmul := mul_slash_SL2 2 4 T (fun z => H₂ z + 2 * H₄ z) f₄
    have hfun : (fun z => (H₂ z + 2 * H₄ z) * f₄ z) =
        (fun z => H₂ z + 2 * H₄ z) * f₄ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_H₂_2H₄, hf₄]
    funext z; simp [Pi.mul_apply]
  -- Now combine and simplify using Jacobi: H₃ = H₂ + H₄, f₃ = f₂ + f₄
  have hfun_g : theta_g = (fun z => (2 * H₂ z + H₄ z) * f₂ z +
      (H₂ z + 2 * H₄ z) * f₄ z) := by funext z; unfold theta_g; ring
  rw [hfun_g]
  have hfun_sum : (fun z => (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z) =
      (fun z => (2 * H₂ z + H₄ z) * f₂ z) + (fun z => (H₂ z + 2 * H₄ z) * f₄ z) := by
    funext; simp [Pi.add_apply]
  have h_add := SlashAction.add_slash (6 : ℤ) T
    (fun z => (2 * H₂ z + H₄ z) * f₂ z) (fun z => (H₂ z + 2 * H₄ z) * f₄ z)
  rw [hfun_sum, h_add, h_term1, h_term2]
  -- Simplify using Jacobi identity
  funext z
  simp only [Pi.add_apply]
  -- H₃ = H₂ + H₄ and f₃ = f₂ + f₄
  have hH₃ : H₃ z = H₂ z + H₄ z := (h_jacobi z).symm
  have hf₃ : f₃ z = f₂ z + f₄ z := (congrFun f₂_add_f₄_eq_f₃ z).symm
  rw [hH₃, hf₃]
  ring

/-- h is invariant under S.

Proof: h = f₂² + f₂f₄ + f₄²
Under S: f₂|[4]S = -f₄, f₄|[4]S = -f₂
Using mul_slash_SL2: (f₂²)|[8]S = (f₂|[4]S)² = (-f₄)² = f₄²
                     (f₂f₄)|[8]S = (f₂|[4]S)(f₄|[4]S) = (-f₄)(-f₂) = f₂f₄
                     (f₄²)|[8]S = (f₄|[4]S)² = (-f₂)² = f₂²
So h|[8]S = f₄² + f₂f₄ + f₂² = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_S_action : (theta_h ∣[(8 : ℤ)] S) = theta_h := by
  have hf₂ := f₂_S_action
  have hf₄ := f₄_S_action
  -- h = f₂² + f₂f₄ + f₄² = f₂*f₂ + f₂*f₄ + f₄*f₄
  -- Use mul_slash_SL2: (f*g)|[k1+k2]S = (f|[k1]S)*(g|[k2]S)
  have h_f₂_sq : ((fun z => f₂ z ^ 2) ∣[(8 : ℤ)] S) = fun z => f₄ z ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₂
    rw [hf₂] at hmul
    have hfun : (fun z => f₂ z ^ 2) = (f₂ * f₂) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, sq, neg_mul_neg]
  have h_f₄_sq : ((fun z => f₄ z ^ 2) ∣[(8 : ℤ)] S) = fun z => f₂ z ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₄ f₄
    rw [hf₄] at hmul
    have hfun : (fun z => f₄ z ^ 2) = (f₄ * f₄) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, sq, neg_mul_neg]
  have h_f₂f₄ : ((fun z => f₂ z * f₄ z) ∣[(8 : ℤ)] S) = fun z => f₂ z * f₄ z := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₄
    rw [hf₂, hf₄] at hmul
    have hfun : (fun z => f₂ z * f₄ z) = (f₂ * f₄) := by funext w; simp [Pi.mul_apply]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, neg_mul_neg, mul_comm]
  -- Combine: h|S = f₄² + f₂f₄ + f₂² = h
  have hfun_h : theta_h = (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) := by
    funext z; unfold theta_h; ring
  rw [hfun_h]
  have hfun_lhs1 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z) =
      (fun z => f₂ z ^ 2) + (fun z => f₂ z * f₄ z) := by funext; simp [Pi.add_apply]
  have h_add1 := SlashAction.add_slash (8 : ℤ) S (fun z => f₂ z ^ 2) (fun z => f₂ z * f₄ z)
  have hfun_lhs2 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) =
      (fun z => f₂ z ^ 2 + f₂ z * f₄ z) + (fun z => f₄ z ^ 2) := by
    funext; simp [Pi.add_apply]
  have h_add2 := SlashAction.add_slash (8 : ℤ) S
    (fun z => f₂ z ^ 2 + f₂ z * f₄ z) (fun z => f₄ z ^ 2)
  rw [hfun_lhs2, h_add2, hfun_lhs1, h_add1, h_f₂_sq, h_f₂f₄, h_f₄_sq]
  funext z; simp only [Pi.add_apply]; ring

/-- h is invariant under T.

Proof: Under T: f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
h|T = (-f₂)² + (-f₂)(f₂ + f₄) + (f₂ + f₄)²
    = f₂² - f₂² - f₂f₄ + f₂² + 2f₂f₄ + f₄²
    = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_T_action : (theta_h ∣[(8 : ℤ)] T) = theta_h := by
  have hf₂ := f₂_T_action
  have hf₄ := f₄_T_action
  have hf₂f₄ := f₂_add_f₄_eq_f₃
  -- Under T: f₂ → -f₂, f₄ → f₃ = f₂ + f₄
  -- (f₂²)|T = (-f₂)² = f₂², (f₄²)|T = (f₂+f₄)², (f₂f₄)|T = (-f₂)(f₂+f₄)
  have h_f₂_sq : ((fun z => f₂ z ^ 2) ∣[(8 : ℤ)] T) = fun z => f₂ z ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₂
    rw [hf₂] at hmul
    have hfun : (fun z => f₂ z ^ 2) = (f₂ * f₂) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, neg_mul_neg]
  have h_f₄_sq : ((fun z => f₄ z ^ 2) ∣[(8 : ℤ)] T) = fun z => (f₂ z + f₄ z) ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₄ f₄
    rw [hf₄] at hmul
    have hfun : (fun z => f₄ z ^ 2) = (f₄ * f₄) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z
    simp only [Pi.mul_apply, sq]
    rw [(congrFun hf₂f₄ z).symm, Pi.add_apply]
  have h_f₂f₄' : ((fun z => f₂ z * f₄ z) ∣[(8 : ℤ)] T) =
      fun z => (-f₂ z) * (f₂ z + f₄ z) := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₄
    rw [hf₂, hf₄] at hmul
    have hfun : (fun z => f₂ z * f₄ z) = (f₂ * f₄) := by funext w; simp [Pi.mul_apply]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z
    simp only [Pi.mul_apply, Pi.neg_apply]
    rw [(congrFun hf₂f₄ z).symm, Pi.add_apply]
  -- Combine: h|T = f₂² + (-f₂)(f₂+f₄) + (f₂+f₄)² = h
  have hfun_h : theta_h = (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) := by
    funext z; unfold theta_h; ring
  rw [hfun_h]
  have hfun_lhs1 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z) =
      (fun z => f₂ z ^ 2) + (fun z => f₂ z * f₄ z) := by funext; simp [Pi.add_apply]
  have h_add1 := SlashAction.add_slash (8 : ℤ) T (fun z => f₂ z ^ 2) (fun z => f₂ z * f₄ z)
  have hfun_lhs2 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) =
      (fun z => f₂ z ^ 2 + f₂ z * f₄ z) + (fun z => f₄ z ^ 2) := by
    funext; simp [Pi.add_apply]
  have h_add2 := SlashAction.add_slash (8 : ℤ) T
    (fun z => f₂ z ^ 2 + f₂ z * f₄ z) (fun z => f₄ z ^ 2)
  rw [hfun_lhs2, h_add2, hfun_lhs1, h_add1, h_f₂_sq, h_f₂f₄', h_f₄_sq]
  funext z; simp only [Pi.add_apply]; ring
