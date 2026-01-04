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

/-!
## Phase 6: Level-1 Invariants g, h
-/

/-- Level-1 invariant of weight 6: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ -/
noncomputable def theta_g : ℍ → ℂ :=
  ((2 : ℂ) • H₂ + H₄) * f₂ + (H₂ + (2 : ℂ) • H₄) * f₄

/-- Level-1 invariant of weight 8: h = f₂² + f₂f₄ + f₄² -/
noncomputable def theta_h : ℍ → ℂ := f₂ ^ 2 + f₂ * f₄ + f₄ ^ 2

/-- g is invariant under S.

Proof: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
Under S: H₂ ↦ -H₄, H₄ ↦ -H₂, f₂ ↦ -f₄, f₄ ↦ -f₂
g|S = (2(-H₄) + (-H₂))(-f₄) + ((-H₄) + 2(-H₂))(-f₂)
    = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂
    = g -/
lemma theta_g_S_action : (theta_g ∣[(6 : ℤ)] S) = theta_g := by
  -- Linear combination transforms: (2•H₂ + H₄)|S = -(2•H₄ + H₂), (H₂ + 2•H₄)|S = -(H₄ + 2•H₂)
  have h_2H₂_H₄ : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) = -((2 : ℂ) • H₄ + H₂) := by
    simp only [SlashAction.add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  have h_H₂_2H₄ : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    simp only [SlashAction.add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Product transforms using mul_slash_SL2
  have h_term1 : ((((2 : ℂ) • H₂ + H₄) * f₂) ∣[(6 : ℤ)] S) = ((2 : ℂ) • H₄ + H₂) * f₄ := by
    have hmul := mul_slash_SL2 2 4 S ((2 : ℂ) • H₂ + H₄) f₂
    simp only [h_2H₂_H₄, f₂_S_action] at hmul
    convert hmul using 1; ext z; simp only [Pi.mul_apply, Pi.neg_apply]; ring
  have h_term2 : (((H₂ + (2 : ℂ) • H₄) * f₄) ∣[(6 : ℤ)] S) = (H₄ + (2 : ℂ) • H₂) * f₂ := by
    have hmul := mul_slash_SL2 2 4 S (H₂ + (2 : ℂ) • H₄) f₄
    simp only [h_H₂_2H₄, f₄_S_action] at hmul
    convert hmul using 1; ext z; simp only [Pi.mul_apply, Pi.neg_apply]; ring
  -- g|S = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂ = g
  simp only [theta_g, SlashAction.add_slash, h_term1, h_term2]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply]; ring

/-- g is invariant under T.

Proof: Under T: H₂ ↦ -H₂, H₄ ↦ H₃, f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
g|T = (2(-H₂) + H₃)(-f₂) + ((-H₂) + 2H₃)(f₂ + f₄)
Using Jacobi: H₃ = H₂ + H₄, simplifies to g. -/
lemma theta_g_T_action : (theta_g ∣[(6 : ℤ)] T) = theta_g := by
  -- Under T: H₂ → -H₂, H₄ → H₃, f₂ → -f₂, f₄ → f₃
  -- Linear combination transforms: (2•H₂ + H₄)|T = -2•H₂ + H₃, (H₂ + 2•H₄)|T = -H₂ + 2•H₃
  have h_2H₂_H₄ : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = -(2 : ℂ) • H₂ + H₃ := by
    simp only [SlashAction.add_slash, SL_smul_slash, H₂_T_action, H₄_T_action, smul_neg]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have h_H₂_2H₄ : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = -H₂ + (2 : ℂ) • H₃ := by
    simp only [SlashAction.add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
  -- Product transforms
  have h_term1 : ((((2 : ℂ) • H₂ + H₄) * f₂) ∣[(6 : ℤ)] T) = (-(2 : ℂ) • H₂ + H₃) * (-f₂) := by
    have hmul := mul_slash_SL2 2 4 T ((2 : ℂ) • H₂ + H₄) f₂
    simp only [h_2H₂_H₄, f₂_T_action] at hmul
    exact hmul
  have h_term2 : (((H₂ + (2 : ℂ) • H₄) * f₄) ∣[(6 : ℤ)] T) = (-H₂ + (2 : ℂ) • H₃) * f₃ := by
    have hmul := mul_slash_SL2 2 4 T (H₂ + (2 : ℂ) • H₄) f₄
    simp only [h_H₂_2H₄, f₄_T_action] at hmul
    exact hmul
  -- Combine and simplify using Jacobi: H₃ = H₂ + H₄, f₃ = f₂ + f₄
  simp only [theta_g, SlashAction.add_slash, h_term1, h_term2]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  have hH₃ : H₃ z = H₂ z + H₄ z := (jacobi_identity' z).symm
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
  -- Under S: f₂ ↦ -f₄, f₄ ↦ -f₂
  -- (f₂²)|S = f₄², (f₄²)|S = f₂², (f₂f₄)|S = f₂f₄
  have h_f₂_sq : ((f₂ ^ 2) ∣[(8 : ℤ)] S) = f₄ ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₂
    simp only [f₂_S_action] at hmul
    convert hmul using 1 <;> ext <;> simp [sq]
  have h_f₄_sq : ((f₄ ^ 2) ∣[(8 : ℤ)] S) = f₂ ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₄ f₄
    simp only [f₄_S_action] at hmul
    convert hmul using 1 <;> ext <;> simp [sq]
  have h_f₂f₄ : ((f₂ * f₄) ∣[(8 : ℤ)] S) = f₂ * f₄ := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₄
    simp only [f₂_S_action, f₄_S_action] at hmul
    convert hmul using 1
    ext z
    simp only [Pi.mul_apply, Pi.neg_apply, neg_mul_neg, mul_comm]
  -- h|S = f₄² + f₂f₄ + f₂² = h
  simp only [theta_h, SlashAction.add_slash, h_f₂_sq, h_f₂f₄, h_f₄_sq]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, sq]
  ring

/-- h is invariant under T.

Proof: Under T: f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
h|T = (-f₂)² + (-f₂)(f₂ + f₄) + (f₂ + f₄)²
    = f₂² - f₂² - f₂f₄ + f₂² + 2f₂f₄ + f₄²
    = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_T_action : (theta_h ∣[(8 : ℤ)] T) = theta_h := by
  -- Under T: f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
  -- (f₂²)|T = f₂², (f₄²)|T = (f₂+f₄)², (f₂f₄)|T = (-f₂)(f₂+f₄)
  have h_f₂_sq : ((f₂ ^ 2) ∣[(8 : ℤ)] T) = f₂ ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₂
    simp only [f₂_T_action] at hmul
    convert hmul using 1 <;> ext <;> simp [sq]
  have h_f₄_sq : ((f₄ ^ 2) ∣[(8 : ℤ)] T) = (f₂ + f₄) ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₄ f₄
    simp only [f₄_T_action] at hmul
    convert hmul using 1
    · ext; simp [sq]
    · ext z; simp only [Pi.pow_apply, Pi.mul_apply, sq]
      rw [(congrFun f₂_add_f₄_eq_f₃ z).symm, Pi.add_apply]
  have h_f₂f₄ : ((f₂ * f₄) ∣[(8 : ℤ)] T) = (-f₂) * (f₂ + f₄) := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₄
    simp only [f₂_T_action, f₄_T_action] at hmul
    convert hmul using 1
    ext z
    simp only [Pi.mul_apply, Pi.neg_apply]
    rw [(congrFun f₂_add_f₄_eq_f₃ z).symm, Pi.add_apply]
  -- h|T = f₂² + (-f₂)(f₂+f₄) + (f₂+f₄)² = h
  simp only [theta_h, SlashAction.add_slash, h_f₂_sq, h_f₂f₄, h_f₄_sq]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, sq]
  ring
