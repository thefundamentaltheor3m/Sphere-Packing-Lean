import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.DimensionFormulas

/-!
# Theta Derivative Identities

This file defines error terms for the Serre derivative identities of Jacobi theta functions
H₂, H₃, H₄ (Blueprint Proposition 6.52), establishes their S/T transformation rules,
and constructs level-1 invariants.

## Contents

### Error Terms (Phases 1-5)
* Error terms `f₂`, `f₃`, `f₄` definitions
* MDifferentiable proofs for error terms
* Relation `f₂ + f₄ = f₃` (from `jacobi_identity` in JacobiTheta.lean)
* S/T transformation rules: `f₂_S_action`, `f₂_T_action`, `f₄_S_action`, `f₄_T_action`

### Level-1 Invariants (Phase 6)
* Level-1 invariant `theta_g` (weight 6): g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
* Level-1 invariant `theta_h` (weight 8): h = f₂² + f₂f₄ + f₄²
* S/T invariance: `theta_g_S_action`, `theta_g_T_action`, `theta_h_S_action`, `theta_h_T_action`

## Strategy

We define error terms f₂, f₃, f₄ = (LHS - RHS) and prove their transformation rules under
the S and T generators of SL(2,ℤ). The key results are:
- f₂|S = -f₄, f₂|T = -f₂
- f₄|S = -f₂, f₄|T = f₃

Using these transformation rules, we construct g and h such that g|S = g, g|T = g, h|S = h, h|T = h.
This makes g and h into level-1 (SL(2,ℤ)-invariant) modular forms.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

/-!
## Phase 1: Error Term Definitions
-/

/-- Error term for the ∂₂H₂ identity: f₂ = ∂₂H₂ - (1/6)(H₂² + 2H₂H₄) -/
noncomputable def f₂ : ℍ → ℂ :=
  serre_D 2 H₂ - (1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))

/-- Error term for the ∂₂H₃ identity: f₃ = ∂₂H₃ - (1/6)(H₂² - H₄²) -/
noncomputable def f₃ : ℍ → ℂ :=
  serre_D 2 H₃ - (1/6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2)

/-- Error term for the ∂₂H₄ identity: f₄ = ∂₂H₄ + (1/6)(2H₂H₄ + H₄²) -/
noncomputable def f₄ : ℍ → ℂ :=
  serre_D 2 H₄ + (1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))

/-- f₂ decomposes as serre_D 2 H₂ + (-1/6) • (H₂ * (H₂ + 2*H₄)) -/
lemma f₂_decompose :
    f₂ = serre_D (2 : ℤ) H₂ + ((-1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))) := by
  ext z; simp [f₂, sub_eq_add_neg]; ring

/-- f₄ decomposes as serre_D 2 H₄ + (1/6) • (H₄ * (2*H₂ + H₄)) -/
lemma f₄_decompose :
    f₄ = serre_D (2 : ℤ) H₄ + ((1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))) := by
  rfl

/-!
## Phase 2: MDifferentiable for Error Terms
-/

/-- f₂ is MDifferentiable -/
lemma f₂_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₂ := by unfold f₂; fun_prop

/-- f₃ is MDifferentiable -/
lemma f₃_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₃ := by unfold f₃; fun_prop

/-- f₄ is MDifferentiable -/
lemma f₄_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₄ := by unfold f₄; fun_prop

/-!
## Phase 3-4: Relation f₂ + f₄ = f₃
-/

/-- The error terms satisfy f₂ + f₄ = f₃ (from Jacobi identity) -/
lemma f₂_add_f₄_eq_f₃ : f₂ + f₄ = f₃ := by
  ext z; simp only [Pi.add_apply, f₂, f₃, f₄]
  -- Key relation: serre_D 2 H₂ z + serre_D 2 H₄ z = serre_D 2 H₃ z (via Jacobi identity)
  have h_serre : serre_D 2 H₂ z + serre_D 2 H₄ z = serre_D 2 H₃ z := by
    have h := congrFun (serre_D_add (2 : ℤ) H₂ H₄ H₂_SIF_MDifferentiable H₄_SIF_MDifferentiable) z
    simp only [Pi.add_apply] at h
    convert h.symm using 2; exact jacobi_identity.symm
  calc serre_D 2 H₂ z - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z)) +
       (serre_D 2 H₄ z + 1/6 * (H₄ z * (2 * H₂ z + H₄ z)))
      = (serre_D 2 H₂ z + serre_D 2 H₄ z) +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by ring
    _ = serre_D 2 H₃ z +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by rw [h_serre]
    _ = serre_D 2 H₃ z - 1/6 * (H₂ z ^ 2 - H₄ z ^ 2) := by ring

/-!
## Phase 5: S/T Transformation Rules for f₂, f₄

These transformations depend on `serre_D_slash_equivariant` (which has a sorry in Derivative.lean).
The proofs use:
- serre_D_slash_equivariant: (serre_D k F)|[k+2]γ = serre_D k (F|[k]γ)
- H₂_S_action: H₂|[2]S = -H₄
- H₄_S_action: H₄|[2]S = -H₂
- H₂_T_action: H₂|[2]T = -H₂
- H₃_T_action: H₃|[2]T = H₄
- H₄_T_action: H₄|[2]T = H₃

From these, we get:
- (serre_D 2 H₂)|[4]S = serre_D 2 (H₂|[2]S) = serre_D 2 (-H₄) = -serre_D 2 H₄
- Products transform multiplicatively: (H₂·G)|[4]S = (H₂|[2]S)·(G|[2]S)
-/

/-- f₂ transforms under S as f₂|S = -f₄.

Proof outline using serre_D_slash_equivariant:
1. (serre_D 2 H₂)|[4]S = serre_D 2 (H₂|[2]S) = serre_D 2 (-H₄) = -serre_D 2 H₄
2. (H₂(H₂ + 2H₄))|[4]S = (-H₄)((-H₄) + 2(-H₂)) = H₄(H₄ + 2H₂)
3. f₂|[4]S = -serre_D 2 H₄ - (1/6)H₄(H₄ + 2H₂) = -f₄

Key lemmas used:
- serre_D_slash_equivariant: (serre_D k F)|[k+2]γ = serre_D k (F|[k]γ)
- serre_D_smul: serre_D k (c • F) = c • serre_D k F (used for negation)
- mul_slash_SL2: (f * g)|[k1+k2]A = (f|[k1]A) * (g|[k2]A)
- add_slash, SL_smul_slash for linearity -/
lemma f₂_S_action : (f₂ ∣[(4 : ℤ)] S) = -f₄ := by
  -- Step 1: (serre_D 2 H₂)|[4]S = -serre_D 2 H₄ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₄ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable S, H₂_S_action]
    simpa using serre_D_smul 2 (-1) H₄ H₄_SIF_MDifferentiable
  -- Step 2: (H₂ + 2•H₄)|[2]S = -(H₄ + 2•H₂)
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    rw [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]S = H₄ * (H₄ + 2•H₂)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] S) = H₄ * (H₄ + (2 : ℂ) • H₂) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 S _ _, H₂_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]; ring
  -- Combine: f₂|[4]S = -serre_D 2 H₄ - (1/6) * H₄ * (2*H₂ + H₄) = -f₄
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  unfold f₄
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring_nf

/-- f₂ transforms under T as f₂|T = -f₂.

Proof outline:
1. (serre_D 2 H₂)|[4]T = serre_D 2 (H₂|[2]T) = serre_D 2 (-H₂) = -serre_D 2 H₂
2. (H₂(H₂ + 2H₄))|[4]T = (-H₂)((-H₂) + 2H₃)
   Using Jacobi H₃ = H₂ + H₄: -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
   So: (H₂(H₂ + 2H₄))|[4]T = (-H₂)(H₂ + 2H₄)
3. f₂|[4]T = -serre_D 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄)
           = -serre_D 2 H₂ + (1/6)H₂(H₂ + 2H₄)
           = -(serre_D 2 H₂ - (1/6)H₂(H₂ + 2H₄)) = -f₂ -/
lemma f₂_T_action : (f₂ ∣[(4 : ℤ)] T) = -f₂ := by
  -- Step 1: (serre_D 2 H₂)|[4]T = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] T) = -serre_D (2 : ℤ) H₂ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable T, H₂_T_action]
    simpa using serre_D_smul 2 (-1) H₂ H₂_SIF_MDifferentiable
  -- Step 2: (H₂ + 2•H₄)|[2]T = H₂ + 2•H₄ using Jacobi: H₃ = H₂ + H₄
  -- -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = H₂ + (2 : ℂ) • H₄ := by
    rw [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    simp only [show H₃ z = H₂ z + H₄ z by rw [← Pi.add_apply, (congrFun jacobi_identity z).symm]]
    ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]T = (-H₂) * (H₂ + 2•H₄)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] T) = -H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 T _ _, H₂_T_action, h_lin_comb]
  -- Combine: f₂|[4]T = -serre_D 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄) = -f₂
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]; ring

/-- f₄ transforms under S as f₄|S = -f₂.

Proof outline (symmetric to f₂_S_action):
1. (serre_D 2 H₄)|[4]S = serre_D 2 (H₄|[2]S) = serre_D 2 (-H₂) = -serre_D 2 H₂
2. (H₄(2H₂ + H₄))|[4]S = (-H₂)(2(-H₄) + (-H₂)) = H₂(H₂ + 2H₄)
3. f₄|[4]S = -serre_D 2 H₂ + (1/6)H₂(H₂ + 2H₄) = -f₂ -/
lemma f₄_S_action : (f₄ ∣[(4 : ℤ)] S) = -f₂ := by
  -- Step 1: (serre_D 2 H₄)|[4]S = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₂ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable S, H₄_S_action]
    simpa using serre_D_smul 2 (-1) H₂ H₂_SIF_MDifferentiable
  -- Step 2: (2•H₂ + H₄)|[2]S = -(2•H₄ + H₂)
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) = -((2 : ℂ) • H₄ + H₂) := by
    rw [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₄ * (2•H₂ + H₄))|[4]S = H₂ * (H₂ + 2•H₄)
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] S) = H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 S _ _, H₄_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]; ring
  -- Combine: f₄|[4]S = -serre_D 2 H₂ + (1/6) * H₂ * (H₂ + 2H₄) = -f₂
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  unfold f₂
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring_nf

/-- f₄ transforms under T as f₄|T = f₃.

Proof outline:
1. (serre_D 2 H₄)|[4]T = serre_D 2 (H₄|[2]T) = serre_D 2 H₃
2. (H₄(2H₂ + H₄))|[4]T = H₃(2(-H₂) + H₃) = H₃(H₃ - 2H₂)
   Using Jacobi H₃ = H₂ + H₄: H₃ - 2H₂ = H₄ - H₂
3. f₄|[4]T = serre_D 2 H₃ + (1/6)H₃(H₃ - 2H₂)
   But H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄)H₃
   So (1/6)(H₂² - H₄²) = -(1/6)H₃(H₄ - H₂) = -(1/6)H₃(H₃ - 2H₂)
   Thus f₃ = serre_D 2 H₃ - (1/6)(H₂² - H₄²) = f₄|[4]T -/
lemma f₄_T_action : (f₄ ∣[(4 : ℤ)] T) = f₃ := by
  -- Step 1: (serre_D 2 H₄)|[4]T = serre_D 2 H₃ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] T) = serre_D (2 : ℤ) H₃ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable T, H₄_T_action]
  -- Step 2: (2•H₂ + H₄)|[2]T = H₄ - H₂ using Jacobi: H₃ = H₂ + H₄
  -- -2H₂ + H₃ = -2H₂ + (H₂ + H₄) = H₄ - H₂
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = H₄ - H₂ := by
    rw [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
    simp only [show H₃ z = H₂ z + H₄ z by rw [← Pi.add_apply, (congrFun jacobi_identity z).symm]]
    ring
  -- Step 3: Product (H₄ * (2•H₂ + H₄))|[4]T = H₃ * (H₄ - H₂)
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] T) = H₃ * (H₄ - H₂) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 T _ _, H₄_T_action, h_lin_comb]
  -- Combine: f₄|[4]T = serre_D 2 H₃ + (1/6) * H₃ * (H₄ - H₂) = f₃
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  -- Now: serre_D 2 H₃ + (1/6) • H₃ * (H₄ - H₂) = f₃
  -- Key: H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄) * H₃
  unfold f₃
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  rw [show H₃ z = H₂ z + H₄ z by rw [← Pi.add_apply, (congrFun jacobi_identity z).symm]]
  ring_nf

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
    simp only [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  have h_H₂_2H₄ : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    simp only [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
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
  simp only [theta_g, add_slash, h_term1, h_term2]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply]; ring

/-- g is invariant under T.

Proof: Under T: H₂ ↦ -H₂, H₄ ↦ H₃, f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
g|T = (2(-H₂) + H₃)(-f₂) + ((-H₂) + 2H₃)(f₂ + f₄)
Using Jacobi: H₃ = H₂ + H₄, simplifies to g. -/
lemma theta_g_T_action : (theta_g ∣[(6 : ℤ)] T) = theta_g := by
  -- Under T: H₂ → -H₂, H₄ → H₃, f₂ → -f₂, f₄ → f₃
  -- Linear combination transforms: (2•H₂ + H₄)|T = -2•H₂ + H₃, (H₂ + 2•H₄)|T = -H₂ + 2•H₃
  have h_2H₂_H₄ : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = -(2 : ℂ) • H₂ + H₃ := by
    simp only [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action, smul_neg]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have h_H₂_2H₄ : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = -H₂ + (2 : ℂ) • H₃ := by
    simp only [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
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
  simp only [theta_g, add_slash, h_term1, h_term2]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  rw [(congrFun jacobi_identity z).symm, (congrFun f₂_add_f₄_eq_f₃ z).symm]
  simp only [Pi.add_apply]; ring

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
  simp only [theta_h, add_slash, h_f₂_sq, h_f₂f₄, h_f₄_sq]
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
  simp only [theta_h, add_slash, h_f₂_sq, h_f₂f₄, h_f₄_sq]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, sq]
  ring
