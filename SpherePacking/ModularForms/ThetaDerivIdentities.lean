import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.ModularForms.AtImInfty
import SpherePacking.ModularForms.EisensteinAsymptotics

/-!
# Theta Derivative Identities

This file proves the Serre derivative identities for Jacobi theta functions
(Blueprint Proposition 6.52, equations (32)–(34)):

* `serre_D_H₂` : serre_D 2 H₂ = (1/6) * (H₂² + 2*H₂*H₄)
* `serre_D_H₃` : serre_D 2 H₃ = (1/6) * (H₂² - H₄²)
* `serre_D_H₄` : serre_D 2 H₄ = -(1/6) * (2*H₂*H₄ + H₄²)

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

### Cusp Form Arguments (Phase 7)
* Tendsto lemmas for f₂, f₄, theta_g, theta_h at infinity
* Cusp form construction for theta_g and theta_h

### Dimension Vanishing (Phase 8)
* theta_g = 0 and theta_h = 0 by weight < 12 cusp form vanishing

### Main Deduction (Phase 9)
* f₂ = f₃ = f₄ = 0

### Main Theorems (Phase 10)
* serre_D_H₂, serre_D_H₃, serre_D_H₄

## Strategy

We define error terms f₂, f₃, f₄ = (LHS - RHS) and prove their transformation rules under
the S and T generators of SL(2,ℤ). The key results are:
- f₂|S = -f₄, f₂|T = -f₂
- f₄|S = -f₂, f₄|T = f₃

Using these transformation rules, we construct g and h such that g|S = g, g|T = g, h|S = h, h|T = h.
This makes g and h into level-1 (SL(2,ℤ)-invariant) modular forms.

We then show g and h vanish at infinity (Phase 7), hence are cusp forms. By dimension
vanishing (Phase 8), all level-1 cusp forms of weight < 12 are zero. This gives g = h = 0,
from which we deduce f₂ = f₃ = f₄ = 0 (Phase 9), yielding the main theorems (Phase 10).
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups CongruenceSubgroup

local notation "Γ " n:100 => Gamma n


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
lemma f₂_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₂ := by
  simp only [f₂]
  exact (serre_D_differentiable H₂_SIF_MDifferentiable).sub
    ((H₂_SIF_MDifferentiable.mul (H₂_SIF_MDifferentiable.add
      (H₄_SIF_MDifferentiable.const_smul _))).const_smul _)

/-- f₃ is MDifferentiable -/
lemma f₃_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₃ := by
  simp only [f₃, sq]
  exact (serre_D_differentiable H₃_SIF_MDifferentiable).sub
    (((H₂_SIF_MDifferentiable.mul H₂_SIF_MDifferentiable).sub
      (H₄_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable)).const_smul _)

/-- f₄ is MDifferentiable -/
lemma f₄_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₄ := by
  simp only [f₄]
  exact (serre_D_differentiable H₄_SIF_MDifferentiable).add
    ((H₄_SIF_MDifferentiable.mul
      ((H₂_SIF_MDifferentiable.const_smul _).add H₄_SIF_MDifferentiable)).const_smul _)

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

/-!
## Phase 7: Cusp Form Arguments

We need to show g and h vanish at infinity.
The tendsto lemmas for H₂, H₃, H₄ are already in AtImInfty.lean:
- H₂_tendsto_atImInfty : Tendsto H₂ atImInfty (𝓝 0)
- H₃_tendsto_atImInfty : Tendsto H₃ atImInfty (𝓝 1)
- H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 1)
-/

/-- theta_g is MDifferentiable (from MDifferentiable of f₂, f₄, H₂, H₄) -/
lemma theta_g_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) theta_g := by
  unfold theta_g
  apply MDifferentiable.add
  · apply MDifferentiable.mul
    · apply MDifferentiable.add
      · apply MDifferentiable.mul mdifferentiable_const H₂_SIF_MDifferentiable
      · exact H₄_SIF_MDifferentiable
    · exact f₂_MDifferentiable
  · apply MDifferentiable.mul
    · apply MDifferentiable.add H₂_SIF_MDifferentiable
      · apply MDifferentiable.mul mdifferentiable_const H₄_SIF_MDifferentiable
    · exact f₄_MDifferentiable

/-- theta_h is MDifferentiable (from MDifferentiable of f₂, f₄) -/
lemma theta_h_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) theta_h := by
  unfold theta_h
  apply MDifferentiable.add
  · apply MDifferentiable.add
    · simp only [pow_two]; exact f₂_MDifferentiable.mul f₂_MDifferentiable
    · exact f₂_MDifferentiable.mul f₄_MDifferentiable
  · simp only [pow_two]; exact f₄_MDifferentiable.mul f₄_MDifferentiable

/-- theta_g is slash-invariant under Γ(1) in GL₂(ℝ) form -/
lemma theta_g_slash_invariant_GL :
    ∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 1),
    theta_g ∣[(6 : ℤ)] γ = theta_g :=
  slashaction_generators_GL2R theta_g 6 theta_g_S_action theta_g_T_action

/-- theta_h is slash-invariant under Γ(1) in GL₂(ℝ) form -/
lemma theta_h_slash_invariant_GL :
    ∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 1),
    theta_h ∣[(8 : ℤ)] γ = theta_h :=
  slashaction_generators_GL2R theta_h 8 theta_h_S_action theta_h_T_action

/-- theta_g as a SlashInvariantForm of level 1 -/
noncomputable def theta_g_SIF : SlashInvariantForm (Γ 1) 6 where
  toFun := theta_g
  slash_action_eq' := theta_g_slash_invariant_GL

/-- theta_h as a SlashInvariantForm of level 1 -/
noncomputable def theta_h_SIF : SlashInvariantForm (Γ 1) 8 where
  toFun := theta_h
  slash_action_eq' := theta_h_slash_invariant_GL

/-- D f → 0 at infinity for bounded holomorphic functions.
Uses Cauchy estimate: ‖D f z‖ ≤ M/(π·z.im) → 0 as im(z) → ∞. -/
lemma D_tendsto_zero_atImInfty {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    Tendsto (D f) atImInfty (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  rw [isBoundedAtImInfty_iff] at hbdd
  obtain ⟨M, A, hMA⟩ := hbdd
  intro ε hε
  rw [Filter.eventually_atImInfty]
  -- For im(z) ≥ max(2*max(A,0)+1, M/(π*ε)+1), we have ‖D f z‖ < ε
  use max (2 * max A 0 + 1) (M / (π * ε) + 1)
  intro z hz
  have hz_large : z.im ≥ 2 * max A 0 + 1 := le_trans (le_max_left _ _) hz
  have hz_half_gt_A : z.im / 2 > max A 0 := by linarith
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  -- Cauchy estimate gives ‖D f z‖ ≤ M/(π·z.im)
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hf_bdd_sphere : ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im := hclosed (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ = z.im / 2 := hdist
    have hw_im_ge_A : A ≤ w.im := by
      have hlower : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
      linarith [le_max_left A 0]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw_im_pos]
    exact hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  have hD_bound := norm_D_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
  -- Now show M/(π·z.im) < ε using hz
  have hz_im_large : z.im > M / (π * ε) := by
    have := le_trans (le_max_right (2 * max A 0 + 1) _) hz
    linarith
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) (hMA z (by linarith [le_max_left A 0]))
  rw [dist_zero_right]
  -- Handle M = 0 case separately (norm is 0, which is < ε)
  rcases hM_nonneg.eq_or_lt with hM_zero | hM_pos
  · rw [← hM_zero, zero_div] at hD_bound
    exact lt_of_le_of_lt hD_bound hε
  · have h_simpl : M / (π * (M / (π * ε))) = ε := by field_simp
    calc ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) := hD_bound
      _ = M / (π * z.im) := by ring
      _ < M / (π * (M / (π * ε))) := by
          apply div_lt_div_of_pos_left hM_pos (by positivity)
          exact mul_lt_mul_of_pos_left hz_im_large Real.pi_pos
      _ = ε := h_simpl

/-- If D F → 0 and F → c, then serre_D k F → -k/12 * c.
Uses E₂_tendsto_one_atImInfty to compute E₂ * F → c. -/
lemma serre_D_tendsto_of_tendsto {k : ℤ} {F : ℍ → ℂ} {c : ℂ}
    (hD : Tendsto (D F) atImInfty (𝓝 0))
    (hF : Tendsto F atImInfty (𝓝 c)) :
    Tendsto (serre_D k F) atImInfty (𝓝 (-(k : ℂ) / 12 * c)) := by
  -- serre_D k F = D F - k/12 * E₂ * F
  -- D F → 0, E₂ → 1, F → c, so serre_D k F → 0 - k/12 * 1 * c = -k/12 * c
  have hE₂_F : Tendsto (fun z => E₂ z * F z) atImInfty (𝓝 c) := by
    simpa [one_mul] using E₂_tendsto_one_atImInfty.mul hF
  have h_coef : Tendsto (fun z => (k : ℂ) * 12⁻¹ * E₂ z * F z) atImInfty
      (𝓝 ((k : ℂ) / 12 * c)) := by
    convert hE₂_F.const_mul ((k : ℂ) * 12⁻¹) using 2
    ring
  convert hD.sub h_coef using 2
  simp only [div_eq_mul_inv]
  ring

/-- f₂ tends to 0 at infinity.
Proof: f₂ = serre_D 2 H₂ - (1/6)H₂(H₂ + 2H₄)
Since H₂ → 0 and serre_D 2 H₂ = D H₂ - (1/6)E₂ H₂ → 0,
we get f₂ → 0 - 0 = 0. -/
lemma f₂_tendsto_atImInfty : Tendsto f₂ atImInfty (𝓝 0) := by
  have hH₂ := H₂_tendsto_atImInfty
  have hH₄ := H₄_tendsto_atImInfty
  have hD_H₂ := D_tendsto_zero_atImInfty H₂_SIF_MDifferentiable isBoundedAtImInfty_H₂
  have h_serre_H₂ : Tendsto (serre_D 2 H₂) atImInfty (𝓝 0) := by
    simpa using serre_D_tendsto_of_tendsto hD_H₂ hH₂
  have h_prod : Tendsto (fun z => H₂ z * (H₂ z + 2 * H₄ z)) atImInfty (𝓝 0) := by
    simpa using hH₂.mul (hH₂.add (hH₄.const_mul 2))
  have h_final := h_serre_H₂.sub (h_prod.const_mul (1/6 : ℂ))
  simp only [mul_zero, sub_zero] at h_final
  convert h_final using 1

/-- f₄ tends to 0 at infinity.
Proof: f₄ = serre_D 2 H₄ + (1/6)H₄(2H₂ + H₄)
serre_D 2 H₄ = D H₄ - (1/6)E₂ H₄ → 0 - (1/6)*1*1 = -1/6 (since H₄ → 1, E₂ → 1)
H₄(2H₂ + H₄) → 1*(0 + 1) = 1
So f₄ → -1/6 + (1/6)*1 = 0. -/
lemma f₄_tendsto_atImInfty : Tendsto f₄ atImInfty (𝓝 0) := by
  have hH₂ := H₂_tendsto_atImInfty
  have hH₄ := H₄_tendsto_atImInfty
  have hD_H₄ := D_tendsto_zero_atImInfty H₄_SIF_MDifferentiable isBoundedAtImInfty_H₄
  have h_serre_H₄ : Tendsto (serre_D 2 H₄) atImInfty (𝓝 (-(1/6 : ℂ))) := by
    convert serre_D_tendsto_of_tendsto hD_H₄ hH₄ using 2; norm_num
  have h_sum : Tendsto (fun z => 2 * H₂ z + H₄ z) atImInfty (𝓝 1) := by
    simpa using (hH₂.const_mul 2).add hH₄
  have h_prod : Tendsto (fun z => H₄ z * (2 * H₂ z + H₄ z)) atImInfty (𝓝 1) := by
    simpa using hH₄.mul h_sum
  have h_scaled : Tendsto (fun z => (1/6 : ℂ) * (H₄ z * (2 * H₂ z + H₄ z)))
      atImInfty (𝓝 (1/6 : ℂ)) := by simpa using h_prod.const_mul (1/6 : ℂ)
  have h_final := h_serre_H₄.add h_scaled
  simp only [neg_add_cancel] at h_final
  convert h_final using 1

/-- theta_g tends to 0 at infinity.
theta_g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄.
Since 2H₂ + H₄ → 1, H₂ + 2H₄ → 2, and f₂, f₄ → 0, we get theta_g → 0. -/
lemma theta_g_tendsto_atImInfty : Tendsto theta_g atImInfty (𝓝 0) := by
  have hH₂ := H₂_tendsto_atImInfty
  have hH₄ := H₄_tendsto_atImInfty
  have hf₂ := f₂_tendsto_atImInfty
  have hf₄ := f₄_tendsto_atImInfty
  have h_coef1 : Tendsto (fun z => 2 * H₂ z + H₄ z) atImInfty (𝓝 1) := by
    simpa using (hH₂.const_mul 2).add hH₄
  have h_coef2 : Tendsto (fun z => H₂ z + 2 * H₄ z) atImInfty (𝓝 2) := by
    simpa using hH₂.add (hH₄.const_mul 2)
  have h_term1 : Tendsto (fun z => (2 * H₂ z + H₄ z) * f₂ z) atImInfty (𝓝 0) := by
    simpa using h_coef1.mul hf₂
  have h_term2 : Tendsto (fun z => (H₂ z + 2 * H₄ z) * f₄ z) atImInfty (𝓝 0) := by
    simpa using h_coef2.mul hf₄
  have hsum := h_term1.add h_term2
  simp only [add_zero] at hsum
  convert hsum using 1

/-- theta_h tends to 0 at infinity.
theta_h = f₂² + f₂f₄ + f₄² → 0 + 0 + 0 = 0 as f₂, f₄ → 0. -/
lemma theta_h_tendsto_atImInfty : Tendsto theta_h atImInfty (𝓝 0) := by
  have hf₂ := f₂_tendsto_atImInfty
  have hf₄ := f₄_tendsto_atImInfty
  have h_f₂_sq : Tendsto (fun z => f₂ z ^ 2) atImInfty (𝓝 0) := by simpa [sq] using hf₂.mul hf₂
  have h_f₄_sq : Tendsto (fun z => f₄ z ^ 2) atImInfty (𝓝 0) := by simpa [sq] using hf₄.mul hf₄
  have h_f₂f₄ : Tendsto (fun z => f₂ z * f₄ z) atImInfty (𝓝 0) := by simpa using hf₂.mul hf₄
  have hsum := (h_f₂_sq.add h_f₂f₄).add h_f₄_sq
  simp only [add_zero] at hsum
  convert hsum using 1

/-- Build a cusp form from a SlashInvariantForm that's MDifferentiable and
tends to zero at infinity. This pattern is reused for theta_g and theta_h. -/
lemma IsCuspForm_of_SIF_tendsto_zero {k : ℤ}
    (f_SIF : SlashInvariantForm (Γ 1) k)
    (h_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f_SIF.toFun)
    (h_zero : Tendsto f_SIF.toFun atImInfty (𝓝 0)) :
    ∃ (f_MF : ModularForm (Γ 1) k),
    IsCuspForm (Γ 1) k f_MF ∧ ∀ z, f_MF z = f_SIF.toFun z := by
  -- Use slash invariance to show zero at all cusps
  have h_zero_at_cusps :
      ∀ {c : OnePoint ℝ}, IsCusp c (Γ 1) → c.IsZeroAt f_SIF.toFun k := by
    intro c hc
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    have h_inv := f_SIF.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩
    rw [h_inv]
    exact h_zero
  -- Construct CuspForm
  let f_CF : CuspForm (Γ 1) k := {
    toSlashInvariantForm := f_SIF
    holo' := h_mdiff
    zero_at_cusps' := fun hc => h_zero_at_cusps hc
  }
  let f_MF := CuspForm_to_ModularForm (Γ 1) k f_CF
  exact ⟨f_MF, ⟨⟨f_CF, rfl⟩, fun _ => rfl⟩⟩

/-- g is a cusp form of level 1. -/
lemma theta_g_IsCuspForm :
    ∃ (g_MF : ModularForm (Γ 1) 6),
      IsCuspForm (Γ 1) 6 g_MF ∧ ∀ z, g_MF z = theta_g z :=
  IsCuspForm_of_SIF_tendsto_zero theta_g_SIF theta_g_MDifferentiable theta_g_tendsto_atImInfty

/-- h is a cusp form of level 1. -/
lemma theta_h_IsCuspForm :
    ∃ (h_MF : ModularForm (Γ 1) 8),
      IsCuspForm (Γ 1) 8 h_MF ∧ ∀ z, h_MF z = theta_h z :=
  IsCuspForm_of_SIF_tendsto_zero theta_h_SIF theta_h_MDifferentiable theta_h_tendsto_atImInfty

/-!
## Phase 8: Apply Dimension Vanishing
-/

/-- g = 0 by dimension argument.

Proof: g is a level-1 cusp form of weight 6. By IsCuspForm_weight_lt_eq_zero,
all cusp forms of weight < 12 vanish. Hence g = 0. -/
lemma theta_g_eq_zero : theta_g = 0 := by
  obtain ⟨g_MF, hg_cusp, hg_eq⟩ := theta_g_IsCuspForm
  have hzero := IsCuspForm_weight_lt_eq_zero 6 (by norm_num : (6 : ℤ) < 12) g_MF hg_cusp
  funext z
  rw [← hg_eq z, hzero]
  rfl

/-- h = 0 by dimension argument.

Proof: h is a level-1 cusp form of weight 8. By IsCuspForm_weight_lt_eq_zero,
all cusp forms of weight < 12 vanish. Hence h = 0. -/
lemma theta_h_eq_zero : theta_h = 0 := by
  obtain ⟨h_MF, hh_cusp, hh_eq⟩ := theta_h_IsCuspForm
  have hzero := IsCuspForm_weight_lt_eq_zero 8 (by norm_num : (8 : ℤ) < 12) h_MF hh_cusp
  funext z
  rw [← hh_eq z, hzero]
  rfl

/-!
## H_sum_sq: H₂² + H₂H₄ + H₄²
-/

/-- H₂² + H₂H₄ + H₄² -/
noncomputable def H_sum_sq : ℍ → ℂ := fun z => H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2

/-- H_sum_sq is MDifferentiable -/
lemma H_sum_sq_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H_sum_sq := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₂ z ^ 2) := by
    simpa [sq] using H₂_SIF_MDifferentiable.mul H₂_SIF_MDifferentiable
  have h2 := H₂_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable
  have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₄ z ^ 2) := by
    simpa [sq] using H₄_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable
  exact (h1.add h2).add h3

/-- H_sum_sq → 1 at infinity -/
lemma H_sum_sq_tendsto : Tendsto H_sum_sq atImInfty (𝓝 1) := by
  have h_H₂ := H₂_tendsto_atImInfty
  have h_H₄ := H₄_tendsto_atImInfty
  have h1 : Tendsto (fun z => H₂ z ^ 2) atImInfty (𝓝 0) := by simpa [sq] using h_H₂.mul h_H₂
  have h2 : Tendsto (fun z => H₂ z * H₄ z) atImInfty (𝓝 0) := by simpa using h_H₂.mul h_H₄
  have h3 : Tendsto (fun z => H₄ z ^ 2) atImInfty (𝓝 1) := by simpa [sq] using h_H₄.mul h_H₄
  simpa [zero_add, add_zero] using (h1.add h2).add h3

/-- H_sum_sq ≠ 0 (since it tends to 1 ≠ 0) -/
lemma H_sum_sq_ne_zero : H_sum_sq ≠ 0 := fun h =>
  one_ne_zero (tendsto_nhds_unique tendsto_const_nhds (h ▸ H_sum_sq_tendsto)).symm

/-- 3 * H_sum_sq ≠ 0 -/
lemma three_H_sum_sq_ne_zero : (fun z => 3 * H_sum_sq z) ≠ 0 := by
  intro h
  apply H_sum_sq_ne_zero
  funext z
  exact (mul_eq_zero.mp (congrFun h z)).resolve_left (by norm_num)

/-- 3 * H_sum_sq is MDifferentiable -/
lemma three_H_sum_sq_MDifferentiable :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 3 * H_sum_sq z) :=
  mdifferentiable_const.mul H_sum_sq_MDifferentiable

/-!
## Phase 9: Deduce f₂ = f₃ = f₄ = 0
-/

/-- Key algebraic identity for proving f₂ = f₄ = 0.
Given Af₂ + Bf₄ = 0, we have f₄² * (A² - AB + B²) = A² * (f₂² + f₂f₄ + f₄²). -/
lemma f₄_sq_mul_eq (z : ℍ) (hg_z : theta_g z = 0) :
    f₄ z ^ 2 * (3 * H_sum_sq z) = (2 * H₂ z + H₄ z) ^ 2 * theta_h z := by
  unfold H_sum_sq
  -- Define A = 2H₂ + H₄, B = H₂ + 2H₄
  set A := 2 * H₂ z + H₄ z with hA
  set B := H₂ z + 2 * H₄ z with hB
  -- From theta_g = 0: A * f₂ + B * f₄ = 0
  have h_Af₂_eq : A * f₂ z + B * f₄ z = 0 := by
    simp only [theta_g, hA, hB, smul_eq_mul, Pi.smul_apply, Pi.mul_apply, Pi.add_apply] at hg_z ⊢
    linear_combination hg_z
  -- Af₂ = -Bf₄
  have hAf₂ : A * f₂ z = -(B * f₄ z) := by linear_combination h_Af₂_eq
  -- A²f₂² = B²f₄²
  have h1 : A ^ 2 * f₂ z ^ 2 = B ^ 2 * f₄ z ^ 2 := by
    have h_sq : (A * f₂ z) ^ 2 = (B * f₄ z) ^ 2 := by rw [hAf₂]; ring
    calc A ^ 2 * f₂ z ^ 2 = (A * f₂ z) ^ 2 := by ring
      _ = (B * f₄ z) ^ 2 := h_sq
      _ = B ^ 2 * f₄ z ^ 2 := by ring
  -- A²f₂f₄ = -ABf₄²
  have h2 : A ^ 2 * (f₂ z * f₄ z) = -(A * B * f₄ z ^ 2) := by
    calc A ^ 2 * (f₂ z * f₄ z) = (A * f₂ z) * (A * f₄ z) := by ring
      _ = (-(B * f₄ z)) * (A * f₄ z) := by rw [hAf₂]
      _ = -(A * B * f₄ z ^ 2) := by ring
  -- A² - AB + B² = 3(H₂² + H₂H₄ + H₄²)
  have h_sum : A ^ 2 - A * B + B ^ 2 = 3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2) := by
    simp only [hA, hB]; ring
  -- Now compute A²θₕ
  unfold theta_h
  calc f₄ z ^ 2 * (3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2))
      = f₄ z ^ 2 * (A ^ 2 - A * B + B ^ 2) := by rw [h_sum]
    _ = B ^ 2 * f₄ z ^ 2 + (-(A * B * f₄ z ^ 2)) + A ^ 2 * f₄ z ^ 2 := by ring
    _ = A ^ 2 * f₂ z ^ 2 + A ^ 2 * (f₂ z * f₄ z) + A ^ 2 * f₄ z ^ 2 := by rw [h1, h2]
    _ = A ^ 2 * (f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) := by ring

/-- From g = 0 and h = 0, deduce f₂ = 0.

Proof: We have two equations:
1. g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ = 0
2. h = f₂² + f₂f₄ + f₄² = 0

From (1): f₄ = -((2H₂ + H₄)/(H₂ + 2H₄)) * f₂ (where H₂ + 2H₄ ≠ 0 generically)

Substituting into (2) and simplifying gives f₂² times a non-zero expression = 0.
Since holomorphic functions have isolated zeros or are identically zero,
and f₂ is holomorphic on all of ℍ, we get f₂ = 0.

Alternative approach: Use that 3(H₂² + H₂H₄ + H₄²) = 3E₄ (blueprint identity).
Then 3E₄ · h = 0 with E₄ having invertible q-series implies h-summand relations
that force f₂ = f₄ = 0. -/
lemma f₂_eq_zero : f₂ = 0 := by
  have hg := theta_g_eq_zero
  have hh := theta_h_eq_zero
  -- Show f₄ = 0 first, then f₂ = 0 follows from theta_h = f₂² = 0
  suffices hf₄ : f₄ = 0 by
    funext z
    have hz := congrFun hh z
    unfold theta_h at hz
    simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.zero_apply, hf₄] at hz
    simpa [sq_eq_zero_iff] using hz
  -- From f₄_sq_mul_eq and theta_h = 0: f₄² * (3 * H_sum_sq) = 0
  have h_f₄_sq_3H : f₄ ^ 2 * (fun z => 3 * H_sum_sq z) = 0 := by
    ext z
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    have hh_z : theta_h z = 0 := congrFun hh z
    calc f₄ z ^ 2 * (3 * H_sum_sq z)
        = (2 * H₂ z + H₄ z) ^ 2 * theta_h z := f₄_sq_mul_eq z (congrFun hg z)
      _ = _ := by rw [hh_z, mul_zero]
  -- f₄² is MDifferentiable
  have f₄_sq_MDiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f₄ ^ 2) := by
    simpa [sq] using f₄_MDifferentiable.mul f₄_MDifferentiable
  -- By mul_eq_zero_iff: f₄² = 0 (since 3 * H_sum_sq ≠ 0)
  have h_f₄_sq_zero : f₄ ^ 2 = 0 :=
    ((UpperHalfPlane.mul_eq_zero_iff f₄_sq_MDiff three_H_sum_sq_MDifferentiable).mp h_f₄_sq_3H
      ).resolve_right three_H_sum_sq_ne_zero
  -- From f₄² = f₄ * f₄ = 0: f₄ = 0
  have h_f₄_mul : f₄ * f₄ = 0 := by convert h_f₄_sq_zero using 1; ext z; exact (sq (f₄ z)).symm
  exact (UpperHalfPlane.mul_eq_zero_iff f₄_MDifferentiable f₄_MDifferentiable).mp h_f₄_mul
    |>.elim id id

/-- From f₂ = 0 and h = 0, deduce f₄ = 0 -/
lemma f₄_eq_zero : f₄ = 0 := by
  funext z
  have hz := congrFun theta_h_eq_zero z
  unfold theta_h at hz
  simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.zero_apply, f₂_eq_zero] at hz
  simpa [sq_eq_zero_iff] using hz

/-- From f₂ + f₄ = f₃ and both = 0, f₃ = 0 -/
lemma f₃_eq_zero : f₃ = 0 := by
  rw [← f₂_add_f₄_eq_f₃]
  simp [f₂_eq_zero, f₄_eq_zero]

/-!
## Phase 10: Main Theorems
-/

/-- Serre derivative of H₂: ∂₂H₂ = (1/6)(H₂² + 2H₂H₄) -/
theorem serre_D_H₂ :
    serre_D 2 H₂ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 + 2 * H₂ z * H₄ z) := by
  funext z
  have := congrFun f₂_eq_zero z
  simp only [f₂, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.add_apply,
    smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  convert this using 1; ring

/-- Serre derivative of H₃: ∂₂H₃ = (1/6)(H₂² - H₄²) -/
theorem serre_D_H₃ : serre_D 2 H₃ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 - H₄ z ^ 2) := by
  funext z
  have := congrFun f₃_eq_zero z
  simp only [f₃, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply,
    smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- Serre derivative of H₄: ∂₂H₄ = -(1/6)(2H₂H₄ + H₄²) -/
theorem serre_D_H₄ :
    serre_D 2 H₄ = fun z => -(1/6 : ℂ) * (2 * H₂ z * H₄ z + H₄ z ^ 2) := by
  funext z
  have := congrFun f₄_eq_zero z
  simp only [f₄, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, Pi.zero_apply, add_eq_zero_iff_eq_neg] at this
  convert this using 1; ring
