module
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.ModularForms.Derivative
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.ModularForms.Lv1Lv2Identities
import SpherePacking.Tactic.FunPropExt

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

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
  ModularForm SlashAction MatrixGroups

private lemma four_eq_two_add_two : (4 : ℤ) = 2 + 2 := rfl

private lemma H₃_eq_H₂_add_H₄ (z : ℍ) : H₃ z = H₂ z + H₄ z := by
  simpa [Pi.add_apply] using (congrFun jacobi_identity z).symm

attribute [local fun_prop] serre_D_differentiable mdifferentiable_H₂ mdifferentiable_H₃
  mdifferentiable_H₄

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
lemma f₂_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₂ := by simpa [f₂] using (by fun_prop)

/-- f₃ is MDifferentiable -/
lemma f₃_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₃ := by simpa [f₃] using (by fun_prop)

/-- f₄ is MDifferentiable -/
lemma f₄_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₄ := by simpa [f₄] using (by fun_prop)

attribute [local fun_prop] f₂_MDifferentiable f₃_MDifferentiable f₄_MDifferentiable

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
  simp only [one_div, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul,
    Pi.pow_apply]
  rw [h_serre.symm]
  ring_nf

/-!
## Phase 5: S/T Transformation Rules for f₂, f₄

These transformations depend on `serre_D_slash_equivariant`.
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
@[grind =]
lemma f₂_S_action : (f₂ ∣[(4 : ℤ)] S) = -f₄ := by
  -- Step 1: (serre_D 2 H₂)|[4]S = -serre_D 2 H₄ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₄ := by
    rw [four_eq_two_add_two,
        serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable S, H₂_S_action]
    simpa using serre_D_smul 2 (-1) H₄
  -- Step 2: (H₂ + 2•H₄)|[2]S = -(H₄ + 2•H₂)
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    rw [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z
    simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
    ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]S = H₄ * (H₄ + 2•H₂)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] S) = H₄ * (H₄ + (2 : ℂ) • H₂) := by
    rw [four_eq_two_add_two, mul_slash_SL2 2 2 S _ _, H₂_S_action, h_lin_comb]
    exact neg_mul_neg H₄ (H₄ + 2 • H₂)
  -- Combine: f₂|[4]S = -serre_D 2 H₄ - (1/6) * H₄ * (2*H₂ + H₄) = -f₄
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  ext z
  simp [f₄, smul_eq_mul]
  ring

/-- f₂ transforms under T as f₂|T = -f₂.

Proof outline:
1. (serre_D 2 H₂)|[4]T = serre_D 2 (H₂|[2]T) = serre_D 2 (-H₂) = -serre_D 2 H₂
2. (H₂(H₂ + 2H₄))|[4]T = (-H₂)((-H₂) + 2H₃)
   Using Jacobi H₃ = H₂ + H₄: -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
   So: (H₂(H₂ + 2H₄))|[4]T = (-H₂)(H₂ + 2H₄)
3. f₂|[4]T = -serre_D 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄)
           = -serre_D 2 H₂ + (1/6)H₂(H₂ + 2H₄)
           = -(serre_D 2 H₂ - (1/6)H₂(H₂ + 2H₄)) = -f₂ -/
@[grind =]
lemma f₂_T_action : (f₂ ∣[(4 : ℤ)] T) = -f₂ := by
  -- Step 1: (serre_D 2 H₂)|[4]T = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] T) = -serre_D (2 : ℤ) H₂ := by
    rw [four_eq_two_add_two,
        serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable T, H₂_T_action]
    simpa using serre_D_smul 2 (-1) H₂
  -- Step 2: (H₂ + 2•H₄)|[2]T = H₂ + 2•H₄ using Jacobi: H₃ = H₂ + H₄
  -- -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = H₂ + (2 : ℂ) • H₄ := by
    rw [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    simp [H₃_eq_H₂_add_H₄]
    ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]T = (-H₂) * (H₂ + 2•H₄)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] T) = -H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [four_eq_two_add_two, mul_slash_SL2 2 2 T _ _, H₂_T_action, h_lin_comb]
  -- Combine: f₂|[4]T = -serre_D 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄) = -f₂
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- f₄ transforms under S as f₄|S = -f₂.

Proof outline (symmetric to f₂_S_action):
1. (serre_D 2 H₄)|[4]S = serre_D 2 (H₄|[2]S) = serre_D 2 (-H₂) = -serre_D 2 H₂
2. (H₄(2H₂ + H₄))|[4]S = (-H₂)(2(-H₄) + (-H₂)) = H₂(H₂ + 2H₄)
3. f₄|[4]S = -serre_D 2 H₂ + (1/6)H₂(H₂ + 2H₄) = -f₂ -/
@[grind =]
lemma f₄_S_action : (f₄ ∣[(4 : ℤ)] S) = -f₂ := by
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₂ := by
    rw [four_eq_two_add_two, serre_D_slash_equivariant (2 : ℤ) H₄ mdifferentiable_H₄ S, H₄_S_action]
    simpa using serre_D_smul 2 (-1) H₂
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] S) = H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [four_eq_two_add_two, mul_slash_SL2 2 2 S _ _, H₄_S_action, add_slash,
      SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  ext z
  simp [f₂, smul_eq_mul]
  ring

/-- f₄ transforms under T as f₄|T = f₃.

Proof outline:
1. (serre_D 2 H₄)|[4]T = serre_D 2 (H₄|[2]T) = serre_D 2 H₃
2. (H₄(2H₂ + H₄))|[4]T = H₃(2(-H₂) + H₃) = H₃(H₃ - 2H₂)
   Using Jacobi H₃ = H₂ + H₄: H₃ - 2H₂ = H₄ - H₂
3. f₄|[4]T = serre_D 2 H₃ + (1/6)H₃(H₃ - 2H₂)
   But H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄)H₃
   So (1/6)(H₂² - H₄²) = -(1/6)H₃(H₄ - H₂) = -(1/6)H₃(H₃ - 2H₂)
   Thus f₃ = serre_D 2 H₃ - (1/6)(H₂² - H₄²) = f₄|[4]T -/
@[grind =]
lemma f₄_T_action : (f₄ ∣[(4 : ℤ)] T) = f₃ := by
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] T) = serre_D (2 : ℤ) H₃ := by
    rw [four_eq_two_add_two, serre_D_slash_equivariant (2 : ℤ) H₄ mdifferentiable_H₄ T, H₄_T_action]
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = H₄ - H₂ := by
    rw [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z
    simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul, H₃_eq_H₂_add_H₄]
    ring
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, four_eq_two_add_two,
    mul_slash_SL2 2 2 T _ _, H₄_T_action, h_lin_comb]
  ext z
  simp [f₃, smul_eq_mul, H₃_eq_H₂_add_H₄]
  ring

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
  ext z
  simp [theta_g, add_slash, mul_slash_SL2_2_4, H₂_S_action, H₄_S_action, f₂_S_action, f₄_S_action,
    smul_eq_mul]
  ring

/-- g is invariant under T.

Proof: Under T: H₂ ↦ -H₂, H₄ ↦ H₃, f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
g|T = (2(-H₂) + H₃)(-f₂) + ((-H₂) + 2H₃)(f₂ + f₄)
Using Jacobi: H₃ = H₂ + H₄, simplifies to g. -/
lemma theta_g_T_action : (theta_g ∣[(6 : ℤ)] T) = theta_g := by
  ext z
  have hJ : H₃ z = H₂ z + H₄ z := H₃_eq_H₂_add_H₄ z
  have hf3 : f₃ z = f₂ z + f₄ z := (congrFun f₂_add_f₄_eq_f₃ z).symm
  simp [theta_g, add_slash, mul_slash_SL2_2_4, H₂_T_action, H₄_T_action, f₂_T_action, f₄_T_action,
    smul_eq_mul, hJ, hf3]
  ring

-- Helper: avoid `k1+k2` ambiguity when rewriting slashes of products.
private lemma mul_slash_SL2_4_4 (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g) ∣[(8 : ℤ)] A = f ∣[(4 : ℤ)] A * g ∣[(4 : ℤ)] A := by
  simpa using (ModularForm.mul_slash_SL2 (k1 := 4) (k2 := 4) A f g)

/-- h is invariant under S.

Proof: h = f₂² + f₂f₄ + f₄²
Under S: f₂|[4]S = -f₄, f₄|[4]S = -f₂
Using mul_slash_SL2: (f₂²)|[8]S = (f₂|[4]S)² = (-f₄)² = f₄²
                     (f₂f₄)|[8]S = (f₂|[4]S)(f₄|[4]S) = (-f₄)(-f₂) = f₂f₄
                     (f₄²)|[8]S = (f₄|[4]S)² = (-f₂)² = f₂²
So h|[8]S = f₄² + f₂f₄ + f₂² = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_S_action : (theta_h ∣[(8 : ℤ)] S) = theta_h := by
  ext z
  simp [theta_h, pow_two, add_slash, mul_slash_SL2_4_4, f₂_S_action, f₄_S_action]
  ring

/-- h is invariant under T.

Proof: Under T: f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
h|T = (-f₂)² + (-f₂)(f₂ + f₄) + (f₂ + f₄)²
    = f₂² - f₂² - f₂f₄ + f₂² + 2f₂f₄ + f₄²
    = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_T_action : (theta_h ∣[(8 : ℤ)] T) = theta_h := by
  ext z
  have hf3 : f₃ z = f₂ z + f₄ z := (congrFun f₂_add_f₄_eq_f₃ z).symm
  simp [theta_h, pow_two, add_slash, mul_slash_SL2_4_4, f₂_T_action, f₄_T_action, hf3]
  ring

/-!
## Phase 7: Vanishing of the error terms

We show that the level-1 invariants `theta_g` (weight 6) and `theta_h` (weight 8) are cusp forms
by checking that they tend to `0` at `i∞`. Since there are no nonzero level-1 cusp forms of weight
`< 12`, we conclude `theta_g = theta_h = 0`. We then deduce `f₂ = f₃ = f₄ = 0`, i.e. the Serre
derivative identities of Blueprint Proposition `prop:theta-der`.
-/

local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

lemma tendsto_D_H₂_atImInfty : Tendsto (D H₂) atImInfty (𝓝 (0 : ℂ)) := by
  simpa [UpperHalfPlane.IsZeroAtImInfty, ZeroAtFilter] using
    D_isZeroAtImInfty_of_bounded H₂_SIF_MDifferentiable
      (by simpa using ModularFormClass.bdd_at_infty H₂_MF)

lemma tendsto_D_H₄_atImInfty : Tendsto (D H₄) atImInfty (𝓝 (0 : ℂ)) := by
  simpa [UpperHalfPlane.IsZeroAtImInfty, ZeroAtFilter] using
    D_isZeroAtImInfty_of_bounded H₄_SIF_MDifferentiable
      (by simpa using ModularFormClass.bdd_at_infty H₄_MF)

lemma tendsto_serre_D_H₂_atImInfty : Tendsto (serre_D 2 H₂) atImInfty (𝓝 (0 : ℂ)) := by
  have hD : Tendsto (D H₂) atImInfty (𝓝 (0 : ℂ)) := tendsto_D_H₂_atImInfty
  have hE2H2 : Tendsto (fun z : ℍ => E₂ z * H₂ z) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using tendsto_E₂_atImInfty.mul H₂_tendsto_atImInfty
  have h12 : Tendsto (fun z : ℍ => (12⁻¹ : ℂ) * (E₂ z * H₂ z)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hE2H2)
  have hterm :
      Tendsto (fun z : ℍ => (2 : ℂ) * ((12⁻¹ : ℂ) * (E₂ z * H₂ z))) atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_assoc] using (tendsto_const_nhds.mul h12)
  have hserre :
      serre_D 2 H₂ = fun z : ℍ => D H₂ z - (2 : ℂ) * ((12⁻¹ : ℂ) * (E₂ z * H₂ z)) := by
    funext z
    simp [serre_D, mul_assoc]
  simpa [hserre] using hD.sub hterm

lemma tendsto_serre_D_H₄_atImInfty : Tendsto (serre_D 2 H₄) atImInfty (𝓝 (-(1 / 6 : ℂ))) := by
  have hD : Tendsto (D H₄) atImInfty (𝓝 (0 : ℂ)) := tendsto_D_H₄_atImInfty
  have hE2H4 : Tendsto (fun z : ℍ => E₂ z * H₄ z) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using tendsto_E₂_atImInfty.mul H₄_tendsto_atImInfty
  have h12 : Tendsto (fun z : ℍ => (12⁻¹ : ℂ) * (E₂ z * H₄ z)) atImInfty (𝓝 (12⁻¹ : ℂ)) := by
    simpa [mul_one] using (tendsto_const_nhds.mul hE2H4)
  have hterm :
      Tendsto
        (fun z : ℍ => (2 : ℂ) * ((12⁻¹ : ℂ) * (E₂ z * H₄ z)))
        atImInfty (𝓝 ((2 : ℂ) * 12⁻¹)) := by
    simpa [mul_assoc] using (tendsto_const_nhds.mul h12)
  have hserre :
      serre_D 2 H₄ = fun z : ℍ => D H₄ z - (2 : ℂ) * ((12⁻¹ : ℂ) * (E₂ z * H₄ z)) := by
    funext z
    simp [serre_D, mul_assoc]
  have hmain :
      Tendsto (fun z : ℍ => D H₄ z - (2 : ℂ) * ((12⁻¹ : ℂ) * (E₂ z * H₄ z)))
        atImInfty (𝓝 (-((2 : ℂ) * 12⁻¹))) := by
    simpa [mul_assoc, sub_eq_add_neg, add_assoc] using hD.sub hterm
  have hmain' : Tendsto (serre_D 2 H₄) atImInfty (𝓝 (-((2 : ℂ) * 12⁻¹))) := by
    simpa [hserre] using hmain
  have hk : -((2 : ℂ) * 12⁻¹) = (-(1 / 6 : ℂ)) := by norm_num
  simpa [hk] using hmain'

lemma f₂_tendsto_atImInfty : Tendsto f₂ atImInfty (𝓝 (0 : ℂ)) := by
  have hlin : Tendsto (H₂ + (2 : ℂ) • H₄) atImInfty (𝓝 (2 : ℂ)) := by
    simpa using
      H₂_tendsto_atImInfty.add
        ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ))).smul
          H₄_tendsto_atImInfty)
  have hpoly : Tendsto (H₂ * (H₂ + (2 : ℂ) • H₄)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using H₂_tendsto_atImInfty.mul hlin
  have hsmul :
      Tendsto ((1 / 6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 / 6 : ℂ)) atImInfty (𝓝 (1 / 6 : ℂ))).smul
        hpoly)
  simpa [f₂] using tendsto_serre_D_H₂_atImInfty.sub hsmul

lemma f₄_tendsto_atImInfty : Tendsto f₄ atImInfty (𝓝 (0 : ℂ)) := by
  have hlin : Tendsto ((2 : ℂ) • H₂ + H₄) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ))).smul
            H₂_tendsto_atImInfty).add
        H₄_tendsto_atImInfty
  have hpoly : Tendsto (H₄ * ((2 : ℂ) • H₂ + H₄)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using H₄_tendsto_atImInfty.mul hlin
  have hsmul :
      Tendsto ((1 / 6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))) atImInfty (𝓝 (1 / 6 : ℂ)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 / 6 : ℂ)) atImInfty (𝓝 (1 / 6 : ℂ))).smul
        hpoly)
  simpa [f₄, add_assoc] using tendsto_serre_D_H₄_atImInfty.add hsmul

lemma theta_g_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) theta_g := by
  simpa [theta_g, add_assoc, mul_assoc] using
    (by fun_prop :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((2 : ℂ) • H₂ + H₄) * f₂ + (H₂ + (2 : ℂ) • H₄) * f₄))

lemma theta_h_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) theta_h := by
  simpa [theta_h, add_assoc] using
    (by fun_prop :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f₂ ^ 2 + f₂ * f₄ + f₄ ^ 2))

lemma theta_g_tendsto_atImInfty : Tendsto theta_g atImInfty (𝓝 (0 : ℂ)) := by
  have hlin1 : Tendsto ((2 : ℂ) • H₂ + H₄) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ))).smul
            H₂_tendsto_atImInfty).add
        H₄_tendsto_atImInfty
  have hlin2 : Tendsto (H₂ + (2 : ℂ) • H₄) atImInfty (𝓝 (2 : ℂ)) := by
    simpa using
      H₂_tendsto_atImInfty.add
        ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ))).smul
          H₄_tendsto_atImInfty)
  have hterm1 : Tendsto (((2 : ℂ) • H₂ + H₄) * f₂) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using hlin1.mul f₂_tendsto_atImInfty
  have hterm2 : Tendsto ((H₂ + (2 : ℂ) • H₄) * f₄) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using hlin2.mul f₄_tendsto_atImInfty
  simpa [theta_g, add_assoc] using hterm1.add hterm2

lemma theta_h_tendsto_atImInfty : Tendsto theta_h atImInfty (𝓝 (0 : ℂ)) := by
  have hf2 : Tendsto f₂ atImInfty (𝓝 (0 : ℂ)) := f₂_tendsto_atImInfty
  have hf4 : Tendsto f₄ atImInfty (𝓝 (0 : ℂ)) := f₄_tendsto_atImInfty
  simpa [theta_h, add_assoc] using ((hf2.pow 2).add (hf2.mul hf4)).add (hf4.pow 2)

lemma isBoundedAtImInfty_theta_g : IsBoundedAtImInfty theta_g :=
  IsZeroAtImInfty.isBoundedAtImInfty theta_g_tendsto_atImInfty

lemma isBoundedAtImInfty_theta_h : IsBoundedAtImInfty theta_h :=
  IsZeroAtImInfty.isBoundedAtImInfty theta_h_tendsto_atImInfty

noncomputable def theta_g_SIF : SlashInvariantForm (Γ 1) 6 where
  toFun := theta_g
  slash_action_eq' := slashaction_generators_GL2R theta_g 6 theta_g_S_action theta_g_T_action

noncomputable def theta_h_SIF : SlashInvariantForm (Γ 1) 8 where
  toFun := theta_h
  slash_action_eq' := slashaction_generators_GL2R theta_h 8 theta_h_S_action theta_h_T_action

lemma theta_g_slash_eq (A' : SL(2, ℤ)) :
    theta_g ∣[(6 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ A') = theta_g := by
  simpa [ModularForm.SL_slash] using
    (slashaction_generators_SL2Z theta_g 6 theta_g_S_action theta_g_T_action A')

lemma theta_h_slash_eq (A' : SL(2, ℤ)) :
    theta_h ∣[(8 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ A') = theta_h := by
  simpa [ModularForm.SL_slash] using
    (slashaction_generators_SL2Z theta_h 8 theta_h_S_action theta_h_T_action A')

noncomputable def theta_g_MF : ModularForm (Γ 1) 6 := {
  theta_g_SIF with
  holo' := theta_g_MDifferentiable
  bdd_at_cusps' := fun hc =>
    bounded_at_cusps_of_bounded_at_infty hc
      (isBoundedAtImInfty_slash_of_slash_eq theta_g_slash_eq isBoundedAtImInfty_theta_g)
}

noncomputable def theta_h_MF : ModularForm (Γ 1) 8 := {
  theta_h_SIF with
  holo' := theta_h_MDifferentiable
  bdd_at_cusps' := fun hc =>
    bounded_at_cusps_of_bounded_at_infty hc
      (isBoundedAtImInfty_slash_of_slash_eq theta_h_slash_eq isBoundedAtImInfty_theta_h)
}

lemma theta_g_eq_zero : theta_g = 0 := by
  have hzero : IsCuspForm (Γ 1) 6 theta_g_MF := by
    rw [IsCuspForm_iff_coeffZero_eq_zero, ModularFormClass.qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    exact UpperHalfPlane.IsZeroAtImInfty.cuspFunction_apply_zero theta_g_tendsto_atImInfty
      (by norm_num : (0 : ℝ) < 1)
  have hMF : theta_g_MF = 0 := IsCuspForm_weight_lt_eq_zero 6 (by norm_num) theta_g_MF hzero
  simpa [theta_g_MF, theta_g_SIF] using congrArg (·.toFun) hMF

lemma theta_h_eq_zero : theta_h = 0 := by
  have hzero : IsCuspForm (Γ 1) 8 theta_h_MF := by
    rw [IsCuspForm_iff_coeffZero_eq_zero, ModularFormClass.qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    exact UpperHalfPlane.IsZeroAtImInfty.cuspFunction_apply_zero theta_h_tendsto_atImInfty
      (by norm_num : (0 : ℝ) < 1)
  have hMF : theta_h_MF = 0 := IsCuspForm_weight_lt_eq_zero 8 (by norm_num) theta_h_MF hzero
  simpa [theta_h_MF, theta_h_SIF] using congrArg (·.toFun) hMF

lemma E₄_mul_f₂_sq_eq_zero : (fun z : ℍ => (E₄ z) * (f₂ z) ^ 2) = 0 := by
  funext z
  have hg : theta_g z = 0 := by simpa using congrFun theta_g_eq_zero z
  have hh : theta_h z = 0 := by simpa using congrFun theta_h_eq_zero z
  set A : ℂ := 2 * H₂ z + H₄ z
  set B : ℂ := H₂ z + 2 * H₄ z
  set x : ℂ := f₂ z
  set y : ℂ := f₄ z
  have h1 : A * x + B * y = 0 := by
    simpa [theta_g, A, B, x, y, smul_eq_mul, Pi.add_apply, Pi.mul_apply] using hg
  have h2 : x ^ 2 + x * y + y ^ 2 = 0 := by
    simpa [theta_h, x, y, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using hh
  have hlin : (B ^ 2 - A * B + A ^ 2) * (x ^ 2) = 0 := by
    grind only
  have hpoly : (B ^ 2 - A * B + A ^ 2) = 3 * E₄ z := by
    have hE4 : E₄ z = (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2) := by
      have h := congrFun SpherePacking.ModularForms.E₄_eq_thetaE4 z
      simpa [SpherePacking.ModularForms.thetaE4, pow_two, mul_assoc, mul_left_comm, mul_comm]
        using h
    have : (B ^ 2 - A * B + A ^ 2) = 3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2) := by
      simp [A, B, pow_two, mul_comm]
      ring
    simpa [hE4] using this
  simp_all

lemma f₂_eq_zero : f₂ = 0 := by
  have hmul0 := E₄_mul_f₂_sq_eq_zero
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hU_open : IsOpen U := isOpen_upperHalfPlaneSet
  have hU_pre : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_im_gt (r := (0 : ℝ))).isPreconnected
  have hDiffE4 : DifferentiableOn ℂ (fun z : ℂ => E₄ (ofComplex z)) U :=
    fun z hz => (MDifferentiableAt_DifferentiableAt (E₄.holo' ⟨z, hz⟩)).differentiableWithinAt
  have hDiffF2 : DifferentiableOn ℂ (fun z : ℂ => f₂ (ofComplex z)) U :=
    fun z hz =>
      (MDifferentiableAt_DifferentiableAt (f₂_MDifferentiable ⟨z, hz⟩)).differentiableWithinAt
  have hfE4 : AnalyticOnNhd ℂ (fun z : ℂ => E₄ (ofComplex z)) U :=
    hDiffE4.analyticOnNhd hU_open
  have hgF2 : AnalyticOnNhd ℂ (fun z : ℂ => (f₂ (ofComplex z)) ^ 2) U :=
    (hDiffF2.pow 2).analyticOnNhd hU_open
  have hfg : ∀ z ∈ U, (E₄ (ofComplex z)) * (f₂ (ofComplex z)) ^ 2 = 0 := by
    intro z hz
    simpa using congrArg (fun f : ℍ → ℂ => f (ofComplex z)) hmul0
  rcases
      AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (U := U) hfE4 hgF2 hfg hU_pre with
    hE4zero | hF2sq
  · have hE4 : (E₄ : ℍ → ℂ) = 0 := by
      funext τ
      have : E₄ (ofComplex (τ : ℂ)) = 0 := hE4zero _ τ.im_pos
      simpa [ofComplex_apply_of_im_pos τ.im_pos] using this
    have hlim1 : Tendsto (fun _ : ℍ => (0 : ℂ)) atImInfty (𝓝 (1 : ℂ)) := by
      have h :=
        (SpherePacking.ModularForms.tendsto_E₄_atImInfty : Tendsto E₄ atImInfty (𝓝 (1 : ℂ)))
      rw [hE4] at h
      exact h
    have : (1 : ℂ) = 0 :=
      tendsto_nhds_unique hlim1
        (tendsto_const_nhds : Tendsto (fun _ : ℍ => (0 : ℂ)) atImInfty (𝓝 (0 : ℂ)))
    exact False.elim ((one_ne_zero : (1 : ℂ) ≠ 0) this)
  · funext τ
    have : (f₂ (ofComplex (τ : ℂ))) ^ 2 = 0 := hF2sq _ τ.im_pos
    simpa

lemma analyticOnNhd_H₂_add_two_mul_H₄ :
    AnalyticOnNhd ℂ
      (fun z : ℂ => H₂ (ofComplex z) + (2 : ℂ) * H₄ (ofComplex z)) {z : ℂ | 0 < z.im} := by
  refine
    (?_ :
        DifferentiableOn ℂ
          (fun z : ℂ => H₂ (ofComplex z) + (2 : ℂ) * H₄ (ofComplex z)) {z : ℂ | 0 < z.im})
      |>.analyticOnNhd isOpen_upperHalfPlaneSet
  intro z hz
  simpa [mul_assoc] using
    (MDifferentiableAt_DifferentiableAt (H₂_SIF_MDifferentiable ⟨z, hz⟩)).differentiableWithinAt.add
      ((MDifferentiableAt_DifferentiableAt (H₄_SIF_MDifferentiable ⟨z, hz⟩)).differentiableWithinAt
        |>.const_mul (2 : ℂ))

lemma analyticOnNhd_f₄ :
    AnalyticOnNhd ℂ (fun z : ℂ => f₄ (ofComplex z)) {z : ℂ | 0 < z.im} := by
  refine
    ((?_ : DifferentiableOn ℂ (fun z : ℂ => f₄ (ofComplex z)) {z : ℂ | 0 < z.im})).analyticOnNhd
      isOpen_upperHalfPlaneSet
  intro z hz
  exact (MDifferentiableAt_DifferentiableAt (f₄_MDifferentiable ⟨z, hz⟩)).differentiableWithinAt

lemma f₄_eq_zero : f₄ = 0 := by
  have hBf4 : (H₂ + (2 : ℂ) • H₄) * f₄ = 0 := by
    simpa [theta_g, f₂_eq_zero] using (theta_g_eq_zero : theta_g = 0)
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hU_pre : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_im_gt (r := (0 : ℝ))).isPreconnected
  have hfB : AnalyticOnNhd ℂ (fun z : ℂ => H₂ (ofComplex z) + (2 : ℂ) * H₄ (ofComplex z)) U := by
    simpa [U] using analyticOnNhd_H₂_add_two_mul_H₄
  have hgF4 : AnalyticOnNhd ℂ (fun z : ℂ => f₄ (ofComplex z)) U := by
    simpa [U] using analyticOnNhd_f₄
  have hfg :
      ∀ z ∈ U,
        (H₂ (ofComplex z) + (2 : ℂ) * H₄ (ofComplex z)) * f₄ (ofComplex z) = 0 := by
    intro z hz
    simpa [smul_eq_mul, Pi.add_apply, Pi.mul_apply, mul_assoc] using
      congrArg (fun f : ℍ → ℂ => f (ofComplex z)) hBf4
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (U := U) hfB hgF4 hfg hU_pre with
    hBzero | hF4zero
  · exfalso
    have hB : (fun τ : ℍ => H₂ τ + (2 : ℂ) * H₄ τ) = 0 := by
      funext τ
      simpa [ofComplex_apply_of_im_pos τ.im_pos] using hBzero (τ : ℂ) τ.im_pos
    have hlim : Tendsto (fun τ : ℍ => H₂ τ + (2 : ℂ) * H₄ τ) atImInfty (𝓝 (2 : ℂ)) := by
      simpa [mul_assoc] using
        H₂_tendsto_atImInfty.add (tendsto_const_nhds.mul H₄_tendsto_atImInfty)
    rw [hB] at hlim
    exact
      (two_ne_zero : (2 : ℂ) ≠ 0) <|
        tendsto_nhds_unique hlim
          (tendsto_const_nhds : Tendsto (fun _ : ℍ => (0 : ℂ)) atImInfty (𝓝 (0 : ℂ)))
  · funext τ
    simpa [ofComplex_apply_of_im_pos τ.im_pos] using hF4zero _ τ.im_pos

lemma f₃_eq_zero : f₃ = 0 := by
  simpa [f₂_eq_zero, f₄_eq_zero] using (f₂_add_f₄_eq_f₃).symm

/-- Serre derivative identity for `H₂` (Blueprint Proposition 6.52). -/
public theorem serre_D_two_H₂ :
    serre_D 2 H₂ = (1 / 6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄)) := by
  exact sub_eq_zero.mp (by simpa [f₂] using (f₂_eq_zero : f₂ = 0))

public theorem serre_D_two_H₃ :
    serre_D 2 H₃ = (1 / 6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2) := by
  exact sub_eq_zero.mp (by simpa [f₃] using (f₃_eq_zero : f₃ = 0))

/-- Serre derivative identity for `H₄` (Blueprint Proposition 6.52). -/
public theorem serre_D_two_H₄ :
    serre_D 2 H₄ = (-1 / 6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄)) := by
  have h0 := (f₄_eq_zero : f₄ = 0)
  dsimp [f₄] at h0
  have h : serre_D 2 H₄ = -((6 : ℂ)⁻¹ • (H₄ * ((2 : ℂ) • H₂ + H₄))) := by
    simpa using (eq_neg_of_add_eq_zero_left h0)
  have h' : serre_D 2 H₄ = (-( (6 : ℂ)⁻¹)) • (H₄ * ((2 : ℂ) • H₂ + H₄)) := by
    simpa [neg_smul] using h
  have hk : (-( (6 : ℂ)⁻¹)) = (-1 / 6 : ℂ) := by norm_num
  simpa [hk] using h'
