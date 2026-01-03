import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.DimensionFormulas

/-!
# Theta Derivative Error Terms and Slash Actions

This file defines error terms for the Serre derivative identities of Jacobi theta functions
H₂, H₃, H₄ (Blueprint Proposition 6.52) and establishes their S/T transformation rules.

## Contents

* Error terms `f₂`, `f₃`, `f₄` definitions
* MDifferentiable proofs for error terms
* Jacobi identity: `f₂ + f₄ = f₃`
* S/T transformation rules: `f₂_S_action`, `f₂_T_action`, `f₄_S_action`, `f₄_T_action`
* Helper lemmas for slash actions: `add_smul_slash`, `prod_slash_weight_4`, `serre_D_neg`

## Strategy

We define error terms f₂, f₃, f₄ = (LHS - RHS) and prove their transformation rules under
the S and T generators of SL(2,ℤ). The key results are:
- f₂|S = -f₄, f₂|T = -f₂
- f₄|S = -f₂, f₄|T = f₃

These transformation rules are used in subsequent files to construct level-1 invariants
and prove the error terms vanish.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

/-!
## Phase 1: Error Term Definitions
-/

/-- Error term for the ∂₂H₂ identity: f₂ = ∂₂H₂ - (1/6)(H₂² + 2H₂H₄) -/
noncomputable def f₂ : ℍ → ℂ := fun z =>
  serre_D 2 H₂ z - (1/6 : ℂ) * (H₂ z * (H₂ z + 2 * H₄ z))

/-- Error term for the ∂₂H₃ identity: f₃ = ∂₂H₃ - (1/6)(H₂² - H₄²) -/
noncomputable def f₃ : ℍ → ℂ := fun z =>
  serre_D 2 H₃ z - (1/6 : ℂ) * (H₂ z ^ 2 - H₄ z ^ 2)

/-- Error term for the ∂₂H₄ identity: f₄ = ∂₂H₄ + (1/6)(2H₂H₄ + H₄²) -/
noncomputable def f₄ : ℍ → ℂ := fun z =>
  serre_D 2 H₄ z + (1/6 : ℂ) * (H₄ z * (2 * H₂ z + H₄ z))

/-- f₂ decomposes as serre_D 2 H₂ + (-1/6) • (H₂ * (H₂ + 2*H₄)) -/
lemma f₂_decompose :
    f₂ = serre_D (2 : ℤ) H₂ + ((-1/6 : ℂ) • fun z => H₂ z * (H₂ z + 2 * H₄ z)) := by
  funext z; simp only [f₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf

/-- f₄ decomposes as serre_D 2 H₄ + (1/6) • (H₄ * (2*H₂ + H₄)) -/
lemma f₄_decompose :
    f₄ = serre_D (2 : ℤ) H₄ + ((1/6 : ℂ) • fun z => H₄ z * (2 * H₂ z + H₄ z)) := by
  funext z; simp only [f₄, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf

/-!
## Phase 2: MDifferentiable for Error Terms
-/

/-- f₂ is MDifferentiable -/
lemma f₂_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₂ := by
  unfold f₂
  apply MDifferentiable.sub
  · exact serre_D_differentiable H₂_SIF_MDifferentiable
  · apply MDifferentiable.mul
    · exact mdifferentiable_const
    · apply MDifferentiable.mul H₂_SIF_MDifferentiable
      apply MDifferentiable.add H₂_SIF_MDifferentiable
      apply MDifferentiable.mul mdifferentiable_const H₄_SIF_MDifferentiable

/-- f₃ is MDifferentiable -/
lemma f₃_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₃ := by
  unfold f₃
  apply MDifferentiable.sub
  · exact serre_D_differentiable H₃_SIF_MDifferentiable
  · apply MDifferentiable.mul
    · exact mdifferentiable_const
    · apply MDifferentiable.sub
      · simp only [pow_two]; exact H₂_SIF_MDifferentiable.mul H₂_SIF_MDifferentiable
      · simp only [pow_two]; exact H₄_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable

/-- f₄ is MDifferentiable -/
lemma f₄_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₄ := by
  unfold f₄
  apply MDifferentiable.add
  · exact serre_D_differentiable H₄_SIF_MDifferentiable
  · apply MDifferentiable.mul
    · exact mdifferentiable_const
    · apply MDifferentiable.mul H₄_SIF_MDifferentiable
      apply MDifferentiable.add
      · apply MDifferentiable.mul mdifferentiable_const H₂_SIF_MDifferentiable
      · exact H₄_SIF_MDifferentiable

/-!
## Phase 3-4: Jacobi Identity and Relation f₂ + f₄ = f₃
-/

/-- Jacobi identity: H₂ + H₄ = H₃ -/
-- This follows from jacobi_identity in JacobiTheta.lean (which has a sorry)
lemma jacobi_identity' (z : ℍ) : H₂ z + H₄ z = H₃ z := by
  have h := jacobi_identity z
  -- jacobi_identity says Θ₂^4 + Θ₄^4 = Θ₃^4, which is exactly H₂ + H₄ = H₃
  simp only [H₂, H₃, H₄] at h ⊢
  exact h

/-- The error terms satisfy f₂ + f₄ = f₃ (from Jacobi identity) -/
lemma f₂_add_f₄_eq_f₃ : ∀ z, f₂ z + f₄ z = f₃ z := by
  intro z
  simp only [f₂, f₃, f₄]
  -- Key relation: serre_D 2 H₂ z + serre_D 2 H₄ z = serre_D 2 H₃ z (via Jacobi identity)
  have h_serre : serre_D 2 H₂ z + serre_D 2 H₄ z = serre_D 2 H₃ z := by
    have add_eq := serre_D_add (2 : ℤ) H₂ H₄ H₂_SIF_MDifferentiable H₄_SIF_MDifferentiable
    have jacobi_eq : H₂ + H₄ = H₃ := by funext w; exact jacobi_identity' w
    have h := congrFun add_eq z
    simp only [Pi.add_apply] at h
    -- Use convert to handle the (2 : ℂ) vs ↑(2 : ℤ) issue
    convert h.symm using 2; rw [jacobi_eq]
  -- Now algebraic: use h_serre to simplify and close with ring
  have h_jacobi := jacobi_identity' z
  calc serre_D 2 H₂ z - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z)) +
       (serre_D 2 H₄ z + 1/6 * (H₄ z * (2 * H₂ z + H₄ z)))
      = (serre_D 2 H₂ z + serre_D 2 H₄ z) +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) -
         1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by ring
    _ = serre_D 2 H₃ z +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) -
         1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by rw [h_serre]
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

/-- Slash action distributes over addition + scalar multiplication -/
lemma add_smul_slash (k : ℤ) (M : SL(2, ℤ)) (f g : ℍ → ℂ) (c : ℂ) :
    (f + c • g) ∣[k] M = (f ∣[k] M) + c • (g ∣[k] M) := by
  rw [SlashAction.add_slash, SL_smul_slash]

/-- Product of weight-2 functions has weight-4 slash action -/
lemma prod_slash_weight_4 (M : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g) ∣[(4 : ℤ)] M = (f ∣[(2 : ℤ)] M) * (g ∣[(2 : ℤ)] M) := by
  have h4 : (4 : ℤ) = 2 + 2 := by norm_num
  rw [h4, mul_slash_SL2 2 2 M f g]

/-- serre_D k (-F) = -serre_D k F (linearity) -/
lemma serre_D_neg (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    serre_D k (-F) = -serre_D k F := by
  funext z; simpa using serre_D_smul k (-1) F hF z

/-- f₂ transforms under S as f₂|S = -f₄.

Proof outline using serre_D_slash_equivariant:
1. (serre_D 2 H₂)|[4]S = serre_D 2 (H₂|[2]S) = serre_D 2 (-H₄) = -serre_D 2 H₄
2. (H₂(H₂ + 2H₄))|[4]S = (-H₄)((-H₄) + 2(-H₂)) = H₄(H₄ + 2H₂)
3. f₂|[4]S = -serre_D 2 H₄ - (1/6)H₄(H₄ + 2H₂) = -f₄

Key lemmas used:
- serre_D_slash_equivariant: (serre_D k F)|[k+2]γ = serre_D k (F|[k]γ)
- serre_D_neg: serre_D k (-F) = -serre_D k F
- mul_slash_SL2: (f * g)|[k1+k2]A = (f|[k1]A) * (g|[k2]A)
- SlashAction.add_slash, smul_slash for linearity -/
lemma f₂_S_action : (f₂ ∣[(4 : ℤ)] S) = -f₄ := by
  have h_serre_neg := serre_D_neg (2 : ℤ) H₄ H₄_SIF_MDifferentiable
  -- Step 1: (serre_D 2 H₂)|[4]S = -serre_D 2 H₄ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₄ := by
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable S
    calc (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] S)
        = (serre_D (2 : ℤ) H₂ ∣[(2 + 2 : ℤ)] S) := by ring_nf
      _ = serre_D (2 : ℤ) (H₂ ∣[(2 : ℤ)] S) := h_equivariant
      _ = serre_D (2 : ℤ) (-H₄) := by rw [H₂_S_action]
      _ = -serre_D (2 : ℤ) H₄ := h_serre_neg
  -- Step 2: (H₂ + 2*H₄)|[2]S = -(H₄ + 2*H₂)
  have h_lin_comb : ((fun z => H₂ z + 2 * H₄ z) ∣[(2 : ℤ)] S) =
      fun z => -(H₄ z + 2 * H₂ z) := by
    have hfun1 : (fun z => H₂ z + 2 * H₄ z) = H₂ + ((2 : ℂ) • H₄) := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, add_smul_slash, H₂_S_action, H₄_S_action]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₂ * (H₂ + 2*H₄))|[4]S = H₄ * (H₄ + 2*H₂)
  have h_prod : ((fun z => H₂ z * (H₂ z + 2 * H₄ z)) ∣[(4 : ℤ)] S) =
      fun z => H₄ z * (H₄ z + 2 * H₂ z) := by
    have hfun : (fun z => H₂ z * (H₂ z + 2 * H₄ z)) =
        H₂ * (fun z => H₂ z + 2 * H₄ z) := by funext; simp [Pi.mul_apply]
    rw [hfun, prod_slash_weight_4, H₂_S_action, h_lin_comb]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]; ring
  -- Combine: f₂|[4]S = -serre_D 2 H₄ - (1/6) * H₄ * (2*H₂ + H₄) = -f₄
  rw [f₂_decompose, add_smul_slash, h_serre_term, h_prod]
  funext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, f₄]; ring_nf

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
  have h_serre_neg := serre_D_neg (2 : ℤ) H₂ H₂_SIF_MDifferentiable
  -- Step 1: (serre_D 2 H₂)|[4]T = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] T) = -serre_D (2 : ℤ) H₂ := by
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable T
    calc (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] T)
        = (serre_D (2 : ℤ) H₂ ∣[(2 + 2 : ℤ)] T) := by ring_nf
      _ = serre_D (2 : ℤ) (H₂ ∣[(2 : ℤ)] T) := h_equivariant
      _ = serre_D (2 : ℤ) (-H₂) := by rw [H₂_T_action]
      _ = -serre_D (2 : ℤ) H₂ := h_serre_neg
  -- Step 2: (H₂ + 2H₄)|[2]T = H₂ + 2H₄ using Jacobi: H₃ = H₂ + H₄
  -- -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
  have h_lin_comb : ((fun z => H₂ z + 2 * H₄ z) ∣[(2 : ℤ)] T) =
      fun z => H₂ z + 2 * H₄ z := by
    have hfun1 : (fun z => H₂ z + 2 * H₄ z) = H₂ + ((2 : ℂ) • H₄) := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, add_smul_slash, H₂_T_action, H₄_T_action]
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    -- -H₂ z + 2 * H₃ z = H₂ z + 2 * H₄ z using Jacobi
    have h_jacobi := jacobi_identity' z
    rw [← h_jacobi]; ring
  -- Step 3: Product (H₂ * (H₂ + 2H₄))|[4]T = (-H₂) * (H₂ + 2H₄)
  have h_prod : ((fun z => H₂ z * (H₂ z + 2 * H₄ z)) ∣[(4 : ℤ)] T) =
      fun z => (-H₂ z) * (H₂ z + 2 * H₄ z) := by
    have hfun : (fun z => H₂ z * (H₂ z + 2 * H₄ z)) =
        H₂ * (fun z => H₂ z + 2 * H₄ z) := by funext; simp [Pi.mul_apply]
    rw [hfun, prod_slash_weight_4, H₂_T_action, h_lin_comb]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]
  -- Combine: f₂|[4]T = -serre_D 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄) = -f₂
  rw [f₂_decompose, add_smul_slash, h_serre_term, h_prod]
  funext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring

/-- f₄ transforms under S as f₄|S = -f₂.

Proof outline (symmetric to f₂_S_action):
1. (serre_D 2 H₄)|[4]S = serre_D 2 (H₄|[2]S) = serre_D 2 (-H₂) = -serre_D 2 H₂
2. (H₄(2H₂ + H₄))|[4]S = (-H₂)(2(-H₄) + (-H₂)) = H₂(H₂ + 2H₄)
3. f₄|[4]S = -serre_D 2 H₂ + (1/6)H₂(H₂ + 2H₄) = -f₂ -/
lemma f₄_S_action : (f₄ ∣[(4 : ℤ)] S) = -f₂ := by
  have h_serre_neg := serre_D_neg (2 : ℤ) H₂ H₂_SIF_MDifferentiable
  -- Step 1: (serre_D 2 H₄)|[4]S = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₂ := by
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable S
    calc (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] S)
        = (serre_D (2 : ℤ) H₄ ∣[(2 + 2 : ℤ)] S) := by ring_nf
      _ = serre_D (2 : ℤ) (H₄ ∣[(2 : ℤ)] S) := h_equivariant
      _ = serre_D (2 : ℤ) (-H₂) := by rw [H₄_S_action]
      _ = -serre_D (2 : ℤ) H₂ := h_serre_neg
  -- Step 2: (2H₂ + H₄)|[2]S = -(2H₄ + H₂)
  have h_lin_comb : ((fun z => 2 * H₂ z + H₄ z) ∣[(2 : ℤ)] S) =
      fun z => -(2 * H₄ z + H₂ z) := by
    have h_smul := SL_smul_slash (2 : ℤ) S H₂ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) S ((2 : ℂ) • H₂) H₄
    have hfun1 : (fun z => 2 * H₂ z + H₄ z) = ((2 : ℂ) • H₂) + H₄ := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, H₂_S_action, H₄_S_action]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₄ * (2H₂ + H₄))|[4]S = H₂ * (H₂ + 2H₄)
  have h_prod : ((fun z => H₄ z * (2 * H₂ z + H₄ z)) ∣[(4 : ℤ)] S) =
      fun z => H₂ z * (H₂ z + 2 * H₄ z) := by
    have hfun : (fun z => H₄ z * (2 * H₂ z + H₄ z)) =
        H₄ * (fun z => 2 * H₂ z + H₄ z) := by funext; simp [Pi.mul_apply]
    rw [hfun, prod_slash_weight_4, H₄_S_action, h_lin_comb]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]; ring
  -- Combine: f₄|[4]S = -serre_D 2 H₂ + (1/6) * H₂ * (H₂ + 2H₄) = -f₂
  rw [f₄_decompose, add_smul_slash, h_serre_term, h_prod]
  funext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, f₂]; ring_nf

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
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable T
    calc (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] T)
        = (serre_D (2 : ℤ) H₄ ∣[(2 + 2 : ℤ)] T) := by ring_nf
      _ = serre_D (2 : ℤ) (H₄ ∣[(2 : ℤ)] T) := h_equivariant
      _ = serre_D (2 : ℤ) H₃ := by rw [H₄_T_action]
  -- Step 2: (2H₂ + H₄)|[2]T = H₄ - H₂ using Jacobi: H₃ = H₂ + H₄
  -- -2H₂ + H₃ = -2H₂ + (H₂ + H₄) = H₄ - H₂
  have h_lin_comb : ((fun z => 2 * H₂ z + H₄ z) ∣[(2 : ℤ)] T) =
      fun z => H₄ z - H₂ z := by
    have h_smul := SL_smul_slash (2 : ℤ) T H₂ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) T ((2 : ℂ) • H₂) H₄
    have hfun1 : (fun z => 2 * H₂ z + H₄ z) = ((2 : ℂ) • H₂) + H₄ := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, H₂_T_action, H₄_T_action]
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    have h_jacobi := jacobi_identity' z
    rw [← h_jacobi]; ring
  -- Step 3: Product (H₄ * (2H₂ + H₄))|[4]T = H₃ * (H₄ - H₂)
  have h_prod : ((fun z => H₄ z * (2 * H₂ z + H₄ z)) ∣[(4 : ℤ)] T) =
      fun z => H₃ z * (H₄ z - H₂ z) := by
    have hfun : (fun z => H₄ z * (2 * H₂ z + H₄ z)) =
        H₄ * (fun z => 2 * H₂ z + H₄ z) := by funext; simp [Pi.mul_apply]
    rw [hfun, prod_slash_weight_4, H₄_T_action, h_lin_comb]
    funext z; simp [Pi.mul_apply]
  -- Combine: f₄|[4]T = serre_D 2 H₃ + (1/6) * H₃ * (H₄ - H₂) = f₃
  rw [f₄_decompose, add_smul_slash, h_serre_term, h_prod]
  -- Now: serre_D 2 H₃ + (1/6) • (fun z => H₃ z * (H₄ z - H₂ z)) = f₃
  -- Key: H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄) * H₃
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, f₃]
  have h_jacobi := jacobi_identity' z
  -- Need: 1/6 * H₃ z * (H₄ z - H₂ z) = -1/6 * (H₂ z^2 - H₄ z^2)
  -- i.e., 1/6 * H₃ z * (H₄ z - H₂ z) = -1/6 * (H₂ z^2 - H₄ z^2)
  -- H₂ z^2 - H₄ z^2 = (H₂ z - H₄ z) * (H₂ z + H₄ z) = (H₂ z - H₄ z) * H₃ z
  have h_diff_sq : H₂ z ^ 2 - H₄ z ^ 2 = (H₂ z - H₄ z) * H₃ z := by
    -- H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄) * H₃ via Jacobi
    have h_factor : H₂ z ^ 2 - H₄ z ^ 2 = (H₂ z - H₄ z) * (H₂ z + H₄ z) := by ring
    rw [h_factor, h_jacobi]
  rw [h_diff_sq]
  ring_nf
