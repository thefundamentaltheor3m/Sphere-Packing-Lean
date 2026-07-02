module

public import SpherePacking.ModularForms.JacobiTheta.JacobiIdentity
public import SpherePacking.ModularForms.Derivative
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ForMathlib.AtImInfty
public import SpherePacking.ModularForms.EisensteinAsymptotics
public import SpherePacking.Tactic.TendstoCont

@[expose] public section

/-!
# Derivatives of the Jacobi theta functions

This file proves the Serre derivative identities for the Jacobi theta functions `H₂`, `H₃`, `H₄`
(Blueprint Proposition 6.52, equations (32)–(34)).

## Main results

* `serre_D_H₂` : `serre_D 2 H₂ = (1/6) * (H₂ ^ 2 + 2 * H₂ * H₄)`
* `serre_D_H₃` : `serre_D 2 H₃ = (1/6) * (H₂ ^ 2 - H₄ ^ 2)`
* `serre_D_H₄` : `serre_D 2 H₄ = -(1/6) * (2 * H₂ * H₄ + H₄ ^ 2)`
* `D_H₂`, `D_H₃`, `D_H₄` : the corresponding formulas for the ordinary derivative `D`
* `E₄_eq_H_sum_sq` : `E₄ = H₂ ^ 2 + H₂ * H₄ + H₄ ^ 2`

## Proof strategy

Let `f₂`, `f₃`, `f₄` be the differences of the two sides of the three Serre derivative
identities. The Jacobi identity gives `f₂ + f₄ = f₃`, and the transformation rules of
`H₂`, `H₃`, `H₄` under the generators `S`, `T` of `SL(2, ℤ)` yield
`f₂ ∣[4] S = -f₄`, `f₂ ∣[4] T = -f₂`, `f₄ ∣[4] S = -f₂`, `f₄ ∣[4] T = f₃`. Hence

* `theta_g = (2 * H₂ + H₄) * f₂ + (H₂ + 2 * H₄) * f₄` (weight 6) and
* `theta_h = f₂ ^ 2 + f₂ * f₄ + f₄ ^ 2` (weight 8)

are `SL(2, ℤ)`-invariant. They vanish at infinity, so they are level-1 cusp forms of weight
less than 12, hence zero. From `theta_g = theta_h = 0` we deduce `f₂ = f₃ = f₄ = 0`.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups CongruenceSubgroup

local notation "Γ " n:100 => Gamma n


/-!
## The error terms `f₂`, `f₃`, `f₄`
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

/-- f₂ is MDifferentiable -/
lemma f₂_MDifferentiable : MDiff f₂ := by unfold f₂; fun_prop

/-- f₃ is MDifferentiable -/
lemma f₃_MDifferentiable : MDiff f₃ := by unfold f₃; fun_prop

/-- f₄ is MDifferentiable -/
lemma f₄_MDifferentiable : MDiff f₄ := by unfold f₄; fun_prop

/-- The error terms satisfy `f₂ + f₄ = f₃`, by the Jacobi identity `H₂ + H₄ = H₃`. -/
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
## Transformation of the error terms under S and T

The transformation rules follow from `serre_D_slash_equivariant` together with the
`S`/`T`-transformation rules of `H₂`, `H₃`, `H₄`.
-/

/-- `f₂` transforms under `S` as `f₂ ∣[4] S = -f₄`. -/
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

/-- `f₂` transforms under `T` as `f₂ ∣[4] T = -f₂`. -/
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

/-- `f₄` transforms under `S` as `f₄ ∣[4] S = -f₂`. -/
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

/-- `f₄` transforms under `T` as `f₄ ∣[4] T = f₃`. -/
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
## The invariants `theta_g` and `theta_h`
-/

/-- Level-1 invariant of weight 6: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ -/
noncomputable def theta_g : ℍ → ℂ := ((2 : ℂ) • H₂ + H₄) * f₂ + (H₂ + (2 : ℂ) • H₄) * f₄

/-- Level-1 invariant of weight 8: h = f₂² + f₂f₄ + f₄² -/
noncomputable def theta_h : ℍ → ℂ := f₂ ^ 2 + f₂ * f₄ + f₄ ^ 2

/-- `theta_g` is invariant under `S`. -/
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

/-- `theta_g` is invariant under `T`. -/
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

/-- `theta_h` is invariant under `S`. -/
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

/-- `theta_h` is invariant under `T`. -/
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
## Vanishing of `theta_g` and `theta_h`

Both invariants extend to cusp forms of level 1 and weight less than 12, hence vanish.
-/

/-- theta_g is MDifferentiable -/
lemma theta_g_MDifferentiable : MDiff theta_g := by rw [theta_g, f₂, f₄]; fun_prop

/-- theta_h is MDifferentiable -/
lemma theta_h_MDifferentiable : MDiff theta_h := by rw [theta_h, f₂, f₄]; fun_prop

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

/-- `f₂` tends to `0` at infinity, since `H₂ → 0`. -/
lemma f₂_tendsto_atImInfty : Tendsto f₂ atImInfty (𝓝 0) := by
  have h_serre_H₂ := serre_D_tendsto_zero_of_tendsto_zero 2 H₂
    H₂_SIF_MDifferentiable isBoundedAtImInfty_H₂ H₂_tendsto_atImInfty
  have h_prod : Tendsto (fun z ↦ H₂ z * (H₂ z + 2 * H₄ z)) atImInfty (𝓝 0) := by
    tendsto_cont [H₂_tendsto_atImInfty, H₄_tendsto_atImInfty]
  simpa [f₂] using h_serre_H₂.sub (h_prod.const_mul (1/6 : ℂ))

/-- `f₄` tends to `0` at infinity: `serre_D 2 H₄ → -1/6` cancels against
`(1/6) * H₄ * (2 * H₂ + H₄) → 1/6`. -/
lemma f₄_tendsto_atImInfty : Tendsto f₄ atImInfty (𝓝 0) := by
  have h_serre_H₄ : Tendsto (serre_D 2 H₄) atImInfty (𝓝 (-(1/6 : ℂ))) := by
    convert serre_D_tendsto_neg_k_div_12 2 H₄ H₄_SIF_MDifferentiable isBoundedAtImInfty_H₄
      H₄_tendsto_atImInfty using 2
    norm_num
  have h_scaled : Tendsto (fun z ↦ (1/6 : ℂ) * (H₄ z * (2 * H₂ z + H₄ z)))
      atImInfty (𝓝 (1/6 : ℂ)) := by
    tendsto_cont [H₂_tendsto_atImInfty, H₄_tendsto_atImInfty]
  simpa [f₄] using h_serre_H₄.add h_scaled

/-- `theta_g` tends to `0` at infinity. -/
lemma theta_g_tendsto_atImInfty : Tendsto theta_g atImInfty (𝓝 0) := by
  change Tendsto (fun z ↦ (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z)
    atImInfty (𝓝 0)
  tendsto_cont [H₂_tendsto_atImInfty, H₄_tendsto_atImInfty, f₂_tendsto_atImInfty,
    f₄_tendsto_atImInfty]

/-- `theta_h` tends to `0` at infinity. -/
lemma theta_h_tendsto_atImInfty : Tendsto theta_h atImInfty (𝓝 0) := by
  change Tendsto (fun z ↦ f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) atImInfty (𝓝 0)
  tendsto_cont [f₂_tendsto_atImInfty, f₄_tendsto_atImInfty]

private noncomputable def theta_g_CF : CuspForm (Γ 1) 6 :=
  cuspFormOfSIFTendstoZero theta_g_SIF theta_g_MDifferentiable theta_g_tendsto_atImInfty

private noncomputable def theta_h_CF : CuspForm (Γ 1) 8 :=
  cuspFormOfSIFTendstoZero theta_h_SIF theta_h_MDifferentiable theta_h_tendsto_atImInfty

/-- `theta_g = 0`, since level-1 cusp forms of weight 6 vanish. -/
lemma theta_g_eq_zero : theta_g = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 6 (by norm_num)) theta_g_CF)

/-- `theta_h = 0`, since level-1 cusp forms of weight 8 vanish. -/
lemma theta_h_eq_zero : theta_h = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 8 (by norm_num)) theta_h_CF)

/-!
## The identity `E₄ = H₂² + H₂H₄ + H₄²`

`E₄` and `H_sum_sq = H₂ ^ 2 + H₂ * H₄ + H₄ ^ 2` are weight-4 level-1 modular forms tending
to `1` at infinity, so their difference is a cusp form of weight 4, hence zero.
-/

/-- H₂² + H₂H₄ + H₄² -/
noncomputable def H_sum_sq : ℍ → ℂ := fun z ↦ H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2

/-- H_sum_sq is MDifferentiable -/
lemma H_sum_sq_MDifferentiable : MDiff H_sum_sq := by
  unfold H_sum_sq
  exact ((H₂_SIF_MDifferentiable.pow 2).add (H₂_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable)).add
    (H₄_SIF_MDifferentiable.pow 2)

/-- H_sum_sq → 1 at infinity -/
lemma H_sum_sq_tendsto : Tendsto H_sum_sq atImInfty (𝓝 1) := by
  unfold H_sum_sq
  tendsto_cont [H₂_tendsto_atImInfty, H₄_tendsto_atImInfty]

/-- H_sum_sq ≠ 0 (since it tends to 1 ≠ 0) -/
lemma H_sum_sq_ne_zero : H_sum_sq ≠ 0 :=
  ne_zero_of_tendsto_ne_zero one_ne_zero H_sum_sq_tendsto

/-- 3 * H_sum_sq ≠ 0 -/
lemma three_H_sum_sq_ne_zero : (fun z ↦ 3 * H_sum_sq z) ≠ 0 :=
  fun h ↦ H_sum_sq_ne_zero
    (funext fun z ↦ (mul_eq_zero.mp (congrFun h z)).resolve_left (by norm_num))

/-- 3 * H_sum_sq is MDifferentiable -/
lemma three_H_sum_sq_MDifferentiable : MDiff (fun z ↦ 3 * H_sum_sq z) :=
  mdifferentiable_const.mul H_sum_sq_MDifferentiable

/-- `H_sum_sq` is invariant under `S`. -/
private lemma H_sum_sq_S_action : (H_sum_sq ∣[(4 : ℤ)] S) = H_sum_sq := by
  have h_eq : H_sum_sq = H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by
    ext z; simp [H_sum_sq, sq]
  simp only [h_eq, show (4 : ℤ) = 2 + 2 from by norm_num,
    SlashAction.add_slash, mul_slash_SL2 2 2 S _ _, H₂_S_action, H₄_S_action]
  ext z; simp [Pi.mul_apply, Pi.add_apply]; ring

/-- `H_sum_sq` is invariant under `T`. -/
private lemma H_sum_sq_T_action : (H_sum_sq ∣[(4 : ℤ)] T) = H_sum_sq := by
  have h_eq : H_sum_sq = H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by
    ext z; simp [H_sum_sq, sq]
  simp only [h_eq, show (4 : ℤ) = 2 + 2 from by norm_num,
    SlashAction.add_slash, mul_slash_SL2 2 2 T _ _, H₂_T_action, H₄_T_action, ← jacobi_identity]
  ext z; simp [Pi.mul_apply, Pi.add_apply]; ring

private lemma H_sum_sq_SL2Z_invariant :
    ∀ γ : SL(2, ℤ), H_sum_sq ∣[(4 : ℤ)] γ = H_sum_sq :=
  slashaction_generators_SL2Z H_sum_sq 4 H_sum_sq_S_action H_sum_sq_T_action

private lemma isBoundedAtImInfty_H_sum_sq : IsBoundedAtImInfty H_sum_sq := by
  have : H_sum_sq = H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by ext z; simp [H_sum_sq, sq]
  rw [this]
  exact ((isBoundedAtImInfty_H₂.mul isBoundedAtImInfty_H₂).add
    (isBoundedAtImInfty_H₂.mul isBoundedAtImInfty_H₄)).add
    (isBoundedAtImInfty_H₄.mul isBoundedAtImInfty_H₄)

private noncomputable def H_sum_sq_SIF : SlashInvariantForm (Γ 1) 4 where
  toFun := H_sum_sq
  slash_action_eq' := slashaction_generators_GL2R H_sum_sq 4 H_sum_sq_S_action H_sum_sq_T_action

private noncomputable def H_sum_sq_MF : ModularForm (Γ 1) 4 := {
  H_sum_sq_SIF with
  holo' := H_sum_sq_MDifferentiable
  bdd_at_cusps' := fun hc ↦ bounded_at_cusps_of_bounded_at_infty hc fun A ⟨A', hA⟩ ↦ by
    rw [← hA]; simpa [SL_slash] using H_sum_sq_SL2Z_invariant A' ▸ isBoundedAtImInfty_H_sum_sq
}

/-- `E₄ = H₂ ^ 2 + H₂ * H₄ + H₄ ^ 2`. -/
theorem E₄_eq_H_sum_sq : _root_.E₄.toFun = H_sum_sq := by
  have h_toFun : (_root_.E₄ - H_sum_sq_MF).toFun = _root_.E₄.toFun - H_sum_sq := by
    ext z; simp [H_sum_sq_MF, H_sum_sq_SIF]; rfl
  have h_diff_tendsto : Tendsto (_root_.E₄ - H_sum_sq_MF).toFun atImInfty (nhds 0) := by
    rw [h_toFun]; simpa using E₄_tendsto_one_atImInfty.sub H_sum_sq_tendsto
  have h_cusp : IsCuspForm (Γ 1) 4 (_root_.E₄ - H_sum_sq_MF) := by
    rw [IsCuspForm_iff_coeffZero_eq_zero, qExpansion_coeff]; simp
    exact IsZeroAtImInfty.cuspFunction_apply_zero h_diff_tendsto (by norm_num : (0 : ℝ) < 1)
  have h_zero := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) (_root_.E₄ - H_sum_sq_MF) h_cusp
  funext z; simpa [sub_eq_zero] using DFunLike.congr_fun h_zero z

/-!
## Vanishing of the error terms
-/

/-- The algebraic identity behind `f₂_eq_zero`: with `A = 2H₂ + H₄` and `B = H₂ + 2H₄`,
the relation `A * f₂ + B * f₄ = 0` gives `f₄ ^ 2 * (A ^ 2 - A * B + B ^ 2) = A ^ 2 * theta_h`. -/
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

/-- `f₂ = 0`: from `theta_g = theta_h = 0` we get `f₄ ^ 2 * (3 * H_sum_sq) = 0`, and since
`H_sum_sq ≠ 0` this forces `f₄ = 0`, whence `f₂ = 0` from `theta_h = f₂ ^ 2 = 0`. -/
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
  have h_f₄_sq_3H : f₄ ^ 2 * (fun z ↦ 3 * H_sum_sq z) = 0 := by
    ext z
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    have hh_z : theta_h z = 0 := congrFun hh z
    calc f₄ z ^ 2 * (3 * H_sum_sq z)
        = (2 * H₂ z + H₄ z) ^ 2 * theta_h z := f₄_sq_mul_eq z (congrFun hg z)
      _ = _ := by rw [hh_z, mul_zero]
  -- f₄² is MDifferentiable
  have f₄_sq_MDiff : MDiff (f₄ ^ 2) := f₄_MDifferentiable.pow 2
  -- By mul_eq_zero_iff: f₄² = 0 (since 3 * H_sum_sq ≠ 0)
  have h_f₄_sq_zero : f₄ ^ 2 = 0 :=
    ((UpperHalfPlane.mul_eq_zero_iff f₄_sq_MDiff three_H_sum_sq_MDifferentiable).mp h_f₄_sq_3H
      ).resolve_right three_H_sum_sq_ne_zero
  -- From f₄² = f₄ * f₄ = 0: f₄ = 0
  exact (UpperHalfPlane.mul_eq_zero_iff f₄_MDifferentiable f₄_MDifferentiable).mp
    (pow_two f₄ ▸ h_f₄_sq_zero) |>.elim id id

/-- `f₄ = 0`, from `f₂ = 0` and `theta_h = 0`. -/
lemma f₄_eq_zero : f₄ = 0 := by
  funext z; simpa [theta_h, sq_eq_zero_iff, f₂_eq_zero] using congrFun theta_h_eq_zero z

/-- `f₃ = 0`, since `f₃ = f₂ + f₄`. -/
lemma f₃_eq_zero : f₃ = 0 := by
  rw [← f₂_add_f₄_eq_f₃]
  simp [f₂_eq_zero, f₄_eq_zero]

/-!
## Main results
-/

/-- Serre derivative of H₂: ∂₂H₂ = (1/6)(H₂² + 2H₂H₄) -/
theorem serre_D_H₂ :
    serre_D 2 H₂ = fun z ↦ (1/6 : ℂ) * (H₂ z ^ 2 + 2 * H₂ z * H₄ z) := by
  funext z; have := congrFun f₂_eq_zero z
  simp only [f₂, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul,
    Pi.zero_apply, sub_eq_zero] at this
  convert this using 1; ring

/-- Serre derivative of H₃: ∂₂H₃ = (1/6)(H₂² - H₄²) -/
theorem serre_D_H₃ : serre_D 2 H₃ = fun z ↦ (1/6 : ℂ) * (H₂ z ^ 2 - H₄ z ^ 2) := by
  funext z; have := congrFun f₃_eq_zero z
  simp only [f₃, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul, Pi.zero_apply,
    sub_eq_zero] at this
  exact this

/-- Serre derivative of H₄: ∂₂H₄ = -(1/6)(2H₂H₄ + H₄²) -/
theorem serre_D_H₄ :
    serre_D 2 H₄ = fun z ↦ -(1/6 : ℂ) * (2 * H₂ z * H₄ z + H₄ z ^ 2) := by
  funext z; have := congrFun f₄_eq_zero z
  simp only [f₄, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply,
    add_eq_zero_iff_eq_neg] at this
  convert this using 1; ring

/-- Ordinary derivative of `H₂` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₂ :
    D H₂ = (1 / 6 : ℂ) • (H₂ ^ 2 + (2 : ℂ) • (H₂ * H₄)) + (1 / 6 : ℂ) • (E₂ * H₂) := by
  ext z
  have h : D H₂ z = serre_D 2 H₂ z + 2 * 12⁻¹ * E₂ z * H₂ z := by
    simp only [serre_D_apply]
    ring
  rw [h, congrFun serre_D_H₂]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Ordinary derivative of `H₃` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₃ :
    D H₃ = (1 / 6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2) + (1 / 6 : ℂ) • (E₂ * H₃) := by
  ext z
  have h : D H₃ z = serre_D 2 H₃ z + 2 * 12⁻¹ * E₂ z * H₃ z := by
    simp only [serre_D_apply]
    ring
  rw [h, congrFun serre_D_H₃]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Ordinary derivative of `H₄` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₄ :
    D H₄ = (-(1 / 6 : ℂ)) • ((2 : ℂ) • (H₂ * H₄) + H₄ ^ 2) + (1 / 6 : ℂ) • (E₂ * H₄) := by
  ext z
  have h : D H₄ z = serre_D 2 H₄ z + 2 * 12⁻¹ * E₂ z * H₄ z := by
    simp only [serre_D_apply]
    ring
  rw [h, congrFun serre_D_H₄]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring
