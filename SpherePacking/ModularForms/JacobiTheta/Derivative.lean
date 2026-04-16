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
# Serre derivative identities for Jacobi theta functions

Proves Blueprint Proposition 6.52, equations (32)-(34):
* `serre_D_H₂` : `serre_D 2 H₂ = (1/6)(H₂² + 2H₂H₄)`
* `serre_D_H₃` : `serre_D 2 H₃ = (1/6)(H₂² - H₄²)`
* `serre_D_H₄` : `serre_D 2 H₄ = -(1/6)(2H₂H₄ + H₄²)`

Strategy: define error terms `f₂, f₃, f₄ := (LHS - RHS)`, show their S/T
transformation rules (`f₂|S = -f₄`, `f₂|T = -f₂`, `f₄|S = -f₂`,
`f₄|T = f₃`), build level-1 invariants `g` (weight 6) and `h` (weight 8)
that vanish at `i∞`, then apply cusp form dimension vanishing to get
`g = h = 0`, from which `f₂ = f₃ = f₄ = 0`.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups CongruenceSubgroup

local notation "Γ " n:100 => Gamma n


/-- Error term: `f₂ = ∂₂H₂ - (1/6)(H₂² + 2H₂H₄)` -/
noncomputable def f₂ : ℍ → ℂ := serre_D 2 H₂ - (1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))

/-- Error term: `f₃ = ∂₂H₃ - (1/6)(H₂² - H₄²)` -/
noncomputable def f₃ : ℍ → ℂ := serre_D 2 H₃ - (1/6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2)

/-- Error term: `f₄ = ∂₂H₄ + (1/6)(2H₂H₄ + H₄²)` -/
noncomputable def f₄ : ℍ → ℂ :=
  serre_D 2 H₄ + (1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))

/-- `f₂ = serre_D 2 H₂ + (-1/6) • (H₂ * (H₂ + 2H₄))` -/
lemma f₂_decompose : f₂ = serre_D (2 : ℤ) H₂ + ((-1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))) := by
  ext z; simp [f₂, sub_eq_add_neg]; ring

/-- `f₄ = serre_D 2 H₄ + (1/6) • (H₄ * (2H₂ + H₄))` -/
lemma f₄_decompose : f₄ = serre_D (2 : ℤ) H₄ + ((1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))) := by rfl

/-- `f₂` is MDifferentiable -/
lemma f₂_MDifferentiable : MDiff f₂ := by unfold f₂; fun_prop

/-- `f₃` is MDifferentiable -/
lemma f₃_MDifferentiable : MDiff f₃ := by unfold f₃; fun_prop

/-- `f₄` is MDifferentiable -/
lemma f₄_MDifferentiable : MDiff f₄ := by unfold f₄; fun_prop

/-- `f₂ + f₄ = f₃` (from Jacobi identity) -/
lemma f₂_add_f₄_eq_f₃ : f₂ + f₄ = f₃ := by
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    Pi.pow_apply, smul_eq_mul, f₂, f₃, f₄]
  have h_serre : serre_D 2 H₂ z + serre_D 2 H₄ z = serre_D 2 H₃ z := by
    have h := congrFun
      (serre_D_add (2 : ℤ) H₂ H₄ H₂_SIF_MDifferentiable H₄_SIF_MDifferentiable) z
    simp only [Pi.add_apply] at h
    convert h.symm using 2; exact jacobi_identity.symm
  linear_combination h_serre

/-- `f₂|[4]S = -f₄` -/
lemma f₂_S_action : (f₂ ∣[(4 : ℤ)] S) = -f₄ := by
  -- Step 1: (serre_D 2 H₂)|[4]S = -serre_D 2 H₄ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₄ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable S, H₂_S_action]
    simpa using serre_D_smul 2 (-1) H₄ H₄_SIF_MDifferentiable
  -- Step 2: (H₂ + 2•H₄)|[2]S = -(H₄ + 2•H₂)
  have h_lin_comb :
      ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    rw [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] S) =
      H₄ * (H₄ + (2 : ℂ) • H₂) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
      mul_slash_SL2 2 2 S _ _, H₂_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]
    ring
  -- Combine: f₂|[4]S = -serre_D 2 H₄ - (1/6) * H₄ * (2*H₂ + H₄) = -f₄
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  unfold f₄
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring_nf

/-- `f₂|[4]T = -f₂` -/
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
    simp only [(by rw [← Pi.add_apply,
      (congrFun jacobi_identity z).symm] : H₃ z = H₂ z + H₄ z)]
    ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]T = (-H₂) * (H₂ + 2•H₄)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] T) =
      -H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
      mul_slash_SL2 2 2 T _ _, H₂_T_action, h_lin_comb]
  -- Combine
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- `f₄|[4]S = -f₂` -/
lemma f₄_S_action : (f₄ ∣[(4 : ℤ)] S) = -f₂ := by
  -- Step 1: (serre_D 2 H₄)|[4]S = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₂ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable S, H₄_S_action]
    simpa using serre_D_smul 2 (-1) H₂ H₂_SIF_MDifferentiable
  -- Step 2: (2•H₂ + H₄)|[2]S = -(2•H₄ + H₂)
  have h_lin_comb :
      (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) = -((2 : ℂ) • H₄ + H₂) := by
    rw [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₄ * (2•H₂ + H₄))|[4]S = H₂ * (H₂ + 2•H₄)
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] S) = H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 S _ _, H₄_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]; ring
  -- Combine
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  unfold f₂
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring_nf

/-- `f₄|[4]T = f₃` -/
lemma f₄_T_action : (f₄ ∣[(4 : ℤ)] T) = f₃ := by
  -- Step 1: (serre_D 2 H₄)|[4]T = serre_D 2 H₃ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] T) = serre_D (2 : ℤ) H₃ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable T, H₄_T_action]
  -- Step 2: (2•H₂ + H₄)|[2]T = H₄ - H₂ using Jacobi: H₃ = H₂ + H₄
  -- -2H₂ + H₃ = -2H₂ + (H₂ + H₄) = H₄ - H₂
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = H₄ - H₂ := by
    rw [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      Pi.sub_apply, smul_eq_mul]
    simp only [(by rw [← Pi.add_apply,
      (congrFun jacobi_identity z).symm] : H₃ z = H₂ z + H₄ z)]
    ring
  -- Step 3
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] T) = H₃ * (H₄ - H₂) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
      mul_slash_SL2 2 2 T _ _, H₄_T_action, h_lin_comb]
  -- Combine
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  unfold f₃
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  rw [(by rw [← Pi.add_apply, (congrFun jacobi_identity z).symm] : H₃ z = H₂ z + H₄ z)]
  ring_nf

/-- Weight-6 level-1 invariant: `g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄` -/
noncomputable def theta_g : ℍ → ℂ := ((2 : ℂ) • H₂ + H₄) * f₂ + (H₂ + (2 : ℂ) • H₄) * f₄

/-- Weight-8 level-1 invariant: `h = f₂² + f₂f₄ + f₄²` -/
noncomputable def theta_h : ℍ → ℂ := f₂ ^ 2 + f₂ * f₄ + f₄ ^ 2

/-- `g|[6]S = g` -/
lemma theta_g_S_action : (theta_g ∣[(6 : ℤ)] S) = theta_g := by
  have h_2H₂_H₄ :
      (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) = -((2 : ℂ) • H₄ + H₂) := by
    simp only [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  have h_H₂_2H₄ :
      ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    simp only [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  have h_term1 : ((((2 : ℂ) • H₂ + H₄) * f₂) ∣[(6 : ℤ)] S) =
      ((2 : ℂ) • H₄ + H₂) * f₄ := by
    have hmul := mul_slash_SL2 2 4 S ((2 : ℂ) • H₂ + H₄) f₂
    simp only [h_2H₂_H₄, f₂_S_action] at hmul
    convert hmul using 1
    ext z; simp only [Pi.mul_apply, Pi.neg_apply]; ring
  have h_term2 : (((H₂ + (2 : ℂ) • H₄) * f₄) ∣[(6 : ℤ)] S) =
      (H₄ + (2 : ℂ) • H₂) * f₂ := by
    have hmul := mul_slash_SL2 2 4 S (H₂ + (2 : ℂ) • H₄) f₄
    simp only [h_H₂_2H₄, f₄_S_action] at hmul
    convert hmul using 1
    ext z; simp only [Pi.mul_apply, Pi.neg_apply]; ring
  simp only [theta_g, add_slash, h_term1, h_term2]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply]; ring

/-- `g|[6]T = g` -/
lemma theta_g_T_action : (theta_g ∣[(6 : ℤ)] T) = theta_g := by
  have h_2H₂_H₄ :
      (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = -(2 : ℂ) • H₂ + H₃ := by
    simp only [add_slash, SL_smul_slash,
      H₂_T_action, H₄_T_action, smul_neg]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]
    ring
  have h_H₂_2H₄ :
      ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = -H₂ + (2 : ℂ) • H₃ := by
    simp only [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
  have h_term1 : ((((2 : ℂ) • H₂ + H₄) * f₂) ∣[(6 : ℤ)] T) = (-(2 : ℂ) • H₂ + H₃) * (-f₂) := by
    simpa only [h_2H₂_H₄, f₂_T_action] using mul_slash_SL2 2 4 T ((2 : ℂ) • H₂ + H₄) f₂
  have h_term2 : (((H₂ + (2 : ℂ) • H₄) * f₄) ∣[(6 : ℤ)] T) = (-H₂ + (2 : ℂ) • H₃) * f₃ := by
    simpa only [h_H₂_2H₄, f₄_T_action]  using mul_slash_SL2 2 4 T (H₂ + (2 : ℂ) • H₄) f₄
  -- Combine and simplify using Jacobi: H₃ = H₂ + H₄, f₃ = f₂ + f₄
  simp only [theta_g, add_slash, h_term1, h_term2]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  rw [(congrFun jacobi_identity z).symm, (congrFun f₂_add_f₄_eq_f₃ z).symm]
  simp only [Pi.add_apply]; ring

/-- `h|[8]S = h` -/
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

/-- `h|[8]T = h` -/
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

/-- `theta_g` is MDifferentiable -/
lemma theta_g_MDifferentiable : MDiff theta_g := by unfold theta_g f₂ f₄; fun_prop

/-- `theta_h` is MDifferentiable -/
lemma theta_h_MDifferentiable : MDiff theta_h := by unfold theta_h f₂ f₄; fun_prop

/-- `theta_g` as a `SlashInvariantForm` of level 1 -/
noncomputable def theta_g_SIF : SlashInvariantForm (Γ 1) 6 where
  toFun := theta_g
  slash_action_eq' := slashaction_generators_GL2R theta_g 6 theta_g_S_action theta_g_T_action

/-- `theta_h` as a `SlashInvariantForm` of level 1 -/
noncomputable def theta_h_SIF : SlashInvariantForm (Γ 1) 8 where
  toFun := theta_h
  slash_action_eq' := slashaction_generators_GL2R theta_h 8 theta_h_S_action theta_h_T_action

/-- `f₂ → 0` at `i∞` -/
lemma f₂_tendsto_atImInfty : Tendsto f₂ atImInfty (𝓝 0) := by
  have h_serre_H₂ := serre_D_tendsto_zero_of_tendsto_zero 2 H₂
    H₂_SIF_MDifferentiable isBoundedAtImInfty_H₂ H₂_tendsto_atImInfty
  have h_prod : Tendsto (fun z => H₂ z * (H₂ z + 2 * H₄ z)) atImInfty (𝓝 0) := by
    have := H₂_tendsto_atImInfty
    have := H₄_tendsto_atImInfty
    tendsto_cont
  simpa [f₂] using h_serre_H₂.sub (h_prod.const_mul (1/6 : ℂ))

/-- `f₄ → 0` at `i∞` -/
lemma f₄_tendsto_atImInfty : Tendsto f₄ atImInfty (𝓝 0) := by
  have h_serre_H₄ : Tendsto (serre_D 2 H₄) atImInfty (𝓝 (-(1/6 : ℂ))) := by
    convert serre_D_tendsto_neg_k_div_12 2 H₄ H₄_SIF_MDifferentiable isBoundedAtImInfty_H₄
      H₄_tendsto_atImInfty using 2
    norm_num
  have h_scaled : Tendsto (fun z => (1/6 : ℂ) * (H₄ z * (2 * H₂ z + H₄ z)))
      atImInfty (𝓝 (1/6 : ℂ)) := by
    have := H₂_tendsto_atImInfty
    have := H₄_tendsto_atImInfty
    tendsto_cont
  simpa [f₄] using h_serre_H₄.add h_scaled

/-- `theta_g → 0` at `i∞` -/
lemma theta_g_tendsto_atImInfty : Tendsto theta_g atImInfty (𝓝 0) := by
  have := H₂_tendsto_atImInfty
  have := H₄_tendsto_atImInfty
  have := f₂_tendsto_atImInfty
  have := f₄_tendsto_atImInfty
  change Tendsto (fun z => (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z) atImInfty (𝓝 0)
  tendsto_cont

/-- `theta_h → 0` at `i∞` -/
lemma theta_h_tendsto_atImInfty : Tendsto theta_h atImInfty (𝓝 0) := by
  have := f₂_tendsto_atImInfty
  have := f₄_tendsto_atImInfty
  change Tendsto (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) atImInfty (𝓝 0)
  tendsto_cont

private noncomputable def theta_g_CF : CuspForm (Γ 1) 6 :=
  cuspFormOfSIFTendstoZero theta_g_SIF theta_g_MDifferentiable theta_g_tendsto_atImInfty

private noncomputable def theta_h_CF : CuspForm (Γ 1) 8 :=
  cuspFormOfSIFTendstoZero theta_h_SIF theta_h_MDifferentiable theta_h_tendsto_atImInfty

/-- `g = 0` by weight-6 cusp form dimension vanishing -/
lemma theta_g_eq_zero : theta_g = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 6 (by norm_num)) theta_g_CF)

/-- `h = 0` by weight-8 cusp form dimension vanishing -/
lemma theta_h_eq_zero : theta_h = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 8 (by norm_num)) theta_h_CF)

/-- `H₂² + H₂H₄ + H₄²` -/
noncomputable def H_sum_sq : ℍ → ℂ := H₂ ^ 2 + H₂ * H₄ + H₄ ^ 2

/-- `H_sum_sq` is MDifferentiable -/
lemma H_sum_sq_MDifferentiable : MDiff H_sum_sq := by unfold H_sum_sq; fun_prop

/-- `H_sum_sq → 1` at `i∞` -/
lemma H_sum_sq_tendsto : Tendsto H_sum_sq atImInfty (𝓝 1) := by
  have := H₂_tendsto_atImInfty
  have := H₄_tendsto_atImInfty
  change Tendsto (fun z => H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2) atImInfty (𝓝 1)
  tendsto_cont

/-- `H_sum_sq ≠ 0` -/
lemma H_sum_sq_ne_zero : H_sum_sq ≠ 0 := ne_zero_of_tendsto_ne_zero one_ne_zero H_sum_sq_tendsto

/-- `3 * H_sum_sq ≠ 0` -/
lemma three_H_sum_sq_ne_zero : (fun z => 3 * H_sum_sq z) ≠ 0 :=
  fun h => H_sum_sq_ne_zero
    (funext fun z => (mul_eq_zero.mp (congrFun h z)).resolve_left (by norm_num))

/-- `3 * H_sum_sq` is MDifferentiable -/
lemma three_H_sum_sq_MDifferentiable : MDiff (fun z => 3 * H_sum_sq z) :=
  mdifferentiable_const.mul H_sum_sq_MDifferentiable

private lemma H_sum_sq_eq_mul : H_sum_sq = H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by
  ext z; simp [H_sum_sq, sq]

/-- `H_sum_sq|[4]S = H_sum_sq` -/
private lemma H_sum_sq_S_action : (H_sum_sq ∣[(4 : ℤ)] S) = H_sum_sq := by
  rw [H_sum_sq_eq_mul, show (4 : ℤ) = 2 + 2 from rfl]
  simp only [SlashAction.add_slash, mul_slash_SL2 2 2 S _ _, H₂_S_action, H₄_S_action]
  ext z; simp [Pi.mul_apply, Pi.add_apply]; ring

/-- `H_sum_sq|[4]T = H_sum_sq` -/
private lemma H_sum_sq_T_action : (H_sum_sq ∣[(4 : ℤ)] T) = H_sum_sq := by
  rw [H_sum_sq_eq_mul, show (4 : ℤ) = 2 + 2 from rfl]
  simp only [SlashAction.add_slash, mul_slash_SL2 2 2 T _ _,
    H₂_T_action, H₄_T_action, ← jacobi_identity]
  ext z; simp [Pi.mul_apply, Pi.add_apply]; ring

private lemma H_sum_sq_SL2Z_invariant : ∀ γ : SL(2, ℤ), H_sum_sq ∣[(4 : ℤ)] γ = H_sum_sq :=
  slashaction_generators_SL2Z H_sum_sq 4 H_sum_sq_S_action H_sum_sq_T_action

private lemma isBoundedAtImInfty_H_sum_sq : IsBoundedAtImInfty H_sum_sq := by
  rw [H_sum_sq_eq_mul]
  exact ((isBoundedAtImInfty_H₂.mul isBoundedAtImInfty_H₂).add
    (isBoundedAtImInfty_H₂.mul isBoundedAtImInfty_H₄)).add
    (isBoundedAtImInfty_H₄.mul isBoundedAtImInfty_H₄)

private noncomputable def H_sum_sq_SIF : SlashInvariantForm (Γ 1) 4 where
  toFun := H_sum_sq
  slash_action_eq' := slashaction_generators_GL2R H_sum_sq 4 H_sum_sq_S_action H_sum_sq_T_action

private noncomputable def H_sum_sq_MF : ModularForm (Γ 1) 4 := {
  H_sum_sq_SIF with
  holo' := H_sum_sq_MDifferentiable
  bdd_at_cusps' := fun hc => bounded_at_cusps_of_bounded_at_infty hc fun A ⟨A', hA⟩ => by
    rw [← hA]; simpa [SL_slash] using H_sum_sq_SL2Z_invariant A' ▸ isBoundedAtImInfty_H_sum_sq
}

/-- `E₄ = H₂² + H₂H₄ + H₄²` by weight-4 cusp form dimension vanishing -/
theorem E₄_eq_H_sum_sq : E₄.toFun = H_sum_sq := by
  have h_toFun : (E₄ - H_sum_sq_MF).toFun = E₄.toFun - H_sum_sq := by
    ext z; simp [H_sum_sq_MF, H_sum_sq_SIF]; rfl
  have h_diff_tendsto : Tendsto (E₄ - H_sum_sq_MF).toFun atImInfty (nhds 0) := by
    rw [h_toFun]; simpa using E₄_tendsto_one_atImInfty.sub H_sum_sq_tendsto
  have h_cusp : IsCuspForm (Γ 1) 4 (E₄ - H_sum_sq_MF) := by
    rw [IsCuspForm_iff_coeffZero_eq_zero, ModularFormClass.qExpansion_coeff]; simp
    exact IsZeroAtImInfty.cuspFunction_apply_zero h_diff_tendsto (by norm_num : (0 : ℝ) < 1)
  have h_zero := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) (E₄ - H_sum_sq_MF) h_cusp
  funext z; simpa [sub_eq_zero] using DFunLike.congr_fun h_zero z

/-- From `Af₂ + Bf₄ = 0`: `f₄² · 3H_sum_sq = A² · theta_h` -/
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
    linear_combination h_sq
  -- A²f₂f₄ = -ABf₄²
  have h2 : A ^ 2 * (f₂ z * f₄ z) = -(A * B * f₄ z ^ 2) := by linear_combination A * f₄ z * hAf₂
  -- A² - AB + B² = 3(H₂² + H₂H₄ + H₄²)
  have h_sum : A ^ 2 - A * B + B ^ 2 = 3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2) := by
    simp only [hA, hB]; ring
  -- Now compute A²θₕ
  unfold theta_h
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  linear_combination -f₄ z ^ 2 * h_sum - h1 - h2

/-- `f₂ = 0` from `g = 0` and `h = 0` -/
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
  have f₄_sq_MDiff : MDiff (f₄ ^ 2) := f₄_MDifferentiable.pow 2
  -- By mul_eq_zero_iff: f₄² = 0 (since 3 * H_sum_sq ≠ 0)
  have h_f₄_sq_zero : f₄ ^ 2 = 0 :=
    ((UpperHalfPlane.mul_eq_zero_iff f₄_sq_MDiff three_H_sum_sq_MDifferentiable).mp h_f₄_sq_3H
      ).resolve_right three_H_sum_sq_ne_zero
  -- From f₄² = f₄ * f₄ = 0: f₄ = 0
  exact (UpperHalfPlane.mul_eq_zero_iff f₄_MDifferentiable f₄_MDifferentiable).mp
    (pow_two f₄ ▸ h_f₄_sq_zero) |>.elim id id

/-- `f₄ = 0` -/
lemma f₄_eq_zero : f₄ = 0 := by
  funext z; simpa [theta_h, sq_eq_zero_iff, f₂_eq_zero] using congrFun theta_h_eq_zero z

/-- `f₃ = 0` -/
lemma f₃_eq_zero : f₃ = 0 := by
  rw [← f₂_add_f₄_eq_f₃]
  simp [f₂_eq_zero, f₄_eq_zero]

/-- `∂₂H₂ = (1/6)(H₂² + 2H₂H₄)` -/
theorem serre_D_H₂ : serre_D 2 H₂ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 + 2 * H₂ z * H₄ z) := by
  funext z; have := congrFun f₂_eq_zero z
  simp only [f₂, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul,
    Pi.zero_apply, sub_eq_zero] at this
  convert this using 1; ring

/-- `∂₂H₃ = (1/6)(H₂² - H₄²)` -/
theorem serre_D_H₃ : serre_D 2 H₃ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 - H₄ z ^ 2) := by
  funext z; have := congrFun f₃_eq_zero z
  simp only [f₃, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul, Pi.zero_apply,
    sub_eq_zero] at this
  exact this

/-- `∂₂H₄ = -(1/6)(2H₂H₄ + H₄²)` -/
theorem serre_D_H₄ : serre_D 2 H₄ = fun z => -(1/6 : ℂ) * (2 * H₂ z * H₄ z + H₄ z ^ 2) := by
  funext z; have := congrFun f₄_eq_zero z
  simp only [f₄, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply,
    add_eq_zero_iff_eq_neg] at this
  convert this using 1; ring

/-- Ordinary derivative of `H₂` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₂ : D H₂ = (1 / 6 : ℂ) • (H₂ ^ 2 + (2 : ℂ) • (H₂ * H₄)) + (1 / 6 : ℂ) • (E₂ * H₂) := by
  ext z
  have h : D H₂ z = serre_D 2 H₂ z + 2 * 12⁻¹ * E₂ z * H₂ z := by
    simp only [serre_D_apply]
    ring
  rw [h, congrFun serre_D_H₂]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Ordinary derivative of `H₃` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₃ : D H₃ = (1 / 6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2) + (1 / 6 : ℂ) • (E₂ * H₃) := by
  ext z
  have h : D H₃ z = serre_D 2 H₃ z + 2 * 12⁻¹ * E₂ z * H₃ z := by
    simp only [serre_D_apply]
    ring
  rw [h, congrFun serre_D_H₃]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Ordinary derivative of `H₄` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₄ : D H₄ =
    (-(1 / 6 : ℂ)) • ((2 : ℂ) • (H₂ * H₄) + H₄ ^ 2) + (1 / 6 : ℂ) • (E₂ * H₄) := by
  ext z
  have h : D H₄ z = serre_D 2 H₄ z + 2 * 12⁻¹ * E₂ z * H₄ z := by
    simp only [serre_D_apply]
    ring
  rw [h, congrFun serre_D_H₄]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring
