module
public import SpherePacking.ModularForms.Derivative.AntiSerreDerPos
import SpherePacking.ModularForms.Lv1Lv2Identities

@[expose] public section

/-!
# Ramanujan identities

This file proves Ramanujan's differential equations for the Eisenstein series `E₂`, `E₄`, `E₆`:
- `ramanujan_E₂ : D E₂ = 12⁻¹ · (E₂² − E₄)`
- `ramanujan_E₄ : D E₄ = 3⁻¹ · (E₂ · E₄ − E₆)`
- `ramanujan_E₆ : D E₆ = 2⁻¹ · (E₂ · E₆ − E₄²)`

These follow by comparing the constant terms at infinity of Serre derivatives and using the fact
that there are no nonzero level-one cusp forms of weight less than 12.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function

/-!
## Ramanujan formulas (level 1)

We prove the weight-`k` Ramanujan identities for `E₄` and `E₆` by:
- showing the Serre derivatives are (level 1) modular forms of weight `k+2`,
- choosing the scalar so that the constant term vanishes,
- concluding the difference is a cusp form of weight `< 12`, hence zero.

The `E₂` identity is handled separately (since `E₂` is not modular).
-/

section Ramanujan

open scoped MatrixGroups

private lemma tendsto_serre_D_of_bounded_tendsto_one {f : ℍ → ℂ} (k : ℂ)
     (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f)
     (h1 : Tendsto f atImInfty (𝓝 (1 : ℂ))) :
     Tendsto (fun z : ℍ => serre_D k f z) atImInfty (𝓝 (-(k * 12⁻¹))) := by
  have hD : Tendsto (fun z : ℍ => D f z) atImInfty (𝓝 (0 : ℂ)) :=
    D_isZeroAtImInfty_of_bounded hf hbdd
  have hE₂ : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) := tendsto_E₂_atImInfty
  have hconst : Tendsto (fun _ : ℍ => k * 12⁻¹) atImInfty (𝓝 (k * 12⁻¹)) :=
    tendsto_const_nhds
  have hterm :
      Tendsto (fun z : ℍ => k * 12⁻¹ * E₂ z * f z) atImInfty (𝓝 (k * 12⁻¹)) := by
    simpa [mul_assoc, mul_one, one_mul] using (hconst.mul hE₂).mul h1
  simpa [serre_D, mul_assoc] using (hD.sub hterm)

private lemma tendsto_E₄_atImInfty : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) := by
  simpa using (SpherePacking.ModularForms.tendsto_E₄_atImInfty :
    Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)))

private lemma tendsto_E₆_atImInfty : Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)) := by
  simpa using (SpherePacking.ModularForms.tendsto_E₆_atImInfty :
    Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)))

lemma tendsto_serre_D_E₄_atImInfty :
    Tendsto (fun z : ℍ => serre_D 4 E₄.toFun z) atImInfty (𝓝 (-(3⁻¹ : ℂ))) := by
  have hmain :
      Tendsto (fun z : ℍ => serre_D 4 E₄.toFun z) atImInfty (𝓝 (-( (4 : ℂ) * 12⁻¹))) :=
    tendsto_serre_D_of_bounded_tendsto_one (k := (4 : ℂ))
      (f := E₄.toFun) E₄.holo' (ModularFormClass.bdd_at_infty E₄)
      (by simpa using tendsto_E₄_atImInfty)
  simpa [show ((4 : ℂ) * 12⁻¹) = (3⁻¹ : ℂ) by norm_num] using hmain

lemma tendsto_serre_D_E₆_atImInfty :
    Tendsto (fun z : ℍ => serre_D 6 E₆.toFun z) atImInfty (𝓝 (-(2⁻¹ : ℂ))) := by
  have hmain :
      Tendsto (fun z : ℍ => serre_D 6 E₆.toFun z) atImInfty (𝓝 (-( (6 : ℂ) * 12⁻¹))) :=
    tendsto_serre_D_of_bounded_tendsto_one (k := (6 : ℂ))
      (f := E₆.toFun) E₆.holo' (ModularFormClass.bdd_at_infty E₆)
      (by simpa using tendsto_E₆_atImInfty)
  simpa [show ((6 : ℂ) * 12⁻¹) = (2⁻¹ : ℂ) by norm_num] using hmain

noncomputable def serreD_modularForm (k : ℤ) (F : ModularForm Γ(1) k) :
    ModularForm Γ(1) (k + 2) :=
  { toFun := serre_D k F.toFun
    slash_action_eq' := by
      intro γ hγ
      rcases (Subgroup.mem_map.1 hγ) with ⟨γ', hγ', rfl⟩
      have hγ'GL :
          (γ' : GL (Fin 2) ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)) :=
        ⟨γ', hγ', rfl⟩
      have hF : F.toFun ∣[(k : ℤ)] γ' = F.toFun := by
        have hFGL := F.slash_action_eq' (γ' : GL (Fin 2) ℝ) hγ'GL
        simpa [ModularForm.SL_slash] using hFGL
      have hSerre := serre_D_slash_invariant k F.toFun F.holo' γ' hF
      simpa [ModularForm.SL_slash] using hSerre
    holo' := serre_D_differentiable (k := (k : ℂ)) F.holo'
    bdd_at_cusps' := by
      intro c hc
      have hbdd : IsBoundedAtImInfty (serre_D k F.toFun) :=
        serre_D_isBoundedAtImInfty (k := (k : ℂ)) F.holo' (ModularFormClass.bdd_at_infty F)
      refine bounded_at_cusps_of_bounded_at_infty
        (f := serre_D k F.toFun) (k := (k + 2 : ℤ)) hc ?_
      intro A hA
      rcases hA with ⟨γ, rfl⟩
      have hγmem : (γ : GL (Fin 2) ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)) :=
        ⟨γ, CongruenceSubgroup.mem_Gamma_one γ, rfl⟩
      have hF : F.toFun ∣[(k : ℤ)] γ = F.toFun := by
        have hFGL := F.slash_action_eq' (γ : GL (Fin 2) ℝ) hγmem
        simpa [ModularForm.SL_slash] using hFGL
      have hSerre : serre_D k F.toFun ∣[(k + 2 : ℤ)] γ = serre_D k F.toFun :=
        serre_D_slash_invariant k F.toFun F.holo' γ hF
      have hSerreGL :
          serre_D k F.toFun ∣[(k + 2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
            serre_D k F.toFun := by
        assumption
      rw [hSerreGL]
      exact hbdd }

lemma eq_zero_of_tendsto_zero_atImInfty {k : ℤ} (hk : k < 12) (G : ModularForm Γ(1) k)
    (hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ))) : G = 0 := by
  refine IsCuspForm_weight_lt_eq_zero k hk G <|
    (IsCuspForm_iff_coeffZero_eq_zero k G).2 ?_
  have hGval : UpperHalfPlane.valueAtInfty (G : ℍ → ℂ) = 0 :=
    UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero (f := (G : ℍ → ℂ)) hGlim
  have hq :
      (qExpansion (1 : ℝ) G).coeff 0 = UpperHalfPlane.valueAtInfty (G : ℍ → ℂ) :=
    qExpansion_coeff_zero (f := G) (h := (1 : ℝ)) (by positivity) (by simp)
  simp [hq, hGval]

/--
Serre derivative of Eisenstein series. We compare constant terms via the limit at infinity,
then use the fact that there are no nonzero level-one cusp forms of weight `< 12`.
-/
public theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by
  let corr : SL(2, ℤ) → ℍ → ℂ := fun γ z =>
    (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z)
  have hcorr_holo (γ : SL(2, ℤ)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (corr γ) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    -- Reduce to a holomorphic rational function on `{z : ℂ | 0 < z.im}`.
    have hG :
        DifferentiableOn ℂ
          (fun z : ℂ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z))
          {z : ℂ | 0 < z.im} := by
      intro z hz
      have hz0 : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ ⟨z, hz⟩
      have hdenom : DifferentiableAt ℂ (fun w : ℂ => denom γ w) z := by
        simpa using (differentiableAt_denom (γ := γ) z)
      have hdiv : DifferentiableAt ℂ (fun w : ℂ => (γ 1 0 : ℂ) / denom γ w) z :=
        (differentiableAt_const _).div hdenom hz0
      exact (hdiv.const_mul ((12 : ℂ) * (2 * π * I)⁻¹)).differentiableWithinAt
    refine hG.congr ?_
    intro z hz
    simp [corr, Function.comp_apply, ofComplex_apply_of_im_pos hz]
  have hcorr_D (γ : SL(2, ℤ)) :
      D (corr γ) = - 12⁻¹ * (corr γ) * (corr γ) := by
    funext z
    -- Compute via the complex derivative of the rational function `c / (cz + d)`.
    have h_eq :
        ((corr γ) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
          (fun w : ℂ => (12 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ w)) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
      simp [corr, Function.comp_apply, ofComplex_apply_of_im_pos hw]
    have hz0 : denom γ (z : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
    have hderiv_div :
        deriv (fun w : ℂ => (γ 1 0 : ℂ) / denom γ w) (z : ℂ) =
          -((γ 1 0 : ℂ) * (γ 1 0 : ℂ)) / (denom γ (z : ℂ)) ^ 2 := by
      rw [deriv_fun_div (differentiableAt_const _)
        (differentiableAt_denom (γ := γ) (z : ℂ)) hz0]
      simp [deriv_denom (γ := γ) (z := (z : ℂ))]
    -- Now rewrite `D` using `h_eq` and compute directly.
    simp only [D, neg_mul, Pi.mul_apply, Pi.neg_apply, Pi.inv_apply, Pi.ofNat_apply]
    rw [h_eq.deriv_eq]
    have htwoPiI : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
    -- `D` applies an extra factor `(2πi)⁻¹`; `corr` itself already contains `(2πi)⁻¹`.
    simp [mul_assoc, mul_left_comm, mul_comm, hderiv_div]
    dsimp [corr]
    field_simp [htwoPiI, hz0]
    ring_nf
    simp
  have hE₂slash (γ : SL(2, ℤ)) :
      (E₂ ∣[(2 : ℤ)] γ) = E₂ + corr γ := by
    simpa [corr] using (E₂_slash γ)
  have hDE₂_slash (γ : SL(2, ℤ)) :
      D E₂ ∣[(4 : ℤ)] γ =
        D E₂
          + (6⁻¹ : ℂ) • (E₂ * corr γ)
          + (12⁻¹ : ℂ) • (corr γ * corr γ) := by
    have hDslash := D_slash (k := (2 : ℤ)) (F := E₂) E₂_holo' γ
    ext z
    have hD := congrFun hDslash z
    have hE := congrFun (hE₂slash γ) z
    have hcorr_h := hcorr_holo γ
    let anom : ℂ :=
      (2 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (E₂ ∣[(2 : ℤ)] γ) z
    have hsolve : (D E₂ ∣[(4 : ℤ)] γ) z = D (E₂ ∣[(2 : ℤ)] γ) z + anom := by
      have h0 : D (E₂ ∣[(2 : ℤ)] γ) z = (D E₂ ∣[(4 : ℤ)] γ) z - anom := by
        simpa [anom, Pi.sub_apply, Pi.mul_apply] using hD
      exact (sub_eq_iff_eq_add).1 h0.symm
    have hDadd : D (E₂ ∣[(2 : ℤ)] γ) z = (D E₂ + D (corr γ)) z := by
      rw [hE₂slash]
      simp [D_add _ _ E₂_holo' hcorr_h]
    have hcorrD : D (corr γ) z = (-12⁻¹ : ℂ) * (corr γ z * corr γ z) := by
      simpa [Pi.mul_apply, Pi.neg_apply, mul_assoc] using congrFun (hcorr_D γ) z
    have hA :
        (2 : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) =
          (6⁻¹ : ℂ) * corr γ z := by
      ring
    have hEeval : (E₂ ∣[(2 : ℤ)] γ) z = E₂ z + corr γ z := by
      simpa [Pi.add_apply] using hE
    have hanom : anom = (6⁻¹ : ℂ) * corr γ z * (E₂ z + corr γ z) := by
      -- rewrite the slashed `E₂` and then use `hA` for the prefactor
      dsimp [anom]
      rw [hEeval]
      have hA' := congrArg (fun t => t * (E₂ z + corr γ z)) hA
      simpa [mul_assoc] using hA'
    rw [hsolve, hDadd]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    -- `D(corr) = -(1/12)·corr²`, and `anom = (1/6)·corr·(E₂+corr)`.
    rw [hcorrD, hanom]
    simp [mul_add, mul_left_comm, mul_comm]
    ring_nf
  have hSerre_slash (γ : SL(2, ℤ)) :
      serre_D 1 E₂ ∣[(4 : ℤ)] γ = serre_D 1 E₂ := by
    ext z
    -- Expand the slash, then rewrite `D E₂` and `E₂` under slash.
    have hE := congrFun (hE₂slash γ) z
    have hD := congrFun (hDE₂_slash γ) z
    -- `E₂(γ·z)` term in the square simplifies via the weight-2 slash.
    have hE_sq :
        (E₂ (γ • z)) ^ (2 : ℕ) * (denom γ z) ^ (-(4 : ℤ)) =
          (E₂ z + corr γ z) ^ (2 : ℕ) := by
      -- Rewrite the transformation law `E₂ ∣[2] γ = E₂ + corr γ` at `z`.
      have hmain : E₂ (γ • z) * (denom γ z) ^ (-(2 : ℤ)) = E₂ z + corr γ z := by
        simpa [ModularForm.SL_slash_apply (f := E₂) (k := (2 : ℤ)) γ z, Pi.add_apply] using hE
      have hden :
          ((denom γ z) ^ (-(2 : ℤ))) ^ (2 : ℕ) = (denom γ z) ^ (-(4 : ℤ)) := by
        calc
          ((denom γ z) ^ (-(2 : ℤ))) ^ (2 : ℕ)
              = ((denom γ z) ^ (-(2 : ℤ))) ^ ((2 : ℤ)) := by
                  simpa using (zpow_natCast ((denom γ z) ^ (-(2 : ℤ))) 2).symm
          _ = (denom γ z) ^ (-(2 : ℤ) * (2 : ℤ)) := by
                  simpa using (zpow_mul (denom γ z) (-(2 : ℤ)) (2 : ℤ)).symm
          _ = (denom γ z) ^ (-(4 : ℤ)) := by norm_num
      have hpow :
          (E₂ (γ • z) * (denom γ z) ^ (-(2 : ℤ))) ^ (2 : ℕ) =
            (E₂ z + corr γ z) ^ (2 : ℕ) := by
        simpa using congrArg (fun w : ℂ => w ^ (2 : ℕ)) hmain
      have hpow' := hpow
      rw [mul_pow] at hpow'
      rw [hden] at hpow'
      exact hpow'
    -- Now compute `serre_D 1 E₂` under slash.
    -- `(serre_D 1 E₂ ∣[4] γ) z = (denom γ z)^(-4) * serre_D 1 E₂(γ•z)`.
    simp only [serre_D, SL_slash_apply, Pi.add_apply] at *
    -- Use the explicit slash formulas for `D E₂` and `E₂`.
    -- For `D E₂`: use `hD` (already evaluated at `z`).
    -- For `E₂(γ•z)`: use the rewritten square identity `hE_sq`.
    -- Everything cancels by expanding the square.
    -- First, rewrite the `D E₂` term.
    -- `hD` is about `(D E₂ ∣[4] γ) z`.
    -- Replace it by `D E₂ (γ•z) * (denom γ z)^(-4)`.
    have hD' :
        D E₂ (γ • z) * (denom γ z) ^ (-(4 : ℤ)) =
          D E₂ z +
            (6⁻¹ : ℂ) * (E₂ z * corr γ z) +
            (12⁻¹ : ℂ) * (corr γ z * corr γ z) := by
      simpa [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using hD
    grind only
  -- Package `serre_D 1 E₂` as a weight-4 level-1 modular form.
  let F₄ : ModularForm Γ(1) 4 :=
    { toFun := serre_D 1 E₂
      slash_action_eq' := fun γ a =>
          slashaction_generators_GL2R (serre_D 1 E₂) 4 (hSerre_slash ModularGroup.S)
          (hSerre_slash ModularGroup.T) γ a
      holo' := serre_D_differentiable (k := (1 : ℂ)) E₂_holo'
      bdd_at_cusps' := by
        intro c hc
        -- Bounded at infinity: both terms in `serre_D` are bounded.
        have hbdd : IsBoundedAtImInfty (serre_D 1 E₂) :=
          serre_D_isBoundedAtImInfty (k := (1 : ℂ)) E₂_holo' E₂_isBoundedAtImInfty
        refine bounded_at_cusps_of_bounded_at_infty
          (f := serre_D 1 E₂) (k := (4 : ℤ)) hc ?_
        intro A hA
        rcases hA with ⟨γ, rfl⟩
        have hcast :
            serre_D 1 E₂ ∣[(4 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
              serre_D 1 E₂ ∣[(4 : ℤ)] γ := by
          simpa using (ModularForm.SL_slash (f := serre_D 1 E₂) (k := (4 : ℤ)) γ).symm
        have hSerreSL : serre_D 1 E₂ ∣[(4 : ℤ)] γ = serre_D 1 E₂ := hSerre_slash γ
        have hSerreGL :
            serre_D 1 E₂ ∣[(4 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
              serre_D 1 E₂ := by
          simpa [hcast] using hSerreSL
        rw [hSerreGL]
        exact hbdd }
  -- Identify `F₄` by its constant term at infinity: it is `-(1/12)·E₄`.
  let G : ModularForm Γ(1) 4 := F₄ + (12⁻¹ : ℂ) • E₄
  have hbddE₂ : IsBoundedAtImInfty E₂ := E₂_isBoundedAtImInfty
  have hDlim : Tendsto (fun z : ℍ => D E₂ z) atImInfty (𝓝 (0 : ℂ)) :=
    D_isZeroAtImInfty_of_bounded E₂_holo' hbddE₂
  have hE₂lim : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) := tendsto_E₂_atImInfty
  have hF₄lim : Tendsto (fun z : ℍ => F₄ z) atImInfty (𝓝 (-(12⁻¹ : ℂ))) := by
    -- `F₄ = D E₂ - (1/12) E₂^2`.
    have hterm :
        Tendsto (fun z => 12⁻¹ * E₂ z * E₂ z) atImInfty (𝓝 (12⁻¹ : ℂ)) := by
      have hE₂' :
          Tendsto (fun z => (12⁻¹ : ℂ) * E₂ z) atImInfty (𝓝 (12⁻¹ : ℂ)) := by
        simpa [mul_one] using (tendsto_const_nhds.mul hE₂lim)
      simpa [mul_assoc, mul_one] using (hE₂'.mul hE₂lim)
    have hmain :
        Tendsto (fun z : ℍ => serre_D 1 E₂ z) atImInfty (𝓝 (-(12⁻¹ : ℂ))) := by
      simpa [serre_D, mul_assoc, mul_one] using (hDlim.sub hterm)
    assumption
  have hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ)) := by
    have hE₄lim :
        Tendsto (fun z : ℍ => (12⁻¹ : ℂ) * E₄ z) atImInfty
          (𝓝 ((12⁻¹ : ℂ) * (1 : ℂ))) :=
      by
        simpa [mul_one] using (tendsto_const_nhds.mul tendsto_E₄_atImInfty)
    have hsum := hF₄lim.add hE₄lim
    simpa [G, mul_one] using hsum
  have hG0 : G = 0 := eq_zero_of_tendsto_zero_atImInfty (k := 4) (by norm_num) G hGlim
  funext z
  have hz : F₄ z + (12⁻¹ : ℂ) * E₄ z = 0 := by
    simpa [G] using congrArg (fun f : ModularForm Γ(1) 4 => f z) hG0
  have hz' : F₄ z = (-12⁻¹ : ℂ) * E₄ z := by
    have : F₄ z = -((12⁻¹ : ℂ) * E₄ z) := (eq_neg_iff_add_eq_zero).2 (by simpa using hz)
    simpa [neg_mul] using this
  assumption

public theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by
  let F₆ : ModularForm Γ(1) 6 := serreD_modularForm 4 E₄
  let G : ModularForm Γ(1) 6 := F₆ + (3⁻¹ : ℂ) • E₆
  have hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ)) := by
    have hF : Tendsto (fun z : ℍ => F₆ z) atImInfty (𝓝 (-(3⁻¹ : ℂ))) := by
      simpa [F₆, serreD_modularForm] using tendsto_serre_D_E₄_atImInfty
    have hE6 :
        Tendsto (fun z : ℍ => (3⁻¹ : ℂ) * E₆ z) atImInfty
          (𝓝 ((3⁻¹ : ℂ) * (1 : ℂ))) :=
      by
        simpa [mul_one] using (tendsto_const_nhds.mul tendsto_E₆_atImInfty)
    simpa [G, mul_one] using hF.add hE6
  have hG0 : G = 0 := eq_zero_of_tendsto_zero_atImInfty (k := (6 : ℤ)) (by norm_num) G hGlim
  funext z
  have hz : F₆ z + (3⁻¹ : ℂ) * E₆ z = 0 := by
    simpa [G] using congrArg (fun f : ModularForm Γ(1) 6 => f z) hG0
  have hz' : F₆ z = -((3⁻¹ : ℂ) * E₆ z) :=
    (eq_neg_iff_add_eq_zero).2 (by simpa using hz)
  have hz'' : F₆.toFun z = -((3⁻¹ : ℂ) * E₆ z) := by
    simpa [ModularForm.toFun_eq_coe] using hz'
  simpa [F₆, serreD_modularForm, neg_mul, mul_assoc] using hz''

public theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by
  let F₈ : ModularForm Γ(1) 8 := serreD_modularForm 6 E₆
  let E4sq : ModularForm Γ(1) 8 := E₄.mul E₄
  let G : ModularForm Γ(1) 8 := F₈ + (2⁻¹ : ℂ) • E4sq
  have hGlim : Tendsto (fun z : ℍ => G z) atImInfty (𝓝 (0 : ℂ)) := by
    have hF : Tendsto (fun z : ℍ => F₈ z) atImInfty (𝓝 (-(2⁻¹ : ℂ))) := by
      simpa [F₈, serreD_modularForm] using tendsto_serre_D_E₆_atImInfty
    have hE4 : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
      tendsto_E₄_atImInfty
    have hE4sq :
        Tendsto (fun z : ℍ => E4sq z) atImInfty (𝓝 ((1 : ℂ) * (1 : ℂ))) := by
      simpa [E4sq] using hE4.mul hE4
    have hE4sq' :
        Tendsto (fun z : ℍ =>
          (2⁻¹ : ℂ) * E4sq z) atImInfty (𝓝 ((2⁻¹ : ℂ) * ((1 : ℂ) * (1 : ℂ)))) :=
      tendsto_const_nhds.mul hE4sq
    simpa [G, mul_one] using hF.add hE4sq'
  have hG0 : G = 0 := eq_zero_of_tendsto_zero_atImInfty (k := (8 : ℤ)) (by norm_num) G hGlim
  funext z
  have hz : F₈ z + (2⁻¹ : ℂ) * E4sq z = 0 := by
    simpa [G] using congrArg (fun f : ModularForm Γ(1) 8 => f z) hG0
  have hz' : F₈ z = -((2⁻¹ : ℂ) * E4sq z) :=
    (eq_neg_iff_add_eq_zero).2 (by simpa using hz)
  have hz'' : F₈.toFun z = -((2⁻¹ : ℂ) * E4sq z) := by
    simpa [ModularForm.toFun_eq_coe] using hz'
  simpa [F₈, serreD_modularForm, E4sq, neg_mul, mul_assoc, mul_left_comm, mul_comm] using hz''

/-- Ramanujan's differential equation for `E₂`. -/
@[simp]
public theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by
  ext z
  have h := ramanujan_E₂'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  field_simp at h1
  simpa [add_comm, sub_eq_iff_eq_add] using h1

/-- Ramanujan's differential equation for `E₄`. -/
@[simp]
public theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by
  ext z
  have h := congrFun ramanujan_E₄' z
  have h' : D E₄.toFun z = (-(3⁻¹ : ℂ) * E₆ z) + (4 : ℂ) * 12⁻¹ * E₂ z * E₄ z :=
    (sub_eq_iff_eq_add).1 (by simpa [serre_D, mul_assoc, mul_left_comm, mul_comm] using h)
  have hconst : ((4 : ℂ) * 12⁻¹) = (3⁻¹ : ℂ) := by norm_num1
  rw [h']
  simp [hconst, sub_eq_add_neg]
  ring_nf

/-- Ramanujan's differential equation for `E₆`. -/
@[simp]
public theorem ramanujan_E₆ :
    D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  ext z
  have h := congrFun ramanujan_E₆' z
  have h' :
      D E₆.toFun z =
        (-(2⁻¹ : ℂ) * (E₄ z * E₄ z)) + (6 : ℂ) * 12⁻¹ * E₂ z * E₆ z :=
    (sub_eq_iff_eq_add).1 (by simpa [serre_D, mul_assoc, mul_left_comm, mul_comm] using h)
  have hconst : ((6 : ℂ) * 12⁻¹) = (2⁻¹ : ℂ) := by norm_num1
  rw [h']
  simp [hconst, sub_eq_add_neg]
  ring_nf

end Ramanujan
