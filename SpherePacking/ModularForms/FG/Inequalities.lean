module
public import SpherePacking.ModularForms.FG.Basic
import SpherePacking.ModularForms.FG.Positivity
import SpherePacking.ModularForms.FG.L10OverAsymptotics
import SpherePacking.ModularForms.FG.AsymptoticsTools
import SpherePacking.Tactic.NormNumI

/-!
# Inequalities

This file proves derivative identities and inequalities for `FmodG` on the imaginary axis.
-/

open scoped Real Manifold Topology ArithmeticFunction.sigma ModularForm MatrixGroups
open Filter Complex UpperHalfPlane ModularForm
open SpherePacking.ModularForms

-- Ensure the `SL(2,ℤ)` Möbius action on `ℍ` is available for the local computations below.
noncomputable local instance : MulAction SL(2, ℤ) ℍ := UpperHalfPlane.SLAction (R := ℤ)


/- $\mathcal{L}_{1, 0}$ is positive on the imaginary axis. -/
lemma L₁₀_pos : ResToImagAxis.Pos L₁₀ :=
  antiSerreDerPos (F := L₁₀) (k := 22) L₁₀_holo SerreDer_22_L₁₀_pos L₁₀_eventuallyPos

private lemma hasDerivAt_resToImagAxis_re (H : ℍ → ℂ) (hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (H.resToImagAxis u).re) (-2 * π * (D H).resToImagAxis t).re t := by
  simpa using
    (hasDerivAt_const (x := t) (c := (Complex.reCLM : ℂ →L[ℝ] ℝ))).clm_apply
      ((ResToImagAxis.Differentiable H hH t ht).hasDerivAt.congr_deriv
        (deriv_resToImagAxis_eq H hH ht))

lemma hasDerivAt_FReal (t : ℝ) (ht : 0 < t) :
    HasDerivAt FReal (-2 * π * (D F).resToImagAxis t).re t := by
  simpa [FReal] using (hasDerivAt_resToImagAxis_re (H := F) F_holo t ht)

lemma hasDerivAt_GReal (t : ℝ) (ht : 0 < t) :
    HasDerivAt GReal (-2 * π * (D G).resToImagAxis t).re t := by
  simpa [GReal] using (hasDerivAt_resToImagAxis_re (H := G) G_holo t ht)

lemma L₁₀_resToImagAxis_re_eq (t : ℝ) (ht : 0 < t) :
    (L₁₀.resToImagAxis t).re =
      ((D F).resToImagAxis t).re * GReal t - FReal t * ((D G).resToImagAxis t).re := by
  have hF_real : ResToImagAxis.Real F := F_pos.1
  have hG_real : ResToImagAxis.Real G := G_pos.1
  have hDF_real : ResToImagAxis.Real (D F) := ResToImagAxis.Real.D_of_real hF_real F_holo
  have hDG_real : ResToImagAxis.Real (D G) := ResToImagAxis.Real.D_of_real hG_real G_holo
  have hFim : (F ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht] using (hF_real t ht)
  have hGim : (G ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht] using (hG_real t ht)
  have hDFim : (D F ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht] using (hDF_real t ht)
  have hDGim : (D G ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht] using (hDG_real t ht)
  simp [L₁₀, FReal, GReal, Function.resToImagAxis, ResToImagAxis, ht, Complex.mul_re, hFim, hGim,
    hDFim, hDGim]

lemma deriv_FmodGReal_neg {t : ℝ} (ht : 0 < t) : deriv FmodGReal t < 0 := by
  have hGpos : 0 < GReal t := by simpa [GReal] using (G_pos.2 t ht)
  have hGne : GReal t ≠ 0 := ne_of_gt hGpos
  have hquot := (hasDerivAt_FReal t ht).div (hasDerivAt_GReal t ht) hGne
  have hLpos : 0 < (L₁₀.resToImagAxis t).re := by
    simpa using (L₁₀_pos.2 t ht)
  have hderiv :
      deriv FmodGReal t =
        ((-2 * π * (D F).resToImagAxis t).re * GReal t -
            FReal t * (-2 * π * (D G).resToImagAxis t).re) / (GReal t) ^ 2 := by
    simpa [FmodGReal] using hquot.deriv
  have hscale (z : ℂ) : (-2 * π * z).re = (-2 * Real.pi) * z.re := by
    simp [Complex.mul_re]
  have hnum :
      (-2 * Real.pi) * ((D F).resToImagAxis t).re * GReal t -
          FReal t * ((-2 * Real.pi) * ((D G).resToImagAxis t).re)
        = (-2 * Real.pi) * (L₁₀.resToImagAxis t).re := by
    have := congrArg (fun x : ℝ => (-2 * Real.pi) * x) (L₁₀_resToImagAxis_re_eq t ht)
    nlinarith [this]
  have hdenpos : 0 < (GReal t) ^ 2 := by
    simpa [pow_two] using sq_pos_of_ne_zero hGne
  have hpi_neg : (-2 * Real.pi : ℝ) < 0 := by nlinarith [Real.pi_pos]
  rw [hderiv, hscale, hscale, hnum]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hpi_neg hLpos) hdenpos

/--
$t \mapsto F(it) / G(it)$ is monotone decreasing.
-/
private lemma FmodG_strictAnti_aux : StrictAntiOn FmodGReal (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn FmodGReal (Set.Ioi (0 : ℝ)) := by
    intro x hx
    have hFdiff : DifferentiableAt ℝ FReal x := FReal_Differentiable (t := x) hx
    have hGdiff : DifferentiableAt ℝ GReal x := GReal_Differentiable (t := x) hx
    have hGne : GReal x ≠ 0 := ne_of_gt (by simpa [GReal] using (G_pos.2 x hx))
    exact (hFdiff.div hGdiff hGne).continuousAt.continuousWithinAt
  exact
    strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ)) hcont (by
      intro t ht
      have ht' : 0 < t := by
        have : t ∈ Set.Ioi (0 : ℝ) := by simpa [interior_Ioi] using ht
        simpa [Set.mem_Ioi] using this
      simpa using deriv_FmodGReal_neg (t := t) ht')

/-- The function `FmodGReal` is antitone on the positive real axis. -/
public theorem FmodG_antitone : AntitoneOn FmodGReal (Set.Ioi 0) :=
  (FmodG_strictAnti_aux).antitoneOn

lemma tendsto_mul_t_resToImagAxis_A_E :
    Tendsto (fun t : ℝ => (t : ℂ) * (A_E.resToImagAxis t)) atTop (nhds (0 : ℂ)) := by
  let a : ℕ → ℂ := A_E_coeff
  have hA_series : ∀ z : ℍ, A_E z =
      ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * ((n + 1 : ℕ) : ℂ) * (z : ℂ)) := by
    intro z
    -- Reuse the shifted `ℕ`-Fourier expansion from `ModularForms.Eisenstein`.
    simpa [a, A_E_term, A_E_coeff, mul_assoc, mul_left_comm, mul_comm] using (A_E_eq_tsum z)
  have ha :
      Summable (fun n : ℕ => ‖a n‖ * Real.exp (-(2 * π * (1 : ℝ)) * (n : ℝ))) := by
    -- Compare with a polynomially-weighted geometric series.
    let r : ℝ := Real.exp (-2 * Real.pi)
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr : ‖r‖ < 1 := by
      have hr' : r < 1 := by
        have : (-2 * Real.pi) < 0 := by nlinarith [Real.pi_pos]
        simpa [r] using (Real.exp_lt_one_iff.2 this)
      simpa [Real.norm_of_nonneg hr0] using hr'
    have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr
    have hr_ne : r ≠ 0 := ne_of_gt (Real.exp_pos (-2 * Real.pi))
    have hs_succ : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1)) := by
      -- Shift the summable series by one.
      simpa [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * r ^ n) 1).2 hs
    have hs_shift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ n) := by
      -- Multiply by `r⁻¹` to remove the extra `r`.
      have hs_mul : Summable fun n : ℕ => (r⁻¹ : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1)) :=
        hs_succ.mul_left (r⁻¹)
      refine hs_mul.congr ?_
      intro n
      -- `r⁻¹ * (A * r^(n+1)) = A * r^n` by `pow_succ` and cancellation.
      have hcancel : (r⁻¹ : ℝ) * (r ^ n * r) = r ^ n := by
        calc
          (r⁻¹ : ℝ) * (r ^ n * r) = r ^ n * (r⁻¹ * r) := by ac_rfl
          _ = r ^ n := by simp [hr_ne]
      calc
        (r⁻¹ : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 5 * r ^ (n + 1))
            = (r⁻¹ : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 5 * (r ^ n * r)) := by
                simp [pow_succ, mul_assoc]
        _ = ((n + 1 : ℕ) : ℝ) ^ 5 * (r⁻¹ : ℝ) * (r ^ n * r) := by ac_rfl
        _ = ((n + 1 : ℕ) : ℝ) ^ 5 * r ^ n := by simp [mul_assoc, hcancel]
    have hbound : ∀ n : ℕ,
        ‖a n‖ * Real.exp (-(2 * π * (1 : ℝ)) * (n : ℝ)) ≤
          (720 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 5 * r ^ n) := by
      intro n
      have hσ : (σ 3 (n + 1) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := by
        exact_mod_cast (sigma_bound 3 (n + 1))
      have hcoeff :
          ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 5 := by
        nlinarith
      have hnorm_a :
          ‖a n‖ = (720 : ℝ) * ((n + 1 : ℕ) : ℝ) * (σ 3 (n + 1) : ℝ) := by
        simpa [a] using (norm_A_E_coeff (n := n))
      have hexp : Real.exp (-(2 * π * (1 : ℝ)) * (n : ℝ)) = r ^ n := by
        -- `exp (-(2π) * n) = (exp (-2π))^n`.
        calc
          Real.exp (-(2 * π * (1 : ℝ)) * (n : ℝ)) = Real.exp (-2 * Real.pi) ^ n := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using (Real.exp_nat_mul (-2 * Real.pi) n)
          _ = r ^ n := by simp [r]
      -- Combine the bounds.
      rw [hnorm_a, hexp]
      have hnexp : 0 ≤ r ^ n := by positivity
      have hmul := mul_le_mul_of_nonneg_right hcoeff hnexp
      nlinarith [hmul]
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hs_shift.mul_left (720 : ℝ)) <;>
      first | exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le | exact hbound n
  simpa [cpow_one, A_E] using
    (tendsto_rpow_mul_resToImagAxis_of_fourier_shift (F := A_E) (a := a) (n₀ := 1) (c := (1 : ℝ))
      (by norm_num) hA_series ha 1)

/-- `S • (it) = i/t` on the imaginary axis. -/
lemma modular_S_smul_imagAxis (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • UpperHalfPlane.mk (Complex.I * t) (by simp [ht]) =
      UpperHalfPlane.mk (Complex.I * t⁻¹) (by simp [inv_pos.2 ht]) := by
  ext1
  -- `modular_S_smul` gives `S • z = mk (-z)⁻¹ ...`.
  -- After coercion to `ℂ` and simplification, this is `(- (I*t))⁻¹ = I*(t⁻¹)`.
  simpa [Complex.ofReal_inv, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun z : ℍ => (z : ℂ))
      (UpperHalfPlane.modular_S_smul (z := UpperHalfPlane.mk (Complex.I * t) (by simp [ht])))

lemma pow_six_mul_inv (t : ℂ) (ht : t ≠ 0) :
    t ^ (6 : ℕ) * t⁻¹ = t ^ (5 : ℕ) := by simp [pow_succ, mul_assoc, ht]

lemma pow_six_mul_inv_mul (t x : ℂ) (ht : t ≠ 0) :
    t ^ (6 : ℕ) * (t⁻¹ * x) = t ^ (5 : ℕ) * x := by
  simpa [mul_assoc] using congrArg (fun y : ℂ => y * x) (pow_six_mul_inv (t := t) ht)

lemma pow_two_mul_pow_four (z : ℂ) :
    z ^ (2 : ℕ) * z ^ (4 : ℕ) = z ^ (6 : ℕ) := by
  simpa using (pow_add z (2 : ℕ) (4 : ℕ)).symm

/-- The `A_E` combination transforms on the imaginary axis as in the blueprint:
`A_E(i/t) = -t^6 A_E(it) + (6/π) t^5 E₄(it)`. -/
lemma A_E_resToImagAxis_inv (t : ℝ) (ht : 0 < t) :
    A_E.resToImagAxis t⁻¹ =
      -((t : ℂ) ^ (6 : ℕ)) * (A_E.resToImagAxis t) + ((6 : ℂ) / π) * ((t : ℂ) ^ (5 : ℕ)) *
        ((E₄.toFun).resToImagAxis t) := by
  have htinv : 0 < t⁻¹ := inv_pos.2 ht
  -- Use the `S`-transformation laws for `E₂, E₄, E₆` at `z = it`.
  set z : ℍ := UpperHalfPlane.mk (Complex.I * t) (by simp [ht])
  have hS : ModularGroup.S • z = UpperHalfPlane.mk (Complex.I * t⁻¹) (by simp [htinv]) := by
    simpa [z] using modular_S_smul_imagAxis t ht
  have hE2 : E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) :=
    E₂_S_transform z
  have hE4 : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z := E₄_S_transform z
  have hE6 : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z := E₆_S_transform z
  -- Simplify the powers of `z = i*t` appearing in the transformation.
  have hz2 : (z : ℂ) ^ (2 : ℕ) = -((t : ℂ) ^ (2 : ℕ)) := by
    simp [z, mul_pow]
  have hz4 : (z : ℂ) ^ (4 : ℕ) = (t : ℂ) ^ (4 : ℕ) := by
    simp [z, mul_pow]
  have hz6 : (z : ℂ) ^ (6 : ℕ) = -((t : ℂ) ^ (6 : ℕ)) := by
    have hI6 : (Complex.I ^ (6 : ℕ) : ℂ) = -1 := by norm_num1
    calc
      (z : ℂ) ^ (6 : ℕ) = (Complex.I * (t : ℂ)) ^ (6 : ℕ) := by simp [z]
      _ = (Complex.I ^ (6 : ℕ)) * ((t : ℂ) ^ (6 : ℕ)) := by simp [mul_pow]
      _ = -((t : ℂ) ^ (6 : ℕ)) := by simp [hI6]
  have hz5 : (z : ℂ) ^ (5 : ℕ) = Complex.I * ((t : ℂ) ^ (5 : ℕ)) := by
    have hI5 : (Complex.I ^ (5 : ℕ) : ℂ) = Complex.I := by norm_num1
    calc
      (z : ℂ) ^ (5 : ℕ) = (Complex.I * (t : ℂ)) ^ (5 : ℕ) := by simp [z]
      _ = (Complex.I ^ (5 : ℕ)) * ((t : ℂ) ^ (5 : ℕ)) := by simp [mul_pow]
      _ = Complex.I * ((t : ℂ) ^ (5 : ℕ)) := by simp [hI5]
  have hdiv : (6 : ℂ) / (π * Complex.I * z) = -((6 : ℂ) / π) * ((t : ℂ)⁻¹) := by
    grind only
  -- Put everything together and simplify.
  have hAE :
      A_E (ModularGroup.S • z) =
        -((t : ℂ) ^ (6 : ℕ)) * (A_E z) + ((6 : ℂ) / π) * ((t : ℂ) ^ (5 : ℕ)) * (E₄ z) := by
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    set a : ℂ := (6 : ℂ) / (π * Complex.I * z)
    have ha : a = -((6 : ℂ) / π) * ((t : ℂ)⁻¹) := by
      simpa [a] using hdiv
    have hmul :
        ((z : ℂ) ^ (2 : ℕ) * (E₂ z + a)) * ((z : ℂ) ^ (4 : ℕ) * E₄ z) =
          (z : ℂ) ^ (6 : ℕ) * ((E₂ z + a) * E₄ z) := by
      ring
    dsimp [A_E]
    have hE2' :
        E₂
            (Matrix.SpecialLinearGroup.toGL
                  ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) • z) =
          (z : ℂ) ^ (2 : ℕ) * (E₂ z + a) := by
      simpa [UpperHalfPlane.SLAction, MulAction.compHom_smul_def, a, mul_assoc, mul_left_comm,
        mul_comm] using hE2
    have hE4_gl :
        E₄
            (Matrix.SpecialLinearGroup.toGL
                  ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) • z) =
          (z : ℂ) ^ (4 : ℕ) * E₄ z := by
      simpa [UpperHalfPlane.SLAction, MulAction.compHom_smul_def] using hE4
    have hE4' :
        (E 4 (by decide))
            (Matrix.SpecialLinearGroup.toGL
                  ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) • z) =
          (z : ℂ) ^ (4 : ℕ) * E₄ z := by
      assumption
    have hE6_gl :
        E₆
            (Matrix.SpecialLinearGroup.toGL
                  ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) • z) =
          (z : ℂ) ^ (6 : ℕ) * E₆ z := by
      simpa [UpperHalfPlane.SLAction, MulAction.compHom_smul_def] using hE6
    have hE6' :
        (E 6 (by decide))
            (Matrix.SpecialLinearGroup.toGL
                  ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) • z) =
          (z : ℂ) ^ (6 : ℕ) * E₆ z := by
      assumption
    rw [hE2', hE4', hE6']
    -- Regroup the main product into `z^6 * (...)`.
    rw [hmul]
    -- Factor out `z^6` and rewrite the remaining term in terms of `A_E`.
    rw [← mul_sub]
    have hins : (E₂ z + a) * E₄ z - E₆ z = A_E z + a * E₄ z := by
      dsimp [A_E]
      ring
    rw [hins, mul_add]
    -- Rewrite `z = i*t` and simplify.
    rw [hz6]
    have hcorr :
        (-((t : ℂ) ^ (6 : ℕ))) * (a * E₄ z) =
          ((6 : ℂ) / π) * ((t : ℂ) ^ (5 : ℕ)) * E₄ z := by
      grind only
    -- Conclude after rewriting the correction term.
    rw [hcorr]
    rw [← (E4_apply (z := z)), ← (E6_apply (z := z))]
    dsimp [A_E]
  -- Convert back to `resToImagAxis`.
  let z0 : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  let zinv : ℍ := ⟨Complex.I * t⁻¹, by simp [htinv]⟩
  have hz0 : z0 = z := by
    ext1; simp [z0, z]
  have hzinv : UpperHalfPlane.mk (Complex.I * t⁻¹) (by simp [htinv]) = zinv := by
    ext1; rfl
  have hS' : ModularGroup.S • z = zinv := hS.trans hzinv
  have hres_inv : A_E.resToImagAxis t⁻¹ = A_E (ModularGroup.S • z) := by
    have hleft : A_E.resToImagAxis t⁻¹ = A_E zinv := by
      simp [Function.resToImagAxis, ResToImagAxis, htinv, zinv]
    exact Mathlib.Meta.NormNumI.eq_of_eq_of_eq_of_eq hleft (congrArg A_E hS) rfl rfl
  have hres_t : A_E.resToImagAxis t = A_E z := by
    have : A_E.resToImagAxis t = A_E z0 := by
      simp [Function.resToImagAxis, ResToImagAxis, ht, z0]
    simpa [hz0] using this
  have hE4_t : (E₄.toFun).resToImagAxis t = E₄ z := by
    have : (E₄.toFun).resToImagAxis t = E₄ z0 := by
      simp [Function.resToImagAxis, ResToImagAxis, ht, z0]
    simpa [hz0] using this
  -- Rewrite in terms of `resToImagAxis`.
  rw [hres_inv, hAE, hres_t, hE4_t]

/-- As a consequence, `F(i/t)` has the quadratic polynomial expansion in `t` from the blueprint. -/
lemma F_resToImagAxis_inv (t : ℝ) (ht : 0 < t) :
    F.resToImagAxis t⁻¹ =
      ((t : ℂ) ^ (12 : ℕ)) * (F.resToImagAxis t) -
        ((12 : ℂ) / π) * ((t : ℂ) ^ (11 : ℕ)) *
          (A_E.resToImagAxis t) * ((E₄.toFun).resToImagAxis t) +
          ((36 : ℂ) / (π ^ (2 : ℕ))) * ((t : ℂ) ^ (10 : ℕ)) * ((E₄.toFun).resToImagAxis t) ^ 2 := by
  -- Use `F = A_E^2` and expand `(A_E(i/t))^2` using `A_E_resToImagAxis_inv`.
  have hF (s : ℝ) (hs : 0 < s) : F.resToImagAxis s = (A_E.resToImagAxis s) ^ 2 := by
    simp [F, A_E, Function.resToImagAxis, ResToImagAxis, hs, pow_two, sub_eq_add_neg]
  -- Expand and simplify.
  rw [hF _ (inv_pos.2 ht), A_E_resToImagAxis_inv t ht]
  -- `ring_nf` handles the binomial expansion; then rewrite `A_E^2` as `F`.
  ring_nf
  -- Rewrite `F.resToImagAxis t` as `A_E.resToImagAxis t ^ 2` and normalize.
  rw [hF _ ht]

/-- Transformation of `H₂` on the imaginary axis: `H₂(i/t) = t^2 * H₄(it)`. -/
private lemma resToImagAxis_inv_of_S_action₂ (F G : ℍ → ℂ)
    (hS : (F ∣[(2 : ℤ)] ModularGroup.S) = -G) (t : ℝ) (ht : 0 < t) :
    F.resToImagAxis (1 / t) = ((t : ℂ) ^ (2 : ℕ)) * G.resToImagAxis t := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hS0 := ResToImagAxis.SlashActionS (F := F) (k := (2 : ℤ)) (t := t) ht
  have hS1 :
      -(G.resToImagAxis t) =
        (Complex.I : ℂ) ^ (-(2 : ℤ)) * (t : ℂ) ^ (-(2 : ℤ)) * F.resToImagAxis (1 / t) := by
    simpa [hS, Function.resToImagAxis, ResToImagAxis, ht] using hS0
  have hS2 : G.resToImagAxis t = (t : ℂ) ^ (-(2 : ℤ)) * F.resToImagAxis (1 / t) := by
    have hIz : (Complex.I : ℂ) ^ (-(2 : ℤ)) = (-1 : ℂ) := by norm_num1
    have : -(G.resToImagAxis t) = -((t : ℂ) ^ (-(2 : ℤ)) * F.resToImagAxis (1 / t)) := by
      simpa [hIz, mul_assoc] using hS1
    exact neg_injective this
  have hcancel : (t : ℂ) ^ (2 : ℤ) * (t : ℂ) ^ (-(2 : ℤ)) = (1 : ℂ) := by
    simpa [mul_comm] using (zpow_neg_mul_zpow_self (a := (t : ℂ)) (n := (2 : ℤ)) ht0)
  have hmul : (t : ℂ) ^ (2 : ℤ) * G.resToImagAxis t = F.resToImagAxis (1 / t) := by
    calc
      (t : ℂ) ^ (2 : ℤ) * G.resToImagAxis t =
          (t : ℂ) ^ (2 : ℤ) * ((t : ℂ) ^ (-(2 : ℤ)) * F.resToImagAxis (1 / t)) := by
            rw [hS2]
      _ = ((t : ℂ) ^ (2 : ℤ) * (t : ℂ) ^ (-(2 : ℤ))) * F.resToImagAxis (1 / t) := by
            simp [mul_assoc]
      _ = F.resToImagAxis (1 / t) := by
            rw [hcancel]
            simp
  simpa [zpow_natCast] using hmul.symm

lemma H₂_resToImagAxis_inv (t : ℝ) (ht : 0 < t) :
    H₂.resToImagAxis t⁻¹ = ((t : ℂ) ^ (2 : ℕ)) * (H₄.resToImagAxis t) := by
  simpa [one_div] using (resToImagAxis_inv_of_S_action₂ H₂ H₄ H₂_S_action t ht)

/-- Transformation of `H₄` on the imaginary axis: `H₄(i/t) = t^2 * H₂(it)`. -/
lemma H₄_resToImagAxis_inv (t : ℝ) (ht : 0 < t) :
    H₄.resToImagAxis t⁻¹ = ((t : ℂ) ^ (2 : ℕ)) * (H₂.resToImagAxis t) := by
  simpa [one_div] using (resToImagAxis_inv_of_S_action₂ H₄ H₂ H₄_S_action t ht)

/-- The corresponding `S`-transform formula for `G` on the imaginary axis. -/
lemma G_resToImagAxis_inv (t : ℝ) (ht : 0 < t) :
    G.resToImagAxis t⁻¹ =
      ((t : ℂ) ^ (10 : ℕ)) *
        (H₄.resToImagAxis t) ^ 3 *
          (2 * (H₄.resToImagAxis t) ^ 2 + 5 * (H₄.resToImagAxis t) * (H₂.resToImagAxis t) +
            5 * (H₂.resToImagAxis t) ^ 2) := by
  have htinv : 0 < t⁻¹ := inv_pos.2 ht
  have hG_eval :
      G.resToImagAxis t⁻¹ =
        (H₂.resToImagAxis t⁻¹) ^ 3 *
          (2 * (H₂.resToImagAxis t⁻¹) ^ 2 + 5 * (H₂.resToImagAxis t⁻¹) * (H₄.resToImagAxis t⁻¹) +
            5 * (H₄.resToImagAxis t⁻¹) ^ 2) := by
    simp [G, Function.resToImagAxis, ResToImagAxis, htinv, pow_succ, mul_assoc]
  rw [hG_eval, H₂_resToImagAxis_inv t ht, H₄_resToImagAxis_inv t ht]
  ring_nf

/-- `E₄(it) → 1` along the imaginary axis as `t → ∞`. -/
lemma tendsto_E₄_resToImagAxis_atTop :
    Tendsto (E₄.toFun.resToImagAxis) atTop (nhds (1 : ℂ)) := by
  simpa using (Function.tendsto_resToImagAxis_atImInfty (E₄ : ℍ → ℂ) (1 : ℂ) tendsto_E₄_atImInfty)

/-- `H₂(it) → 0` along the imaginary axis as `t → ∞`. -/
lemma tendsto_H₂_resToImagAxis_atTop :
    Tendsto (H₂.resToImagAxis) atTop (nhds (0 : ℂ)) := by
  simpa using (Function.tendsto_resToImagAxis_atImInfty H₂ (0 : ℂ) H₂_tendsto_atImInfty)

/-- `H₄(it) → 1` along the imaginary axis as `t → ∞`. -/
lemma tendsto_H₄_resToImagAxis_atTop :
    Tendsto (H₄.resToImagAxis) atTop (nhds (1 : ℂ)) := by
  simpa using (Function.tendsto_resToImagAxis_atImInfty H₄ (1 : ℂ) H₄_tendsto_atImInfty)

/-- Cusp decay for `F = A_E^2` on the imaginary axis: `t^2 * F(it) → 0`. -/
lemma tendsto_mul_t_sq_resToImagAxis_F :
    Tendsto (fun t : ℝ => ((t : ℂ) ^ (2 : ℕ)) * F.resToImagAxis t) atTop (nhds (0 : ℂ)) := by
  have hA : Tendsto (fun t : ℝ => (t : ℂ) * (A_E.resToImagAxis t)) atTop (nhds (0 : ℂ)) :=
    tendsto_mul_t_resToImagAxis_A_E
  have hA2 : Tendsto (fun t : ℝ => ((t : ℂ) * (A_E.resToImagAxis t)) ^ 2) atTop (nhds (0 : ℂ)) := by
    simpa [pow_two, mul_zero] using hA.mul hA
  refine hA2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [F, A_E, Function.resToImagAxis, ResToImagAxis, ht, pow_two, mul_assoc,
    mul_left_comm, mul_comm, sub_eq_add_neg]

/-- The numerator in the blueprint formula for `F(i/t)/G(i/t)` tends to `36/π^2`. -/
lemma tendsto_FmodG_num_atTop :
    Tendsto
      (fun t : ℝ =>
        ((t : ℂ) ^ (2 : ℕ)) * F.resToImagAxis t -
          ((12 : ℂ) / π) * ((t : ℂ) * (A_E.resToImagAxis t) * (E₄.toFun.resToImagAxis t)) +
            ((36 : ℂ) / (π ^ (2 : ℕ))) * (E₄.toFun.resToImagAxis t) ^ 2)
      atTop (nhds ((36 : ℂ) / (π ^ (2 : ℕ)))) := by
  have hF : Tendsto (fun t : ℝ => ((t : ℂ) ^ (2 : ℕ)) * F.resToImagAxis t) atTop (nhds (0 : ℂ)) :=
    tendsto_mul_t_sq_resToImagAxis_F
  have hE4 : Tendsto (E₄.toFun.resToImagAxis) atTop (nhds (1 : ℂ)) :=
    tendsto_E₄_resToImagAxis_atTop
  have hAE : Tendsto (fun t : ℝ => (t : ℂ) * (A_E.resToImagAxis t)) atTop (nhds (0 : ℂ)) :=
    tendsto_mul_t_resToImagAxis_A_E
  have hmiddle :
      Tendsto
        (fun t : ℝ =>
          ((12 : ℂ) / π) * ((t : ℂ) * (A_E.resToImagAxis t) * (E₄.toFun.resToImagAxis t)))
        atTop (nhds (0 : ℂ)) := by
    have hprod :
        Tendsto (fun t : ℝ => ((t : ℂ) * (A_E.resToImagAxis t)) * (E₄.toFun.resToImagAxis t)) atTop
          (nhds (0 : ℂ)) := by
      simpa [zero_mul] using hAE.mul hE4
    simpa [mul_assoc, mul_zero] using (tendsto_const_nhds.mul hprod)
  have hE4sq :
      Tendsto (fun t : ℝ => (E₄.toFun.resToImagAxis t) ^ 2) atTop (nhds (1 : ℂ)) := by
    simpa [pow_two] using hE4.mul hE4
  have hlast :
      Tendsto (fun t : ℝ => ((36 : ℂ) / (π ^ (2 : ℕ))) * (E₄.toFun.resToImagAxis t) ^ 2) atTop
        (nhds (((36 : ℂ) / (π ^ (2 : ℕ))) * (1 : ℂ))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (tendsto_const_nhds.mul hE4sq)
  have hsum :
      Tendsto
        (fun t : ℝ =>
          (((t : ℂ) ^ (2 : ℕ)) * F.resToImagAxis t -
              ((12 : ℂ) / π) *
                ((t : ℂ) * (A_E.resToImagAxis t) * (E₄.toFun.resToImagAxis t))) +
            ((36 : ℂ) / (π ^ (2 : ℕ))) * (E₄.toFun.resToImagAxis t) ^ 2)
        atTop (nhds ((0 : ℂ) + (((36 : ℂ) / (π ^ (2 : ℕ))) * (1 : ℂ)))) := by
    simpa using (hF.sub hmiddle).add hlast
  simpa [sub_eq_add_neg, add_assoc, mul_assoc] using hsum

/-- The denominator in the blueprint formula for `F(i/t)/G(i/t)` tends to `2`. -/
lemma tendsto_FmodG_den_atTop :
    Tendsto
      (fun t : ℝ =>
        (H₄.resToImagAxis t) ^ 3 *
          (2 * (H₄.resToImagAxis t) ^ 2 + 5 * (H₄.resToImagAxis t) * (H₂.resToImagAxis t) +
            5 * (H₂.resToImagAxis t) ^ 2))
      atTop (nhds (2 : ℂ)) := by
  have hH2 : Tendsto (H₂.resToImagAxis) atTop (nhds (0 : ℂ)) := tendsto_H₂_resToImagAxis_atTop
  have hH4 : Tendsto (H₄.resToImagAxis) atTop (nhds (1 : ℂ)) := tendsto_H₄_resToImagAxis_atTop
  have hH4sq : Tendsto (fun t : ℝ => (H₄.resToImagAxis t) ^ 2) atTop (nhds (1 : ℂ)) := by
    simpa [pow_two] using hH4.mul hH4
  have hH2sq : Tendsto (fun t : ℝ => (H₂.resToImagAxis t) ^ 2) atTop (nhds (0 : ℂ)) := by
    simpa [pow_two, zero_mul] using hH2.mul hH2
  have hH4H2 :
      Tendsto (fun t : ℝ => (H₄.resToImagAxis t) * (H₂.resToImagAxis t)) atTop (nhds (0 : ℂ)) :=
    by simpa [mul_zero] using hH4.mul hH2
  have hpoly :
      Tendsto
        (fun t : ℝ =>
          2 * (H₄.resToImagAxis t) ^ 2 + 5 * (H₄.resToImagAxis t) * (H₂.resToImagAxis t) +
            5 * (H₂.resToImagAxis t) ^ 2)
        atTop (nhds (2 : ℂ)) := by
    have h1 : Tendsto (fun t : ℝ => (2 : ℂ) * (H₄.resToImagAxis t) ^ 2) atTop (nhds (2 : ℂ)) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul hH4sq)
    have h2 :
        Tendsto (fun t : ℝ => (5 : ℂ) * ((H₄.resToImagAxis t) * (H₂.resToImagAxis t))) atTop
          (nhds (0 : ℂ)) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul hH4H2)
    have h3 : Tendsto (fun t : ℝ => (5 : ℂ) * (H₂.resToImagAxis t) ^ 2) atTop (nhds (0 : ℂ)) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul hH2sq)
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc] using h1.add (h2.add h3)
  have hH4cube : Tendsto (fun t : ℝ => (H₄.resToImagAxis t) ^ 3) atTop (nhds (1 : ℂ)) := by
    simpa [pow_succ, pow_two, Nat.succ_eq_add_one, mul_assoc] using hH4sq.mul hH4
  -- Multiply the limiting factors: `1 * 2 = 2`.
  simpa [mul_assoc] using hH4cube.mul hpoly

/-- The blueprint quotient formula on the imaginary axis after applying `S` and canceling `t^10`. -/
lemma FmodG_resToImagAxis_inv_formula (t : ℝ) (ht : 0 < t) :
    F.resToImagAxis t⁻¹ / G.resToImagAxis t⁻¹ =
      (((t : ℂ) ^ (2 : ℕ)) * F.resToImagAxis t -
          ((12 : ℂ) / π) * ((t : ℂ) * (A_E.resToImagAxis t) * (E₄.toFun.resToImagAxis t)) +
            ((36 : ℂ) / (π ^ (2 : ℕ))) * (E₄.toFun.resToImagAxis t) ^ 2) /
        ((H₄.resToImagAxis t) ^ 3 *
          (2 * (H₄.resToImagAxis t) ^ 2 + 5 * (H₄.resToImagAxis t) * (H₂.resToImagAxis t) +
            5 * (H₂.resToImagAxis t) ^ 2)) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  -- Substitute the `S`-transform formulas and cancel the common `t^10`.
  rw [F_resToImagAxis_inv t ht, G_resToImagAxis_inv t ht]
  -- `field_simp` with `t ≠ 0` clears the division by `(t : ℂ)^10`.
  field_simp [ht0]

/-- `F(i/t)/G(i/t) → 18/π^2` as `t → ∞`. -/
lemma tendsto_FmodG_resToImagAxis_inv_atTop :
    Tendsto (fun t : ℝ => F.resToImagAxis t⁻¹ / G.resToImagAxis t⁻¹) atTop
      (nhds ((18 : ℂ) / (π ^ (2 : ℕ)))) := by
  have hEq :
      (fun t : ℝ => F.resToImagAxis t⁻¹ / G.resToImagAxis t⁻¹) =ᶠ[atTop]
        fun t : ℝ =>
          (((t : ℂ) ^ (2 : ℕ)) * F.resToImagAxis t -
              ((12 : ℂ) / π) * ((t : ℂ) * (A_E.resToImagAxis t) * (E₄.toFun.resToImagAxis t)) +
                ((36 : ℂ) / (π ^ (2 : ℕ))) * (E₄.toFun.resToImagAxis t) ^ 2) /
            ((H₄.resToImagAxis t) ^ 3 *
              (2 * (H₄.resToImagAxis t) ^ 2 + 5 * (H₄.resToImagAxis t) * (H₂.resToImagAxis t) +
                5 * (H₂.resToImagAxis t) ^ 2)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    simpa using (FmodG_resToImagAxis_inv_formula t ht)
  have hnum := tendsto_FmodG_num_atTop
  have hden := tendsto_FmodG_den_atTop
  have hquot : Tendsto (fun t : ℝ => F.resToImagAxis t⁻¹ / G.resToImagAxis t⁻¹) atTop
      (nhds (((36 : ℂ) / (π ^ (2 : ℕ))) / (2 : ℂ))) :=
    (hnum.div hden (by norm_num)).congr' hEq.symm
  have hconst : ((36 : ℂ) / (π ^ (2 : ℕ))) / (2 : ℂ) = (18 : ℂ) / (π ^ (2 : ℕ)) := by ring_nf
  simpa [hconst] using hquot

/--
$\lim_{t \to 0^+} F(it) / G(it) = 18 / \pi^2$.
-/
public theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (18 * (π ^ (-2 : ℤ))) Set.univ) := by
  -- Work in `ℂ` and take real parts at the end.
  have hQc :
      Tendsto (fun t : ℝ => F.resToImagAxis t / G.resToImagAxis t) (𝓝[>] (0 : ℝ))
        (nhds ((18 : ℂ) / (π ^ (2 : ℕ)))) := by
    have h := tendsto_FmodG_resToImagAxis_inv_atTop.comp tendsto_inv_nhdsGT_zero
    refine h.congr' (Eventually.of_forall ?_)
    intro t
    simp [Function.comp, inv_inv]
  have hRe :
      Tendsto (fun t : ℝ => (F.resToImagAxis t / G.resToImagAxis t).re) (𝓝[>] (0 : ℝ))
        (nhds (18 / (π ^ (2 : ℕ)) : ℝ)) := by
    have hRe' :
        Tendsto (fun t : ℝ => (F.resToImagAxis t / G.resToImagAxis t).re) (𝓝[>] (0 : ℝ))
          (nhds (((18 : ℂ) / (π ^ (2 : ℕ))).re)) :=
      (Complex.continuous_re.tendsto ((18 : ℂ) / (π ^ (2 : ℕ)))).comp hQc
    have hre : (((18 : ℂ) / (π ^ (2 : ℕ))).re) = (18 / (π ^ (2 : ℕ)) : ℝ) := by
      have h :
          (18 / (π ^ (2 : ℕ)) : ℝ) =
            ((18 : ℂ) / ((π ^ (2 : ℕ) : ℝ) : ℂ)).re := by
        have h0 := congrArg Complex.re (Complex.ofReal_div 18 (π ^ (2 : ℕ) : ℝ))
        simpa only [Complex.ofReal_re] using h0
      simp_all
    simpa [hre] using hRe'
  have hEq :
      FmodGReal =ᶠ[𝓝[>] (0 : ℝ)] fun t : ℝ => (F.resToImagAxis t / G.resToImagAxis t).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hF : (FmodGReal t : ℂ) = F.resToImagAxis t / G.resToImagAxis t := by
      simpa using (FmodG_eq_FmodGReal (t := t) ht)
    -- Take real parts.
    simpa [Complex.ofReal_re] using congrArg Complex.re hF
  have hR :
      Tendsto FmodGReal (𝓝[>] (0 : ℝ)) (nhds (18 / (π ^ (2 : ℕ)) : ℝ)) :=
    (hRe.congr' hEq.symm)
  -- Rewrite the target constant as `18 * π^(-2)`.
  simpa

/--
Main inequalities between $F$ and $G$ on the imaginary axis.
-/
public theorem FG_inequality_1 {t : ℝ} (ht : 0 < t) :
    FReal t + 18 * (π ^ (-2 : ℤ)) * GReal t > 0 := by
  have hcoef : 0 < (18 : ℝ) * (π ^ (-2 : ℤ)) := mul_pos (by norm_num) (zpow_pos Real.pi_pos _)
  have hF : 0 < FReal t := by simpa [FReal] using (F_pos.2 t ht)
  have hG : 0 < GReal t := by simpa [GReal] using (G_pos.2 t ht)
  exact add_pos hF (mul_pos hcoef hG)

lemma FmodG_strictAnti : StrictAntiOn FmodGReal (Set.Ioi (0 : ℝ)) := by
  exact FmodG_strictAnti_aux

lemma FmodGReal_le_rightLimitAt_zero {t : ℝ} (ht : 0 < t) :
    FmodGReal t ≤ 18 * (π ^ (-2 : ℤ)) := by
  set c : ℝ := 18 * (π ^ (-2 : ℤ))
  have hlim : Tendsto FmodGReal (𝓝[>] (0 : ℝ)) (nhds c) := by
    simpa [c, nhdsWithin_univ] using FmodG_rightLimitAt_zero
  have hant : AntitoneOn FmodGReal (Set.Ioi (0 : ℝ)) := FmodG_antitone
  have htI : t ∈ Set.Ioi (0 : ℝ) := ht
  have hEv : ∀ᶠ u in 𝓝[>] (0 : ℝ), FmodGReal t ≤ FmodGReal u := by
    have hul : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ≤ t := by
      have : Set.Ioi (0 : ℝ) ∩ Set.Iio t ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        inter_mem_nhdsWithin _ (Iio_mem_nhds ht)
      exact mem_of_superset this (by intro u hu; exact le_of_lt (by simpa [Set.mem_Iio] using hu.2))
    filter_upwards [self_mem_nhdsWithin, hul] with u hu0 hut
    exact hant hu0 htI hut
  exact ge_of_tendsto hlim hEv

lemma FmodGReal_lt_rightLimitAt_zero {t : ℝ} (ht : 0 < t) :
    FmodGReal t < 18 * (π ^ (-2 : ℤ)) := by
  have hstrict : StrictAntiOn FmodGReal (Set.Ioi (0 : ℝ)) := FmodG_strictAnti
  have hlt : FmodGReal t < FmodGReal (t / 2) :=
    hstrict (by simpa using half_pos ht) ht (half_lt_self ht)
  exact lt_of_lt_of_le hlt (FmodGReal_le_rightLimitAt_zero (t := t / 2) (half_pos ht))

/-- An explicit inequality relating `FReal` and `GReal` on the imaginary axis. -/
public theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  have hGpos : 0 < GReal t := by simpa [GReal] using (G_pos.2 t ht)
  have hquot : FReal t / GReal t < 18 * (π ^ (-2 : ℤ)) := by
    simpa [FmodGReal] using FmodGReal_lt_rightLimitAt_zero ht
  have hmul := mul_lt_mul_of_pos_right hquot hGpos
  have hGne : GReal t ≠ 0 := ne_of_gt hGpos
  have hmul' : FReal t < (18 * (π ^ (-2 : ℤ))) * GReal t := by
    simpa [div_eq_mul_inv, hGne, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact sub_lt_zero.2 hmul'
